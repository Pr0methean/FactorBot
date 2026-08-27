use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::{NumericFactor, find_factors_of_numeric, get_numeric_value_cache};
use crate::graph::EntryId;
use crate::net::NumberStatus::{FullyFactored, Invalid, PartlyFactoredComposite, Prime, UnfactoredComposite, Unknown};
use crate::{BasicCache, get_from_cache};
use crate::{
    EXIT_TIME, FAILED_U_SUBMISSIONS_OUT, FactorSubmission, MAX_CPU_BUDGET_TENTHS,
    MAX_ID_EQUAL_TO_VALUE, ReportFactorResult, SUBMIT_FACTOR_MAX_ATTEMPTS, create_cache,
};
use crate::{Factor, NumberSpecifier, NumberStatusApiResponse, RETRY_DELAY};
use async_backtrace::framed;
use atomic_time::AtomicInstant;
use core::cell::RefCell;
use core::fmt::{Display, Formatter};
use curl::easy::{Easy2, Handler, WriteError};
use futures_util::TryFutureExt;
use governor::middleware::StateInformationMiddleware;
use governor::{DefaultDirectRateLimiter, Quota, RateLimiter};
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use regex::{Regex, RegexBuilder};
use reqwest::Client;
use reqwest::Response;
use serde_json::from_str;
use std::cmp;
use std::io::Write;
use std::mem::swap;
use std::num::NonZeroU32;
use std::process::exit;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Duration;
use tokio::sync::Mutex;
use tokio::task::block_in_place;
use tokio::time::{Instant, sleep, sleep_until};
use urlencoding::encode;

pub const MAX_RETRIES: usize = 40;

const CONNECT_TIMEOUT: Duration = Duration::from_mins(1);
const E2E_TIMEOUT: Duration = Duration::from_mins(2);
const PARALLEL_REQUEST_THROTTLING_DURATION: Duration = Duration::from_secs(5);

const REQWEST_MAX_URL_LEN: usize = (u16::MAX - 1) as usize;

thread_local! {
    static CURL_CLIENT: RefCell<Easy2<CurlResponseCollector >> = RefCell::new(Easy2::new(CurlResponseCollector(Vec::new())));
}

struct CurlResponseCollector(Vec<u8>);

impl Handler for CurlResponseCollector {
    fn write(&mut self, data: &[u8]) -> Result<usize, WriteError> {
        self.0.extend_from_slice(data);
        Ok(data.len())
    }
}

impl CurlResponseCollector {
    fn take_all(&mut self) -> Vec<u8> {
        let mut out = Vec::new();
        swap(&mut self.0, &mut out);
        out
    }
}

#[cfg_attr(test, mockall::automock)]
pub trait FactorDbClient {
    async fn wait_if_resource_limited(
        &self,
        resources_text: &str,
    ) -> bool;
    /// Executes a GET request with a large reasonable default number of retries, or else
    /// restarts the process if that request consistently fails.
    async fn retrying_get_and_decode(
        &self,
        url: &str,
        retry_delay: Duration,
    ) -> Option<HipStr<'static>>;
    async fn try_get_and_decode(&self, url: &str) -> Option<HipStr<'static>>;
    async fn try_get_expression_form(&self, entry_id: EntryId) -> Option<Factor>;
    async fn known_factors_as_digits<'a>(
        &self,
        id: NumberSpecifier<'a>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse;
    fn cached_factors<'a>(&self, id: &'a NumberSpecifier<'a>)
    -> Option<ProcessedStatusApiResponse>;
    fn invalidate_cached_factors(&self, id: Option<EntryId>, expression: &Factor);
    async fn try_report_factor<'a>(
        &self,
        u_id: NumberSpecifier<'a>,
        factor: &Factor,
    ) -> ReportFactorResult;
    async fn report_numeric_factor(
        &self,
        u_id: EntryId,
        factor: NumericFactor,
    ) -> ReportFactorResult;
}

/// Separates a method that mockall can't currently mock.
pub trait FactorDbClientReadIdsAndExprs: FactorDbClient {
    fn read_ids_and_exprs<'a>(&self, haystack: &'a str)
    -> impl Iterator<Item = (EntryId, &'a str)>;
}

pub struct RealFactorDbClient {
    resources_regex: Regex,
    http: Client,
    rate_limiter: DefaultDirectRateLimiter<StateInformationMiddleware>,
    requests_left_last_check: AtomicU32,
    requests_per_hour: u32,
    request_mutex: Mutex<()>,
    all_threads_blocked_until: AtomicInstant,
    id_and_expr_regex: Regex,
    digits_fallback_regex: Regex,
    expression_form_regex: Regex,
    by_id_cache: BasicCache<EntryId, ProcessedStatusApiResponse>,
    by_expr_cache: BasicCache<Factor, ProcessedStatusApiResponse>,
    expression_form_cache: BasicCache<EntryId, Factor>,
}

impl RealFactorDbClient {
    pub fn new(requests_per_hour: NonZeroU32) -> Self {
        let rate_limiter =
            RateLimiter::direct(Quota::per_hour(requests_per_hour)).with_middleware();
        let resources_regex =
            RegexBuilder::new("Page requests(?:[^0-9])+([0-9,]+).*CPU.*>([0-9]+)\\.([0-9]) seconds.*600\\.0 seconds.*([0-6][0-9]):([0-6][0-9])")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let id_and_expr_regex =
            Regex::new("index\\.php\\?id=([0-9]+)\"><font[^>]*>([^<]+)</font>").unwrap();
        let http = Client::builder()
            .pool_max_idle_per_host(4)
            .timeout(E2E_TIMEOUT)
            .connect_timeout(CONNECT_TIMEOUT)
            .build()
            .unwrap();
        let digits_fallback_regex =
            RegexBuilder::new("<tr><td>Number</td>[^<]*<td[^>]*>([0-9br<>\\pZ]+)")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let expression_form_regex = Regex::new("name=\"query\" value=\"([^\"]+)\"").unwrap();
        // Governor rate-limiters start out with their full burst capacity and recharge starting
        // immediately, but this would lead to twice the allowed number of requests in our first hour,
        // so we make it start nearly empty instead.
        rate_limiter
            .check_n(6050u32.try_into().unwrap())
            .unwrap()
            .unwrap();
        let requests_left_last_check = AtomicU32::new(requests_per_hour.get());
        Self {
            resources_regex,
            http,
            rate_limiter,
            requests_per_hour: requests_per_hour.get(),
            requests_left_last_check,
            request_mutex: Mutex::const_new(()),
            all_threads_blocked_until: AtomicInstant::now(),
            id_and_expr_regex,
            digits_fallback_regex,
            expression_form_regex,
            by_id_cache: create_cache(1 << 16),
            by_expr_cache: create_cache(1 << 12),
            expression_form_cache: create_cache(1 << 16),
        }
    }

    #[framed]
    async fn try_get_and_decode_core(&self, url: &str) -> Option<HipStr<'static>> {
        self.rate_limiter.until_ready().await;
        let permit = self.request_mutex.lock().await;
        info!("Start of request to {url}");
        let result = if url.len() > REQWEST_MAX_URL_LEN {
            let result = block_in_place(|| {
                CURL_CLIENT.with_borrow_mut(|curl| {
                    curl.get(true)
                        .and_then(|_| curl.connect_timeout(CONNECT_TIMEOUT))
                        .and_then(|_| curl.timeout(E2E_TIMEOUT))
                        .and_then(|_| curl.url(url))
                        .and_then(|_| curl.perform())
                        .map_err(anyhow::Error::from)
                        .and_then(|_| {
                            let response_code = curl.response_code()?;
                            if response_code != 200 {
                                error!("Error reading {url}: HTTP response code {response_code}");
                            }
                            let response_body = curl.get_mut().take_all();
                            curl.reset();
                            Ok(response_body)
                        })
                })
            });
            drop(permit);
            result.and_then(|response_body| Ok(String::from_utf8(response_body)?))
        } else {
            let result = self
                .http
                .get(url)
                .header("Referer", "https://factordb.com")
                .send()
                .and_then(Response::text)
                .await;
            drop(permit);
            result.map_err(|e| anyhow::Error::from(e.without_url()))
        };
        info!("End of request to {url}");
        match result {
            Err(e) => {
                error!("Error reading {url}: {e}");
                None
            }
            Ok(text) => {
                if text.contains("502 Proxy Error") {
                    error!("502 error from {url}");
                    None
                } else if text.contains("parallel processing requests") {
                    warn!("Parallel-request limit reached; throttling");
                    let end_of_throttling = Instant::now() + PARALLEL_REQUEST_THROTTLING_DURATION;
                    self.all_threads_blocked_until
                        .store(end_of_throttling.into(), Release);
                    None
                } else {
                    Some(text.into())
                }
            }
        }
    }
}

impl FactorDbClient for RealFactorDbClient {
    #[framed]
    async fn wait_if_resource_limited(
        &self,
        resources_text: &str,
    ) -> bool {
        let now = Instant::now();
        let Some(captures) = self.resources_regex.captures_iter(resources_text).next() else {
            return false;
        };
        let (
            _,
            [
                requests,
                cpu_seconds,
                cpu_tenths_within_second,
                minutes_to_reset,
                seconds_within_minute_to_reset,
            ],
        ) = captures.extract();
        let requests = requests.replace(",", "").parse::<u32>().unwrap();
        let requests_left = self.requests_per_hour - requests;
        let prev_requests_left = self
            .requests_left_last_check
            .swap(requests, Ordering::AcqRel);
        if prev_requests_left > requests_left
            && let Ok(state) = self.rate_limiter.check()
        {
            let limiter_burst_capacity = state.remaining_burst_capacity();
            if let Some(excess) = limiter_burst_capacity.checked_sub(requests_left)
                && let Some(excess) = NonZeroU32::new(excess)
            {
                warn!("{excess} more requests consumed than expected");
                self.rate_limiter.until_n_ready(excess).await.unwrap();
            }
        }
        // info!("Resources parsed: {}, {}, {}, {}",
        //     cpu_seconds, cpu_tenths_within_second, minutes_to_reset, seconds_within_minute_to_reset);
        let cpu_tenths_spent = cpu_seconds.parse::<usize>().unwrap() * 10
            + cpu_tenths_within_second.parse::<usize>().unwrap();
        CPU_TENTHS_SPENT_LAST_CHECK.store(cpu_tenths_spent, Release);
        let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60
            + seconds_within_minute_to_reset.parse::<u64>().unwrap();
        let resets_at = now + Duration::from_secs(seconds_to_reset);
        if EXIT_TIME
            .get()
            .is_some_and(|exit_time| exit_time <= &resets_at)
        {
            error!("Resource limits reached and won't reset during this process's lifespan");
            exit(0);
        }
        self.all_threads_blocked_until
            .store(resets_at.into(), Release);
        true
    }

    /// Executes a GET request with a large reasonable default number of retries, or else
    /// restarts the process if that request consistently fails.
    #[framed]
    async fn retrying_get_and_decode(
        &self,
        url: &str,
        retry_delay: Duration,
    ) -> Option<HipStr<'static>> {
        for _ in 0..MAX_RETRIES {
            if let Some(value) = self.try_get_and_decode(url).await {
                return Some(value);
            }
            sleep(retry_delay).await;
        }
        None
    }

    #[framed]
    async fn try_get_and_decode(&self, url: &str) -> Option<HipStr<'static>> {
        sleep_until(self.all_threads_blocked_until.load(Acquire).into()).await;
        loop {
            let response = self.try_get_and_decode_core(url).await?;
            if !self.wait_if_resource_limited(&response).await
            {
                return Some(response);
            }
        }
    }

    #[inline]
    #[framed]
    async fn try_get_expression_form(&self, entry_id: EntryId) -> Option<Factor> {
        if entry_id <= MAX_ID_EQUAL_TO_VALUE {
            return Some(Factor::from(entry_id));
        }
        if let Some(response) = self.expression_form_cache.get(&entry_id) {
            info!("Expression-form cache hit for {entry_id}");
            return Some(response.clone());
        }
        let response = self
            .try_get_and_decode(&format!("https://factordb.com/index.php?id={entry_id}"))
            .await?;
        let expression_form = Factor::from(
            self.expression_form_regex
                .captures(&response)?
                .get(1)?
                .as_str(),
        );
        self.expression_form_cache
            .insert(entry_id, expression_form.clone());
        Some(expression_form)
    }

    #[inline]
    #[framed]
    async fn known_factors_as_digits<'a>(
        &self,
        id: NumberSpecifier<'a>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse {
        debug!("known_factors_as_digits: id={id:?}");
        if let Some(cached) = self.cached_factors(&id) {
            return cached;
        }
        let response = match id {
            Id(id) => {
                let url = format!("https://factordb.com/api?id={id}");
                if let Some(response) = self.try_get_and_decode(&url).await {
                    if response.is_empty() {
                        let fallback_from_empty = self
                            .try_get_and_decode(&format!("https://factordb.com/index.php?showid={id}"))
                            .await;
                        if let Some(valid_fallback_from_empty) = &fallback_from_empty
                                && valid_fallback_from_empty.contains("Not divisible") {
                            return ProcessedStatusApiResponse {
                                status: Some(Invalid),
                                factors: Box::new([]),
                                id: None,
                            };
                        } else {
                            Err(fallback_from_empty)
                        }
                    } else {
                        Ok(response)
                    }
                } else if get_digits_as_fallback {
                    sleep(RETRY_DELAY).await;
                    Err(self
                        .try_get_and_decode(&format!("https://factordb.com/index.php?showid={id}"))
                        .await)
                } else {
                    Err(None)
                }
            }
            Expression(ref expr) => {
                let url = format!(
                    "https://factordb.com/api?query={}",
                    encode(&expr.to_unelided_string())
                );
                self.try_get_and_decode(&url)
                    .await
                    .map(Ok)
                    .unwrap_or(Err(None))
            }
        };
        debug!("{id}: Got API response:\n{response:?}");
        let mut processed = match response {
            Ok(api_response) => match from_str::<NumberStatusApiResponse>(&api_response) {
                Err(e) => {
                    error!("{id}: Failed to decode API response: {e}: {api_response}");
                    ProcessedStatusApiResponse::default()
                }
                Ok(NumberStatusApiResponse {
                    status,
                    factors,
                    id: recvd_id,
                }) => {
                    let recvd_id_parsed = recvd_id.to_string().parse::<EntryId>().ok();
                    debug!("Parsed received ID {recvd_id} as {recvd_id_parsed:?}");
                    info!(
                        "{recvd_id_parsed:?} ({id}): Fetched status of {status} and {} factors of sizes {}",
                        factors.len(),
                        factors.iter().map(|(digits, _)| digits.len()).join(",")
                    );
                    let status = match &*status {
                        "FF" => Some(FullyFactored),
                        "P" | "PRP" => Some(Prime),
                        "C" => Some(UnfactoredComposite),
                        "CF" => Some(PartlyFactoredComposite),
                        "U" => Some(Unknown),
                        x => {
                            error!("{recvd_id:?} ({id}): Unrecognized number status code: {x}");
                            None
                        }
                    };
                    let factors = {
                        let mut factors: Vec<_> = factors
                            .into_iter()
                            .map(|(factor, _exponent)| Factor::from(factor.as_str()))
                            .collect();
                        factors.sort_unstable();
                        factors.dedup();
                        factors
                    };
                    ProcessedStatusApiResponse {
                        status,
                        factors: factors.into_boxed_slice(),
                        id: recvd_id_parsed,
                    }
                }
            },
            Err(None) => ProcessedStatusApiResponse {
                status: None,
                id: None,
                factors: Box::new([]),
            },
            Err(Some(fallback_response)) => {
                if fallback_response.contains("Error: ") {
                    return ProcessedStatusApiResponse {
                        status: Some(Invalid),
                        factors: Box::new([]),
                        id: None,
                    };
                }
                let factors = self
                    .digits_fallback_regex
                    .captures(&fallback_response)
                    .and_then(|c| c.get(1))
                    .map(|digits_cell| {
                        vec![Factor::from(
                            digits_cell
                                .as_str()
                                .chars()
                                .filter(char::is_ascii_digit)
                                .collect::<String>()
                                .as_str(),
                        )]
                    })
                    .unwrap_or_default();
                ProcessedStatusApiResponse {
                    status: None,
                    factors: factors.into_boxed_slice(),
                    id: None,
                }
            }
        };
        if processed.status == Some(Prime)
            || (processed.status == Some(FullyFactored) && processed.factors.len() > 1)
        {
            if let Some(id) = processed
                .id
                .or(if let Id(id) = id { Some(id) } else { None })
            {
                self.by_id_cache.insert(id, processed.clone());
            }
            if let Expression(expr) = &id {
                self.by_expr_cache
                    .insert(expr.clone().into_owned(), processed.clone());
            }
        }
        if !include_ff && processed.status.is_known_finished() {
            processed.factors = Box::default();
        }
        processed
    }

    #[inline]
    fn cached_factors(&self, id: &NumberSpecifier) -> Option<ProcessedStatusApiResponse> {
        let numeric_or_id = match id {
            Id(entry_id) => Some(*entry_id),
            Expression(x) => {
                if let Numeric(n) = **x {
                    Some(n)
                } else if let Some(Some(n)) = get_from_cache(get_numeric_value_cache(), x.as_ref())
                {
                    Some(n)
                } else {
                    None
                }
            }
        };
        if let Some(entry_id) = numeric_or_id
            && entry_id <= MAX_ID_EQUAL_TO_VALUE
        {
            debug!("Specially handling numeric expression {entry_id}");
            let factors: Box<[_]> = find_factors_of_numeric(entry_id).into_keys().collect();
            return Some(ProcessedStatusApiResponse {
                status: Some(if factors.len() > 1 {
                    FullyFactored
                } else {
                    Prime
                }),
                factors,
                id: Some(entry_id),
            });
        }
        let cached = match id {
            Id(id) => self.by_id_cache.get(id).or_else(|| {
                self.expression_form_cache
                    .get(id)
                    .as_ref()
                    .and_then(|expr| get_from_cache(&self.by_expr_cache, expr))
            }),
            Expression(expr) => get_from_cache(&self.by_expr_cache, expr.as_ref()),
        };
        if cached.is_some() {
            info!("Factor cache hit for {id}");
        }
        cached
    }

    fn invalidate_cached_factors(&self, id: Option<EntryId>, expression: &Factor) {
        if let Some(id) = id {
            self.by_id_cache.remove(&id);
        }
        self.by_expr_cache.remove(expression);
    }

    #[framed]
    async fn try_report_factor(
        &self,
        u_id: NumberSpecifier<'_>,
        factor: &Factor,
    ) -> ReportFactorResult {
        if u_id == Expression(std::borrow::Cow::Borrowed(factor)) {
            error!("Attempted to submit factor {factor} to itself");
            return DoesNotDivide;
        }
        let (id, number) = match u_id {
            Expression(ref x) => {
                if let Some(x_numeric) = x.as_numeric() {
                    error!("Attempted to submit factor {factor} of too-small number {x_numeric}");
                    return AlreadyFullyFactored;
                }
                (None, Some(x.to_unelided_string()))
            },
            Id(id) => {
                if id <= MAX_ID_EQUAL_TO_VALUE {
                    error!("Attempted to submit factor {factor} of too-small number {id}");
                    return AlreadyFullyFactored;
                }
                (Some(id), None)
            }
        };
        self.rate_limiter.until_ready().await;
        let permit = self.request_mutex.lock().await;
        info!("Start of request to https://factordb.com/reportfactor.php");
        let response = self
            .http
            .post("https://factordb.com/reportfactor.php")
            .form(&FactorSubmission {
                id,
                number,
                factor: &factor.to_unelided_string(),
            })
            .send()
            .and_then(Response::text)
            .await;
        drop(permit);
        info!("End of request to https://factordb.com/reportfactor.php");
        match response {
            Ok(text) => {
                info!("{u_id}: reported a factor of {factor}; response: {text}",);
                if text.contains("Error") {
                    OtherError
                } else if text.contains("submitted") {
                    Accepted
                } else if text.contains("fully factored") || text.contains("Number too small") {
                    AlreadyFullyFactored
                } else if text.contains("Does not divide") {
                    DoesNotDivide
                } else {
                    self.wait_if_resource_limited(&text).await;
                    OtherError
                }
            }
            Err(e) => {
                error!("{u_id}: Failed to get response when submitting {factor}: {e}");
                sleep(RETRY_DELAY).await;
                OtherError
            }
        }
    }

    #[framed]
    async fn report_numeric_factor(
        &self,
        u_id: EntryId,
        factor: NumericFactor,
    ) -> ReportFactorResult {
        for _ in 0..SUBMIT_FACTOR_MAX_ATTEMPTS {
            let result = self.try_report_factor(Id(u_id), &Numeric(factor)).await;
            if result != OtherError {
                return result;
            }
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{u_id},{}\n", factor))
        {
            Ok(_) => warn!("{u_id}: wrote {factor} to failed submissions file"),
            Err(e) => error!("{u_id}: failed to write {factor} to failed submissions file: {e}"),
        }
        OtherError // factor that we failed to submit may still have been valid
    }
}

impl FactorDbClientReadIdsAndExprs for RealFactorDbClient {
    fn read_ids_and_exprs<'a>(
        &self,
        haystack: &'a str,
    ) -> impl Iterator<Item = (EntryId, &'a str)> {
        self.id_and_expr_regex
            .captures_iter(haystack)
            .filter_map(move |capture| {
                let Some(id) = capture.get(1) else {
                    error!("Failed to get ID for expression in\n{haystack}");
                    return None;
                };
                let id = match id.as_str().parse::<EntryId>() {
                    Ok(id) => id,
                    Err(e) => {
                        error!("Failed to parse ID {}: {e}", id.as_str());
                        return None;
                    }
                };
                let Some(expr) = capture.get(2) else {
                    error!("Failed to get expression for ID {id} in\n{haystack}");
                    return None;
                };
                Some((id, expr.as_str()))
            })
            .unique()
    }
}

pub static CPU_TENTHS_SPENT_LAST_CHECK: AtomicUsize = AtomicUsize::new(MAX_CPU_BUDGET_TENTHS);

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct BigNumber(pub HipStr<'static>);

impl PartialOrd for BigNumber {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigNumber {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.cmp(&other.0))
    }
}

impl AsRef<str> for BigNumber {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl Display for BigNumber {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Into<HipStr<'static>>> From<T> for BigNumber {
    fn from(value: T) -> Self {
        BigNumber(value.into())
    }
}

#[derive(Clone, Default, Debug)]
pub struct ProcessedStatusApiResponse {
    pub status: Option<NumberStatus>,
    pub factors: Box<[Factor]>,
    pub id: Option<EntryId>,
}

pub trait NumberStatusExt {
    fn is_known_finished(&self) -> bool;
}

impl NumberStatusExt for Option<NumberStatus> {
    #[inline]
    fn is_known_finished(&self) -> bool {
        matches!(self, Some(FullyFactored) | Some(Prime) | Some(Invalid))
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub enum NumberStatus {
    Unknown,
    UnfactoredComposite,
    PartlyFactoredComposite,
    Prime, // includes PRP
    FullyFactored,
    /// This expression represents a number outside FactorDB's domain (integers from 0 to
    /// 10^10^7) or produces one as an intermediate value.
    Invalid,
}
