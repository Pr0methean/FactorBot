#![allow(stable_features)]
#![allow(incomplete_features)]
#![feature(float_gamma)]
#![feature(exact_div)]
#![feature(explicit_tail_calls)]
#![feature(never_type)]
use tokio_stream::StreamExt;
extern crate alloc;
extern crate core;

mod algebraic;
mod channel;
mod graph;
mod monitor;
mod net;
mod yafu;

use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored};
use crate::algebraic::Factor;
use crate::graph::EntryId;
use crate::monitor::Monitor;
use crate::net::{FactorDbClient, FactorDbClientReadIdsAndExprs};
use crate::yafu::{YafuWorkItem, YAFU_KILL_GRACE_PERIOD, YAFU_SENDER, yafu_task};
use ahash::RandomState;
use alloc::sync::Arc;
use async_backtrace::framed;
use async_backtrace::taskdump_tree;
use channel::PushbackReceiver;
use cuckoofilter::CuckooFilter;
use futures_util::FutureExt;
use hipstr::HipStr;
use log::{error, info, warn};
use net::NumberStatus::FullyFactored;
use net::{RealFactorDbClient};
use net::{NumberStatusExt, ProcessedStatusApiResponse};
use quick_cache::UnitWeighter;
use quick_cache::sync::{Cache, DefaultLifecycle};
use rand::seq::SliceRandom;
use rand::{RngExt, rng};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use stats_alloc::StatsAlloc;
use std::alloc::GlobalAlloc;
use std::borrow::Cow;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::num::NonZeroU32;
use std::ops::Add;
use std::panic;
use std::process::{abort};
use std::sync::OnceLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::{Release};
use sysinfo::MemoryRefreshKind;
use sysinfo::RefreshKind;
use tokio::signal::ctrl_c;
use tokio::sync::mpsc::error::SendError;
use tokio::sync::mpsc::{OwnedPermit, channel};
use tokio::sync::{Mutex, OnceCell};
use tokio::task::JoinHandle;
use tokio::time::{Duration, Instant, sleep, sleep_until, timeout};
use tokio::{select, task};

#[cfg(not(windows))]
#[global_allocator]
static GLOBAL: StatsAlloc<tikv_jemallocator::Jemalloc> =
    StatsAlloc::new(tikv_jemallocator::Jemalloc);

#[cfg(windows)]
#[global_allocator]
static GLOBAL: StatsAlloc<std::alloc::System> = StatsAlloc::system();

pub type BasicCache<K, V> = Cache<K, V, UnitWeighter, RandomState, DefaultLifecycle<K, V>>;

static RANDOM_STATE: OnceLock<RandomState> = OnceLock::new();
fn get_random_state() -> &'static RandomState {
    RANDOM_STATE.get_or_init(RandomState::new)
}

pub fn hash(input: impl Hash) -> u64 {
    get_random_state().hash_one(input)
}

pub fn create_cache<T: Eq + Hash, U: Clone>(capacity: usize) -> BasicCache<T, U> {
    Cache::with(
        capacity,
        Default::default(),
        Default::default(),
        get_random_state().clone(),
        Default::default(),
    )
}

pub fn get_from_cache<'a, K: Eq + Hash, V: Clone>(
    cache: &'a BasicCache<K, V>,
    key: &'a K,
) -> Option<V> {
    if cache.is_empty() {
        None
    } else {
        cache.get(key)
    }
}

pub type NumberLength = u32;

const MAX_START: EntryId = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(3);
const SEARCH_RETRY_DELAY: Duration = Duration::from_secs(10);
const UNPARSEABLE_RESPONSE_RETRY_DELAY: Duration = Duration::from_secs(10);
const PRP_RESULTS_PER_PAGE: usize = 32;
const PRP_MIN_DIGITS: NumberLength = 300u32;
const PRP_MAX_DIGITS: NumberLength = 80_000u32; // FIXME: Increase this once FactorDB can handle PRP checks on larger numbers without timing out.
const PRP_MAX_DIGITS_FOR_START_OFFSET: NumberLength = 30489;
const U_RESULTS_PER_PAGE: usize = 1;
const PRP_TASK_BUFFER_SIZE: usize = 4 * PRP_RESULTS_PER_PAGE;
const U_TASK_BUFFER_SIZE: usize = 256;
const C_RESULTS_PER_PAGE: usize = 5000;
const C_TASK_BUFFER_SIZE: usize = 8192;
const C_MIN_DIGITS: NumberLength = 92;
const C_MAX_DIGITS: NumberLength = 300;

const U_MIN_DIGITS: NumberLength = 2001;
const U_MAX_DIGITS: NumberLength = 199_999;
const SUBMIT_FACTOR_MAX_ATTEMPTS: usize = 5;
static EXIT_TIME: OnceCell<Instant> = OnceCell::const_new();
pub(crate) static FAILED_U_SUBMISSIONS_OUT: OnceCell<Mutex<File>> = OnceCell::const_new();

#[derive(Clone, Debug, Eq)]
struct CompositeCheckTask {
    id: EntryId,
    digits_or_expr: HipStr<'static>,
}

impl PartialEq<Self> for CompositeCheckTask {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for CompositeCheckTask {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct NumberStatusApiResponse {
    id: Value,
    status: HipStr<'static>,
    factors: Box<[(HipStr<'static>, EntryId)]>,
}

#[derive(Serialize)]
struct FactorSubmission<'a> {
    id: Option<EntryId>,
    number: Option<HipStr<'static>>,
    factor: &'a str,
}

#[framed]
async fn composites_while_waiting(
    end: Instant,
    http: &impl FactorDbClientReadIdsAndExprs,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut CuckooFilter<DefaultHasher>,
) {
    let Some(mut remaining) = end.checked_duration_since(Instant::now()) else {
        return;
    };
    info!("Processing composites for {remaining:?} while other work is waiting");
    loop {
        let Ok((CompositeCheckTask { id, digits_or_expr }, return_permit)) =
            timeout(remaining, c_receiver.recv()).await
        else {
            warn!("Timed out waiting for a composite number to check");
            return;
        };
        check_composite(http, c_filter, id, digits_or_expr, return_permit).await;
        match end.checked_duration_since(Instant::now()) {
            None => {
                info!("Out of time while processing composites");
                return;
            }
            Some(new_remaining) => remaining = new_remaining,
        };
    }
}

#[framed]
async fn check_composite(
    http: &impl FactorDbClientReadIdsAndExprs,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    id: EntryId,
    digits_or_expr: HipStr<'static>,
    return_permit: OwnedPermit<CompositeCheckTask>,
) -> bool {
    if c_filter.contains(&id) {
        info!("{id}: Skipping duplicate C");
        return true;
    }
    let checks_triggered = if http
        .try_get_and_decode(&format!("https://factordb.com/sequences.php?check={id}"))
        .await
        .is_some()
    {
        info!("{id}: Checked C");
        true
    } else {
        false
    };
    // First, convert the composite to digits
    let ProcessedStatusApiResponse {
        factors, status, ..
    } = http.known_factors_as_digits(Id(id), false, true).await;
    if factors.is_empty() {
        if status.is_known_finished() {
            warn!("{id}: Already fully factored");
            true
        } else {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        }
    } else {
        let mut factors_submitted = false;
        let mut dispatched = false;
        for factor in factors {
            if matches!(factor, Factor::Numeric(_)) {
                continue;
            }
            if graph::find_and_submit_factors(http, id, factor.clone(), true).await {
                factors_submitted = true;
            } else {
                if let Some(sender) = YAFU_SENDER.get() {
                    let (lower_bound, upper_bound) = algebraic::estimate_log10(&factor);
                    let number_str = factor.to_unelided_string().into_owned();
                    let item = YafuWorkItem {
                        id,
                        number: number_str,
                        lower_bound,
                        upper_bound,
                    };
                    match sender.send(item).await {
                        Ok(()) => {
                            info!("{id}: Dispatched C to yafu");
                            dispatched = true;
                        }
                        Err(e) => error!("{id}: Failed to send to yafu_task: {e}"),
                    }
                }
            }
        }
        if !dispatched && !checks_triggered && !factors_submitted {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        } else {
            true
        }
    }
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
enum NumberSpecifier<'a> {
    Id(EntryId),
    Expression(Cow<'a, Factor>),
}

impl<'a> Display for NumberSpecifier<'a> {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Id(id) => write!(f, "ID {}", id),
            Expression(e) => write_bignum(f, &e.to_unelided_string()),
        }
    }
}

#[inline(always)]
pub fn write_bignum(f: &mut Formatter, e: &str) -> fmt::Result {
    let len = e.len();
    if len < 300 {
        f.write_str(e)
    } else {
        write!(f, "{}...{}<{}>", &e[..20], &e[(len - 5)..], len)
    }
}

#[inline(always)]
#[framed]
async fn report_primality_proof(id: EntryId, parameter: &str, http: &impl FactorDbClient) {
    let _ = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/index.php?open=Prime&{parameter}=Proof&id={id}"),
            RETRY_DELAY,
        )
        .await;
}

const MAX_CPU_BUDGET_TENTHS: usize = 6000;
static NO_RESERVE: AtomicBool = AtomicBool::new(false);

const STATS_INTERVAL: Duration = Duration::from_mins(1);

pub fn log_stats<T: GlobalAlloc>(
    reg: &mut stats_alloc::Region<T>,
    sys: &mut sysinfo::System,
    backtraces_paused_task: &mut Option<JoinHandle<()>>,
) {
    info!("Allocation stats: {:#?}", reg.change());
    sys.refresh_all();
    info!("System used memory: {}", sys.used_memory());
    info!("System available memory: {}", sys.available_memory());
    info!("Task backtraces:\n{}", taskdump_tree(false));
    match backtraces_paused_task {
        Some(task) => {
            if !task.is_finished() {
                return;
            }
        }
        None => return,
    }
    *backtraces_paused_task = Some(task::spawn(async {
        info!(
            "Task backtraces with all tasks idle:\n{}",
            taskdump_tree(true)
        )
    }));
}

#[tokio::main(flavor = "multi_thread", worker_threads = 1)]
#[framed]
async fn main() -> anyhow::Result<()> {
    let mut reg = stats_alloc::Region::new(&GLOBAL);
    let mut sys = sysinfo::System::new_with_specifics(
        RefreshKind::nothing().with_memory(MemoryRefreshKind::everything()),
    );
    let (shutdown_sender, mut shutdown_receiver) = Monitor::new();
    simple_log::console("info,reqwest=debug").unwrap();

    let signal_installer = task::spawn(async move {
        let sigint = Box::pin(ctrl_c());
        #[cfg(unix)]
        {
            let sigterm = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
                .expect("Failed to create SIGTERM signal stream");
            (sigint, tokio_stream::wrappers::SignalStream::new(sigterm))
        }
        #[cfg(not(unix))]
        (sigint, tokio_stream::pending::<()>())
    });

    let is_no_reserve = std::env::var("NO_RESERVE").is_ok();
    NO_RESERVE.store(is_no_reserve, Release);
    let mut c_digits = std::env::var("C_DIGITS")
        .ok()
        .and_then(|s| s.parse::<NumberLength>().ok());
    let mut u_digits = std::env::var("U_DIGITS")
        .ok()
        .and_then(|s| s.parse::<NumberLength>().ok());
    let prp_start = std::env::var("PRP_START")
        .ok()
        .and_then(|s| s.parse::<EntryId>().ok());
    let mut prp_digits = std::env::var("PRP_DIGITS")
        .ok()
        .and_then(|s| s.parse::<NumberLength>().ok());
    if let Ok(run_number) = std::env::var("RUN") {
        let mut run_number = run_number.parse::<EntryId>()?;
        if let Ok(sub_run_number) = std::env::var("SUB_RUN")
                && let Ok(sub_run_number) = sub_run_number.parse::<EntryId>() {
            run_number += 149993 * (11 + sub_run_number);
        }
        if c_digits.is_none() {
            let mut c_digits_value = C_MAX_DIGITS
                - NumberLength::try_from(
                    (run_number * 19) % EntryId::from(C_MAX_DIGITS - C_MIN_DIGITS + 2),
                )?;
            if c_digits_value == C_MIN_DIGITS - 1 {
                c_digits_value = 1;
            }
            c_digits = Some(c_digits_value);
        }
        if u_digits.is_none() {
            let u_digits_value: NumberLength = U_MIN_DIGITS
                + NumberLength::try_from(
                    (run_number * 19793) % EntryId::from(U_MAX_DIGITS - U_MIN_DIGITS + 1),
                )?;
            u_digits = Some(u_digits_value);
        }
        if prp_digits.is_none() {
            prp_digits = Some(PRP_MIN_DIGITS.saturating_add(NumberLength::try_from(
                (run_number * 9973) % EntryId::from(PRP_MAX_DIGITS - PRP_MIN_DIGITS + 1),
            )?));
        }
        info!("Run number is {run_number}");
    }
    match c_digits {
        Some(0) => info!("Skipping processing of C's"),
        Some(c_digits) => info!("C's will be {c_digits} digits"),
        None => info!("C's will be random sizes"),
    }
    match u_digits {
        Some(0) => info!("Skipping processing of U's"),
        Some(u_digits) => info!("U's will be {u_digits} digits"),
        None => info!("U's will be random sizes"),
    }
    let unknown_status_check_backoff = if let Some(u_digits) = u_digits
        && u_digits != 0
    {
        // max will be 15s + (200_000 * 200_000 * 200_000 / 40_000) ns = 15 s + (8e15 / 4e4)*(1e-9 s) = 215 s
        let u_digits = u_digits as u64;
        Duration::from_secs(15) + Duration::from_nanos(u_digits * u_digits * u_digits / 40_000)
    } else {
        Duration::from_mins(3)
    };
    let mut prp_digits =
        prp_digits.unwrap_or_else(|| rng().random_range(PRP_MIN_DIGITS..=PRP_MAX_DIGITS));
    let mut prp_start = prp_start.unwrap_or_else(|| {
        if prp_digits > PRP_MAX_DIGITS_FOR_START_OFFSET {
            0
        } else {
            rng().random_range(0..=MAX_START)
        }
    });
    if prp_digits > 0 {
        info!("PRP initial start is {prp_start}");
    }
    let rph_limit: NonZeroU32 = if is_no_reserve { 6400 } else { 6100 }.try_into()?;
    let (prp_sender, prp_receiver) = channel(PRP_TASK_BUFFER_SIZE);
    let (u_sender, u_receiver) = channel(U_TASK_BUFFER_SIZE);
    let (c_sender, c_raw_receiver) = channel(C_TASK_BUFFER_SIZE);
    let mut c_receiver = PushbackReceiver::new(c_raw_receiver, &c_sender);
    if std::env::var("CI").is_ok() {
        EXIT_TIME.set(Instant::now().add(Duration::from_mins(355)))?;
    }
    let http = Arc::new(RealFactorDbClient::new(rph_limit));
    // Spawn the yafu factoring task. The channel is bounded so that backpressure
    // propagates naturally if yafu can't keep up.
    let (yafu_tx, yafu_rx) = channel::<YafuWorkItem>(64);
    YAFU_SENDER.set(yafu_tx).expect("YAFU_SENDER already set");
    let yafu_http = http.clone();
    let yafu_shutdown = shutdown_receiver.clone();
    let yafu_task_handle = task::spawn(
        async_backtrace::location!()
            .named_const("Yafu task")
            .frame(async move { yafu_task(yafu_rx, yafu_http, yafu_shutdown).await }),
    );
    let mut c_shutdown_receiver = shutdown_receiver.clone();
    FAILED_U_SUBMISSIONS_OUT
        .get_or_init(async || {
            Mutex::new(
                File::options()
                    .create(true)
                    .append(true)
                    .open("failed-u-submissions.csv")
                    .unwrap(),
            )
        })
        .await;
    let mut prp_filter: CuckooFilter<DefaultHasher> = CuckooFilter::with_capacity(4096);

    // Task to consume PRP's, C's and U's dispatched from the other tasks
    let mut prp_receiver = PushbackReceiver::new(prp_receiver, &prp_sender);
    let mut u_receiver = PushbackReceiver::new(u_receiver, &u_sender);
    let check_c_and_prp_http = http.clone();
    let mut check_c_and_prp_shutdown_receiver = shutdown_receiver.clone();
    let check_c_and_prp = task::spawn(async_backtrace::location!().named_const("Check PRPs/Cs").frame(async move {
        let mut c_filter = CuckooFilter::with_capacity(4096);
        let nm1_regex = Regex::new("id=([0-9]+)\">N-1<").unwrap();
        let np1_regex = Regex::new("id=([0-9]+)\">N\\+1<").unwrap();
        let _bases_regex = Regex::new("Bases checked[^\n]*\n[^\n]*([0-9, ]+)").unwrap();
        let _bases_before_next_cpu_check = 1;
        let _cert_regex = Regex::new("(Verified|Processing)").unwrap();
        loop {
            info!("check_c_and_prp: Polling for next task");
            select! {
                biased;
                _ = check_c_and_prp_shutdown_receiver.recv() => {
                    warn!("check_c_and_prp received shutdown signal; exiting");
                    return;
                }
                (id, task_return_permit) = prp_receiver.recv() => {
                    info!("{id}: Ready to check a PRP");
                    let mut stopped_early = false;
                    let Some(bases_text) = check_c_and_prp_http
                        .retrying_get_and_decode(
                            &format!("https://factordb.com/frame_prime.php?id={id}"),
                            RETRY_DELAY,
                        )
                        .await else {
                        task_return_permit.send(id);
                        info!("{id}: Requeued PRP");
                        continue;
                    };
                    if bases_text.contains("Proven") {
                        info!("{id}: No longer PRP");
                        continue;
                    }
                    #[derive(Debug)]
                    struct NPlusMinus1Info {
                        id: EntryId,
                        parameter: &'static str,
                        known_to_divide_2: bool,
                        known_to_divide_3: bool,
                        factors: Option<Box<[Factor]>>,
                    }

                    if let Some(mut infos) = (async {
                        let mut results = Vec::with_capacity(2);
                        for (parameter, regex) in [("nm1", &nm1_regex), ("np1", &np1_regex)] {
                            if let Some(captures) = regex.captures(&bases_text) {
                                let id_to_check = captures[1].parse::<EntryId>().unwrap();
                                let ProcessedStatusApiResponse {
                                    status,
                                    factors,
                                    ..
                                } = check_c_and_prp_http
                                    .known_factors_as_digits(Id(id_to_check), false, false)
                                    .await;
                                if factors.is_empty() && status == Some(FullyFactored) {
                                    info!("{id}: {parameter} (ID {id_to_check}) is fully factored!");
                                    report_primality_proof(id, parameter, check_c_and_prp_http.as_ref()).await;
                                    return None;
                                }
                                let divide_2 = factors.first().and_then(|f| f.as_numeric()) == Some(2);
                                let divide_3 = factors.first().and_then(|f| f.as_numeric()) == Some(3)
                                    || factors.get(1).and_then(|f| f.as_numeric()) == Some(3);
                                results.push(NPlusMinus1Info {
                                    id: id_to_check,
                                    parameter,
                                    known_to_divide_2: divide_2,
                                    known_to_divide_3: divide_3,
                                    factors: if factors.is_empty() {
                                        None
                                    } else {
                                        Some(factors)
                                    },
                                });
                            } else {
                                error!("{id}: {parameter} ID not found: {bases_text}");
                            }
                        }
                        Some(results)
                    })
                        .await
                    {
                        for info in &mut infos {
                            if !info.known_to_divide_2 {
                                match check_c_and_prp_http.report_numeric_factor(info.id, 2).await {
                                    AlreadyFullyFactored => {
                                        info!(
                                                        "{id}: {} (ID {}) is fully factored!",
                                                        info.parameter, info.id
                                                    );
                                        report_primality_proof(id, info.parameter, check_c_and_prp_http.as_ref())
                                            .await;
                                        stopped_early = true;
                                        break;
                                    }
                                    Accepted => {
                                        info.factors = None;
                                    }
                                    _ => {
                                        error!(
                                                        "{id}: PRP, but factor of 2 was rejected for {} (id {})",
                                                        info.parameter, info.id
                                                    );
                                    }
                                }
                            }
                        }
                        if stopped_early {
                            continue;
                        }
                        if infos.len() == 2 && !infos[0].known_to_divide_3 && !infos[1].known_to_divide_3 {
                            match check_c_and_prp_http.report_numeric_factor(infos[0].id, 3).await {
                                AlreadyFullyFactored => {
                                    info!(
                                                    "{id}: {} (ID {}) is fully factored!",
                                                    infos[0].parameter, infos[0].id
                                                );
                                    report_primality_proof(id, infos[0].parameter, check_c_and_prp_http.as_ref())
                                        .await;
                                    stopped_early = true;
                                }
                                Accepted => {
                                    infos[0].factors = None;
                                }
                                _ => match check_c_and_prp_http.report_numeric_factor(infos[1].id, 3).await {
                                    AlreadyFullyFactored => {
                                        info!(
                                                        "{id}: {} (ID {}) is fully factored!",
                                                        infos[1].parameter, infos[1].id
                                                    );
                                        report_primality_proof(id, infos[1].parameter, check_c_and_prp_http.as_ref())
                                            .await;
                                        stopped_early = true;
                                    }
                                    Accepted => {
                                        infos[1].factors = None;
                                    }
                                    _ => {
                                        error!(
                                                        "{id}: PRP, but factor of 3 was rejected for both N-1 (id {}) and N+1 (id {})",
                                                        infos[0].id, infos[1].id
                                                    );
                                    }
                                },
                            }
                        }
                        if stopped_early {
                            continue;
                        }
                        for info in infos {
                            let factors = if let Some(factors) = info.factors {
                                factors
                            } else {
                                check_c_and_prp_http
                                    .known_factors_as_digits(Id(info.id), false, true)
                                    .await
                                    .factors
                            };
                            for factor in factors {
                                if !matches!(factor, Factor::Numeric(_)) {
                                    graph::find_and_submit_factors(
                                        check_c_and_prp_http.as_ref(),
                                        info.id,
                                        factor,
                                        true,
                                    )
                                        .await;
                                }
                            }
                        }
                    } else {
                        continue;
                    }
                    let status_text = check_c_and_prp_http
                        .retrying_get_and_decode(
                            &format!("https://factordb.com/index.php?open=Prime&ct=Proof&id={id}"),
                            RETRY_DELAY,
                        ).await;
                    if !status_text.as_ref().is_some_and(|status_text| status_text.contains("&lt;")) {
                        error!("{id}: Failed to decode status for PRP: {status_text:?}");
                        composites_while_waiting(
                            Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
                            check_c_and_prp_http.as_ref(),
                            &mut c_receiver,
                            &mut c_filter,
                        )
                            .await;
                        task_return_permit.send(id);
                        info!("{id}: Requeued PRP");
                        continue;
                    };
                    let status_text = status_text.unwrap();
                    if status_text.contains(" is prime") || !status_text.contains("PRP") {
                        info!("{id}: No longer PRP");
                        continue;
                    }
                }

                c_task = c_receiver.recv() => {
                    let (CompositeCheckTask {id, digits_or_expr}, return_permit) = c_task;
                    info!("{id}: Ready to check a C");
                    check_composite(check_c_and_prp_http.as_ref(), &mut c_filter, id, digits_or_expr, return_permit).await;
                }
            }
        }
    }));
    let check_u = if u_digits != Some(0) {
        let mut check_u_shutdown_receiver = shutdown_receiver.clone();
        let check_u_http = http.clone();
        task::spawn(async_backtrace::location!().named_const("Check Us").frame(async move {
            info!("check_u task starting");
            let mut next_unknown_attempt = Instant::now();
            let many_digits_regex =
                Regex::new("&lt;([2-9]|[0-9]+[0-9])[0-9][0-9][0-9][0-9][0-9]&gt;").unwrap();
            let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
            loop {
                info!("check_u: Polling for next task");
                select! {
                    biased;
                    _ = check_u_shutdown_receiver.recv() => {
                        warn!("check_u received shutdown signal; exiting");
                        return;
                    }
                    (id, task_return_permit) = sleep_until(next_unknown_attempt).then(|_| u_receiver.recv())
                    => {
                        info!("{id}: Ready to check a U");
                        let url = format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker");
                        let Some(result) = check_u_http.retrying_get_and_decode(&url, RETRY_DELAY).await else {
                            task_return_permit.send(id);
                            info!("{id}: Requeued U");
                            continue;
                        };
                        if let Some(status) = u_status_regex.captures_iter(&result).next() {
                            match status.get(1) {
                                None => {
                                    if many_digits_regex.is_match(&result) {
                                        warn!("{id}: U is too large for a PRP check!");
                                    } else {
                                        error!("{id}: Failed to decode status for U: {result}");
                                        next_unknown_attempt = Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY;
                                        task_return_permit.send(id);
                                        info!("{id}: Requeued U");
                                    }
                                }
                                Some(matched_status) => match matched_status.as_str() {
                                    "Assigned" => {
                                         info!("Assigned PRP check for unknown-status number with ID {id}");
                                    }
                                    "Please wait" => {
                                        warn!("{id}: Got 'please wait' for U");
                                        next_unknown_attempt = Instant::now() + unknown_status_check_backoff;
                                        task_return_permit.send(id);
                                        info!("{id}: Requeued U");
                                    }
                                    _ => {
                                        warn!("{id}: U is already being checked");
                                    }
                                },
                            }
                        } else if many_digits_regex.is_match(&result) {
                            warn!("{id}: U is too large for a PRP check!");
                        } else {
                            error!("{id}: Failed to decode status for U from result: {result}");
                            next_unknown_attempt = Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY;
                            task_return_permit.send(id);
                            info!("{id}: Requeued U");
                        }
                    }
                }
            }
        }))
    } else {
        task::spawn(async {})
    };
    let queue_u = if u_digits != Some(0) {
        // Task to queue unknowns
        let mut queue_u_shutdown_receiver = shutdown_receiver.clone();
        let u_http = http.clone();
        let mut u_start = if u_digits.is_some() {
            0
        } else {
            rng().random_range(0..=MAX_START)
        };
        task::spawn(async_backtrace::location!().named_const("Queue U's").frame(async move {
            let mut u_filter: CuckooFilter<DefaultHasher> = CuckooFilter::with_capacity(4096);
            loop {
                if queue_u_shutdown_receiver.check_for_shutdown() {
                    warn!("Queue U's task received shutdown signal; exiting");
                    return;
                }
                let digits = u_digits.unwrap_or_else(|| {
                    rng().random_range(U_MIN_DIGITS..=U_MAX_DIGITS)
                });
                if u_digits.is_none() && digits == U_MIN_DIGITS {
                    u_start = 0;
                }
                let u_search_url =
                    format!("https://factordb.com/listtype.php?t=2&perpage={U_RESULTS_PER_PAGE}&start={u_start}&mindig={digits}");
                let Some(results_text) = u_http.try_get_and_decode(&u_search_url).await else {
                    continue;
                };
                info!("U search results retrieved");
                let ids = u_http
                    .read_ids_and_exprs(&results_text);
                let mut advance_start = 0;
                for (u_id, digits_or_expr) in ids {
                    if queue_u_shutdown_receiver.check_for_shutdown() {
                        warn!("try_queue_unknowns thread received shutdown signal; exiting");
                        return;
                    }
                    if !matches!(u_filter.test_and_add(&u_id), Ok(true)) {
                        warn!("{u_id}: Skipping duplicate U");
                        advance_start += 1;
                        continue;
                    }
                    let digits_or_expr = Factor::from(digits_or_expr);
                    if graph::find_and_submit_factors(
                        &*u_http,
                        u_id,
                        digits_or_expr,
                        false,
                    )
                        .await {
                        info!("{u_id}: Skipping PRP check because this former U is now CF or FF");
                    } else {
                        if u_sender.send(u_id).await.is_ok() {
                            info!("{u_id}: Queued U");
                        }
                        advance_start += 1;
                    }
                }
                if u_digits.is_some() {
                    u_start += advance_start;
                    u_start %= MAX_START + 1;
                } else if advance_start != 0 {
                    u_start = rng().random_range(0..=MAX_START);
                }
            }
        }))
    } else {
        task::spawn(async {})
    };
    let mut backtraces_paused_task = None;
    // Monitoring task: print stats periodically
    task::spawn(async move {
        let Ok((mut sigint, mut sigterm)) = signal_installer.await else {
            error!("Failed to install signal handlers!");
            abort();
        };
        info!("Signal handlers installed");
        log_stats(&mut reg, &mut sys, &mut backtraces_paused_task);
        let mut next_backtrace = Instant::now() + STATS_INTERVAL;
        loop {
            select! {
                biased;
                _ = sigterm.next() => {
                    warn!("Received SIGTERM; signaling tasks to exit");
                    break;
                },
                _ = &mut sigint => {
                    warn!("Received SIGINT; signaling tasks to exit");
                    break;
                }
                _ = sleep_until(next_backtrace) => {
                    log_stats(&mut reg, &mut sys, &mut backtraces_paused_task);
                    next_backtrace = Instant::now() + STATS_INTERVAL;
                }
            }
        }
        if let Err(e) = shutdown_sender.send(()) {
            error!("Error sending shutdown signal: {e}");
        }
        // Continue logging stats until other tasks exit
        loop {
            sleep_until(next_backtrace).await;
            log_stats(&mut reg, &mut sys, &mut backtraces_paused_task);
            next_backtrace = Instant::now() + STATS_INTERVAL;
        }
    });
    let queue_c: JoinHandle<Result<(), SendError<()>>> = if c_digits != Some(0) {
        let c_http = http.clone();
        task::spawn(async move {
            let mut c_tasks = Vec::with_capacity(C_RESULTS_PER_PAGE);
            loop {
                let select_start = Instant::now();
                select! {
                    biased;
                    _ = c_shutdown_receiver.recv() => {
                        warn!("queue_c received shutdown signal; exiting");
                        return Ok(());
                    }
                    c_permits = c_sender.reserve_many(C_RESULTS_PER_PAGE) => {
                        let mut c_permits = c_permits?;
                        info!("Ready to send C's from new search after {:?}", Instant::now() - select_start);
                        while c_tasks.is_empty() {
                            let start = if c_digits.is_some_and(|digits| digits < C_MIN_DIGITS) {
                                0
                            } else {
                                rng().random_range(0..=MAX_START)
                            };
                            let mut results_per_page = C_RESULTS_PER_PAGE;
                            let mut composites_page = None;
                            while composites_page.is_none() && results_per_page > 0 {
                                if c_shutdown_receiver.check_for_shutdown() {
                                    return Ok(());
                                }
                                let digits = c_digits.unwrap_or_else(|| {
                                    rng().random_range(C_MIN_DIGITS..=C_MAX_DIGITS)
                                });
                                info!("Retrieving {digits}-digit C's starting from {start}");
                                composites_page = c_http.try_get_and_decode(
                                    &format!("https://factordb.com/listtype.php?t=3&perpage={results_per_page}&start={start}&mindig={digits}")
                                ).await;
                                if composites_page.is_none() {
                                    results_per_page >>= 1;
                                    sleep(SEARCH_RETRY_DELAY).await;
                                }
                            }
                            info!("{results_per_page} C search results retrieved");
                            c_tasks.extend(c_http
                                .read_ids_and_exprs(&composites_page.unwrap())
                                .map(|(id, expr)| CompositeCheckTask {
                                    id,
                                    digits_or_expr: expr.into(),
                                }));
                            c_tasks.shuffle(&mut rng());
                        }
                        let c_sent = c_tasks.len();
                        for task in c_tasks.drain(..) {
                            c_permits.next().unwrap().send(task);
                        }
                        info!("Sent {c_sent} C's to channel");

                    }
                }
            }
        })
    } else {
        task::spawn(async { Ok(()) })
    };
    if prp_digits != 0 {
        'queue_tasks: loop {
            let select_start = Instant::now();
            select! {
                biased;
                _ = shutdown_receiver.recv() => {
                    warn!("Main task received shutdown signal; waiting for other tasks to exit");
                    let _ = queue_u.await;
                    let _ = check_u.await;
                    let _ = queue_c.await;
                    let _ = check_c_and_prp.await;
                    select! {
                        _ = yafu_task_handle => {},
                        _ = sleep(YAFU_KILL_GRACE_PERIOD) => warn!("yafu_task did not finish within grace period"),
                    }
                    return Ok(());
                }
                prp_permits = prp_sender.reserve_many(PRP_RESULTS_PER_PAGE) => {
                    let prp_permits = prp_permits?;
                    info!("Ready to search for PRP's after {:?}", Instant::now() - select_start);
                    let mut results_per_page = PRP_RESULTS_PER_PAGE;
                    let mut results_text = None;
                    while results_text.is_none() && results_per_page > 0 {
                        let prp_search_url = format!("https://factordb.com/listtype.php?t=1&mindig={prp_digits}&perpage={results_per_page}&start={prp_start}");
                        let Some(text) = http.try_get_and_decode(&prp_search_url).await else {
                            sleep(SEARCH_RETRY_DELAY).await;
                            results_per_page >>= 1;
                            continue;
                        };
                        results_text = Some(text);
                        break;
                    }
                    info!("{results_per_page} PRP search results retrieved");
                    let Some(results_text) = results_text else {
                        continue 'queue_tasks;
                    };
                    for ((prp_id, _), prp_permit) in http.read_ids_and_exprs(&results_text).zip(prp_permits)
                    {
                        if !matches!(prp_filter.test_and_add(&prp_id), Ok(true)) {
                            warn!("{prp_id}: Skipping duplicate PRP");
                            continue;
                        }
                        prp_permit.send(prp_id);
                        info!("{prp_id}: Queued PRP from search");
                    }
                    if prp_digits > PRP_MAX_DIGITS_FOR_START_OFFSET {
                        prp_digits += if prp_digits > 100_001 {
                            100
                        } else {
                            1
                        };
                        if prp_digits > PRP_MAX_DIGITS {
                            prp_digits = PRP_MIN_DIGITS;
                        }
                        prp_start = 0;
                    } else {
                        prp_start += PRP_RESULTS_PER_PAGE as EntryId;
                        if prp_start > MAX_START {
                            info!("Restarting PRP search: reached maximum starting index");
                            prp_start = 0;
                            prp_digits += 1;
                        }
                    }
                }
            }
        }
    } else {
        shutdown_receiver.recv().await;
        warn!("Main task received shutdown signal; waiting for other tasks to exit");
        let _ = queue_u.await;
        let _ = check_u.await;
        let _ = queue_c.await;
        let _ = check_c_and_prp.await;
        select! {
            _ = yafu_task_handle => {},
            _ = sleep(YAFU_KILL_GRACE_PERIOD) => warn!("yafu_task did not finish within grace period"),
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ReportFactorResult {
    Accepted,
    DoesNotDivide,
    AlreadyFullyFactored,
    OtherError,
}

const MAX_ID_EQUAL_TO_VALUE: EntryId = 999_999_999_999_999_999;
