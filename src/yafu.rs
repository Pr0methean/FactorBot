use crate::FAILED_U_SUBMISSIONS_OUT;
use crate::NumberLength;
use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored};
use crate::algebraic::Factor;
use crate::graph::EntryId;
use crate::monitor::Monitor;
use crate::net::{FactorDbClient, RealFactorDbClient};

use alloc::sync::Arc;
use async_backtrace::framed;
use hipstr::HipStr;
use log::{error, info, warn};
use regex::Regex;
use std::borrow::Cow;
use std::collections::{BinaryHeap, HashSet};
use std::io::Write;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicBool, Ordering};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::Command;
use tokio::select;
use tokio::sync::OnceCell;
use tokio::sync::mpsc::Receiver;
use tokio::task;
use tokio::time::{Duration, Instant, sleep};

pub static YAFU_SENDER: OnceCell<tokio::sync::mpsc::Sender<YafuWorkItem>> = OnceCell::const_new();

/// Duration to wait after shutdown before forcibly killing yafu.
pub const YAFU_KILL_GRACE_PERIOD: Duration = Duration::from_secs(120);

/// Regex matching yafu factor output lines, e.g. "P15 = 123456789012345" or "factor = 123456789012345".
static YAFU_FACTOR_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?i)(?:P\d+|factor)\s*=\s*([0-9]+)").unwrap());

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct YafuWorkItem {
    pub id: Option<EntryId>,
    pub number: HipStr<'static>,
    pub lower_bound: NumberLength,
    pub upper_bound: NumberLength,
}

impl Ord for YafuWorkItem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .upper_bound
            .cmp(&self.upper_bound)
            .then_with(|| other.lower_bound.cmp(&self.lower_bound))
            .then_with(|| other.id.cmp(&self.id))
    }
}

impl PartialOrd for YafuWorkItem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn is_sigill(status: &std::process::ExitStatus) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        status.signal() == Some(4)
    }
    #[cfg(windows)]
    {
        status.code() == Some(0xC000001D_u32 as i32)
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = status;
        false
    }
}

async fn wait_for_status(child: &mut tokio::process::Child) -> Option<std::process::ExitStatus> {
    match tokio::time::timeout(Duration::from_secs(5), child.wait()).await {
        Ok(Ok(status)) => Some(status),
        _ => None,
    }
}

struct PersistentYafu {
    child: tokio::process::Child,
    stdin: tokio::process::ChildStdin,
    stdout_reader: tokio::io::Lines<BufReader<tokio::process::ChildStdout>>,
}

impl PersistentYafu {
    async fn spawn() -> std::io::Result<Self> {
        let mut child = Command::new("./yafu")
            .args([
                "-threads",
                "4",
                "-R",
                "-qssave",
                "./qs",
                "-session",
                "./session",
                "-logfile",
                "./log",
                "-o",
                "./nfs",
                "-pscreen",
                "-inmem",
                "2000000000",
            ])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;

        let stdin = child.stdin.take().expect("stdin piped");
        let stdout = child.stdout.take().expect("stdout piped");
        let stderr = child.stderr.take().expect("stderr piped");

        task::spawn(async move {
            let mut stderr_reader = BufReader::new(stderr).lines();
            while let Ok(Some(line)) = stderr_reader.next_line().await {
                info!("yafu stderr: {line}");
            }
        });

        let stdout_reader = BufReader::new(stdout).lines();
        Ok(Self {
            child,
            stdin,
            stdout_reader,
        })
    }
}

/// Task that factors composite numbers using a persistent yafu binary and submits found factors
/// to FactorDB. Runs until the channel is closed (all other tasks have exited), then waits up
/// to [`YAFU_KILL_GRACE_PERIOD`] for any in-progress yafu invocation to complete before killing it.
#[framed]
pub async fn yafu_task(
    mut receiver: Receiver<YafuWorkItem>,
    http: Arc<RealFactorDbClient>,
    mut shutdown: Monitor,
) {
    let mut in_flight: HashSet<EntryId> = HashSet::new();
    let mut heap: BinaryHeap<YafuWorkItem> = BinaryHeap::new();
    let mut shutdown_received = false;

    let mut persistent_yafu: Option<PersistentYafu> = match PersistentYafu::spawn().await {
        Ok(y) => {
            info!("Started yafu process ahead of time");
            Some(y)
        }
        Err(e) => {
            error!("Failed to spawn initial yafu process ahead of time: {e}");
            None
        }
    };

    loop {
        if persistent_yafu.is_none() && !shutdown_received {
            match PersistentYafu::spawn().await {
                Ok(y) => {
                    info!("Restarted yafu process ahead of time");
                    persistent_yafu = Some(y);
                }
                Err(e) => {
                    error!("Failed to restart yafu process ahead of time: {e}");
                }
            }
        }

        while let Ok(item) = receiver.try_recv() {
            if item.id.is_none_or(|id| in_flight.insert(id)) {
                heap.push(item);
            } else {
                info!("{}: Skipping duplicate yafu dispatch", item.id.unwrap());
            }
        }

        if heap.is_empty() {
            if shutdown_received {
                info!("yafu_task: channel closed/shutdown received and work queue empty; exiting");
                break;
            }

            select! {
                biased;
                _ = shutdown.recv() => {
                    warn!("yafu_task received shutdown signal");
                    break;
                }
                item = receiver.recv(), if !shutdown_received => {
                    match item {
                        Some(item) => {
                            if item.id.is_none_or(|id| in_flight.insert(id)) {
                                heap.push(item);
                            } else {
                                info!("{}: Skipping duplicate yafu dispatch", item.id.unwrap());
                            }
                        }
                        None => {
                            info!("yafu_task: receiver channel closed");
                            shutdown_received = true;
                            if heap.is_empty() {
                                break;
                            }
                        }
                    }
                }
            }
        }
        let Some(item) = heap.pop() else {
            continue;
        };

        let id = item.id;
        let number = item.number;

        if persistent_yafu.is_none() {
            match PersistentYafu::spawn().await {
                Ok(y) => {
                    info!("Spawned new yafu process");
                    persistent_yafu = Some(y);
                }
                Err(e) => {
                    error!("Failed to spawn yafu process: {e}");
                    if let Some(id) = id {
                        in_flight.remove(&id);
                    }
                    continue;
                }
            }
        }

        let yafu = persistent_yafu.as_mut().unwrap();
        info!(
            "{id:?}: Factoring with yafu (bounds: {}..{})",
            item.lower_bound, item.upper_bound
        );
        let start = Instant::now();
        let expr = if item.upper_bound > 93 {
            format!("factor({number})\n")
        } else {
            format!("mpqs({number})\n")
        };
        let write = async {
            yafu.stdin.write_all(expr.as_bytes()).await?;
            yafu.stdin.flush().await
        };
        if let Err(e) = write.await {
            let status = wait_for_status(&mut yafu.child).await;
            if status.as_ref().is_some_and(is_sigill) {
                error!(
                    "{id:?}: yafu process exited with SIGILL while writing stdin; aborting composite ({number}) and restarting yafu"
                );
            } else {
                error!("{id:?}: Failed to write to yafu stdin: {e}");
                if let Some(id) = id {
                    in_flight.remove(&id);
                }
            }
            persistent_yafu = None;
            continue;
        }

        let composite = Factor::from(number.as_str());
        let mut found_factors_count = 0usize;
        let mut yafu_failed = false;
        let specifier = if let Some(id) = id {
            Id(id)
        } else {
            Expression(Cow::Owned(composite))
        };
        let kill_yafu = Arc::new(AtomicBool::new(false));
        while !kill_yafu.load(Ordering::Acquire) && !yafu_failed {
            select! {
                biased;
                incoming = receiver.recv(), if !shutdown_received => {
                    match incoming {
                        Some(new_item) => {
                            if new_item.id.is_none_or(|id| in_flight.insert(id)) {
                                heap.push(new_item);
                            }
                        }
                        None => {
                            shutdown_received = true;
                        }
                    }
                }
                line = yafu.stdout_reader.next_line() => {
                    match line {
                        Ok(Some(line)) => {
                            if let Some(caps) = YAFU_FACTOR_REGEX.captures(&line) {
                                let factor_str = caps[1].to_owned();
                                info!("{id:?}: yafu found factor {factor_str}");
                                found_factors_count += 1;

                                let http = http.clone();
                                let number = number.clone();
                                let kill_yafu = kill_yafu.clone();
                                let specifier = specifier.clone();
                                task::spawn(async move {
                                    let factor = Factor::from(factor_str.as_str());
                                    match http.try_report_factor(
                                        &specifier,
                                        &factor,
                                    ).await {
                                        Accepted => info!("{specifier}: Submitted factor {factor_str} to FactorDB"),
                                        AlreadyFullyFactored => {
                                            info!("{specifier}: Factor {factor_str} already known");
                                            kill_yafu.store(true, Ordering::Release);
                                        }
                                        result => {
                                            error!("{specifier}: Error submitting factor {factor_str}: {result:?}");
                                            if let Some(out) = FAILED_U_SUBMISSIONS_OUT.get() {
                                                match out.lock().await.write_fmt(format_args!("{number},{factor_str}\n")) {
                                                    Ok(_) => warn!("{specifier}: Wrote failed factor {factor_str} to failed-u-submissions.csv"),
                                                    Err(e) => error!("{specifier}: Failed to write {factor_str} to failed-u-submissions.csv: {e}"),
                                                }
                                            }
                                        }
                                    }
                                });
                            } else {
                                info!("{specifier}: yafu: {line}");
                            }

                            if line.contains("ans = 1") {
                                break;
                            }
                        }
                        Ok(None) => {
                            let status = wait_for_status(&mut yafu.child).await;
                            if status.as_ref().is_some_and(is_sigill) {
                                error!(
                                    "{specifier}: yafu process exited with SIGILL while factoring composite {number}; aborting composite and restarting yafu"
                                );
                            } else {
                                error!("{specifier}: yafu stdout closed unexpectedly (status: {status:?})");
                            }
                            yafu_failed = true;
                        }
                        Err(e) => {
                            let status = wait_for_status(&mut yafu.child).await;
                            if status.as_ref().is_some_and(is_sigill) {
                                error!(
                                    "{specifier}: yafu process exited with SIGILL while factoring composite {number}; aborting composite and restarting yafu"
                                );
                            } else {
                                error!("{specifier}: Error reading yafu stdout: {e} (status: {status:?})");
                            }
                            yafu_failed = true;
                        }
                    }
                }
            }
        }

        let elapsed = start.elapsed();
        let elapsed_secs = elapsed.as_secs();
        let elapsed_nanos = elapsed.subsec_nanos();
        if found_factors_count == 0 {
            warn!(
                "{specifier}: yafu found no factors after {:02}:{:02}.{:09}",
                elapsed_secs / 60,
                elapsed_secs % 60,
                elapsed_nanos
            );
        } else {
            info!(
                "{specifier}: Done factoring with yafu after {:02}:{:02}.{:09}",
                elapsed_secs / 60,
                elapsed_secs % 60,
                elapsed_nanos
            );
        }
        if kill_yafu.load(Ordering::Acquire) {
            let _ = yafu.child.kill().await;
            persistent_yafu = None;
        } else if yafu_failed {
            persistent_yafu = None;
        }
    }

    if let Some(mut yafu) = persistent_yafu {
        let _ = yafu.stdin.write_all(b"exit()\n").await;
        let _ = yafu.stdin.flush().await;
        select! {
            _ = yafu.child.wait() => {
                info!("yafu process exited cleanly");
            }
            _ = sleep(YAFU_KILL_GRACE_PERIOD) => {
                warn!("yafu grace period expired on shutdown; killing process");
                let _ = yafu.child.kill().await;
                let _ = yafu.child.wait().await;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(unix)]
    fn test_is_sigill_unix() {
        use std::os::unix::process::ExitStatusExt;
        let status_sigill = std::process::ExitStatus::from_raw(4);
        assert!(is_sigill(&status_sigill));

        let status_normal = std::process::ExitStatus::from_raw(0);
        assert!(!is_sigill(&status_normal));

        let status_sigterm = std::process::ExitStatus::from_raw(15);
        assert!(!is_sigill(&status_sigterm));
    }

    #[test]
    #[cfg(windows)]
    fn test_is_sigill_windows() {
        use std::os::windows::process::ExitStatusExt;
        let status_sigill = std::process::ExitStatus::from_raw(0xC000001D);
        assert!(is_sigill(&status_sigill));

        let status_normal = std::process::ExitStatus::from_raw(0);
        assert!(!is_sigill(&status_normal));
    }
}
