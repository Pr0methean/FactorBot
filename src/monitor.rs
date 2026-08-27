// Adapted from: https://github.com/tokio-rs/mini-redis/blob/e186482ca00f8d884ddcbe20417f3654d03315a4/src/shutdown.rs

use async_backtrace::framed;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::{Acquire, Release};
use tokio::sync::broadcast::{Receiver, Sender, channel};
use tokio::time::sleep_until;

use crate::EXIT_TIME;

/// Shutdown is signalled using a `broadcast::Receiver`. Only a single value is
/// ever sent. Once a value has been sent via the broadcast channel, the server
/// should shut down.
///
/// The `Monitor` struct listens for the signal and tracks that the signal has
/// been received. Callers may query for whether the shutdown signal has been
/// received or not.
#[derive(Debug)]
pub(crate) struct Monitor {
    /// `true` if the shutdown signal has been received
    is_shutdown: Arc<AtomicBool>,

    /// The receiving half of the channel used to listen for shutdown.
    shutdown_notify: Receiver<()>,

    /// A sender clone kept so this Monitor can broadcast the shutdown signal
    /// itself (e.g. when EXIT_TIME is reached).
    shutdown_sender: Sender<()>,
}

impl Monitor {
    /// Create a new `Monitor` and a sender for it.
    pub(crate) fn new() -> (Sender<()>, Monitor) {
        let (sender, notify) = channel(1);
        (
            sender.clone(),
            Monitor {
                is_shutdown: Arc::new(false.into()),
                shutdown_notify: notify,
                shutdown_sender: sender,
            },
        )
    }

    /// Returns `true` if the shutdown signal has been received.
    pub(crate) fn check_for_shutdown(&mut self) -> bool {
        if self.shutdown_notify.try_recv().is_ok() {
            self.is_shutdown.store(true, Release);
            true
        } else {
            self.is_shutdown.load(Acquire)
        }
    }

    /// Receive the shutdown notice, waiting if necessary.
    ///
    /// If `EXIT_TIME` is set, this will also trigger the shutdown signal when
    /// that deadline is reached.
    #[framed]
    pub(crate) async fn recv(&mut self) {
        // If the shutdown signal has already been received, then return
        // immediately.
        if self.is_shutdown.load(Acquire) {
            return;
        }

        if let Some(&exit_time) = EXIT_TIME.get() {
            // Race between the broadcast channel and the EXIT_TIME deadline.
            // Cannot receive a "lag error" as only one value is ever sent.
            tokio::select! {
                _ = self.shutdown_notify.recv() => {}
                _ = sleep_until(exit_time) => {
                    // Broadcast the shutdown signal so all other Monitor
                    // clones are also notified.
                    let _ = self.shutdown_sender.send(());
                }
            }
        } else {
            // No deadline configured – wait for the broadcast signal only.
            // Cannot receive a "lag error" as only one value is ever sent.
            let _ = self.shutdown_notify.recv().await;
        }

        // Remember that the signal has been received.
        self.is_shutdown.store(true, Release);
    }
}

impl Clone for Monitor {
    /// All clones will receive the shutdown from the same sender.
    fn clone(&self) -> Self {
        Monitor {
            is_shutdown: self.is_shutdown.clone(),
            shutdown_notify: self.shutdown_notify.resubscribe(),
            shutdown_sender: self.shutdown_sender.clone(),
        }
    }
}
