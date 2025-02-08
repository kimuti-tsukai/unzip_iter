use std::{error::Error, fmt::Display};

/// Represents errors that can occur when attempting to acquire a lock without blocking.
///
/// This error is returned by the [`try_lock`](crate::SyncUnzipIter::try_lock) method when the lock
/// cannot be acquired immediately. It indicates whether the lock would block or if the inner
/// iterator has panicked.
///
/// # Example
/// ```
/// use unzip_iter::{Unzip, unzip_iters::sync_unzip_iter::errors::TryLockError};
///
/// let it = vec![(1, "a"), (2, "b")].into_iter();
/// let (numbers, _) = it.unzip_iter_sync();
///
/// let lock1 = numbers.try_lock().unwrap();
/// assert!(matches!(numbers.try_lock(), Err(TryLockError::WouldBlock)));
/// ```
///
/// # Variants
/// - `WouldBlock`: The operation would block because the lock is held by another thread.
/// - `Panicekd`: The inner iterator panicked while holding the lock.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TryLockError {
    /// The operation would block.
    WouldBlock,
    /// The inner iterator panicked.
    Panicked,
}

impl Display for TryLockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WouldBlock => write!(f, "try_lock failed because the operation would block"),
            Self::Panicked => write!(f, "try_lock failed because the inner iterator panicked"),
        }
    }
}

impl Error for TryLockError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LockError;

impl Display for LockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to Lock. Iterator panicked.")
    }
}

impl Error for LockError {}
