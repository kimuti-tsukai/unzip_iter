use std::{error::Error, fmt::Display};

/// Represents errors that can occur when attempting to acquire a lock without blocking.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TryLockError {
    /// The operation would block.
    WouldBlock,
    /// The inner iterator panicked.
    Paniced,
}

impl Display for TryLockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WouldBlock => write!(f, "try_lock failed because the operation would block"),
            Self::Paniced => write!(f, "try_lock failed because the inner iterator paniced"),
        }
    }
}

impl Error for TryLockError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LockError;

impl Display for LockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to Lock. Iterator paniced.")
    }
}

impl Error for LockError {}
