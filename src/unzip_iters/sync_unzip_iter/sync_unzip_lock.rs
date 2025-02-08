use std::sync::MutexGuard;

use crate::unzip_iters::{unzip_inner::UnzipInner, unzip_lock::UnzipLock};

/// A guard that holds a lock on the shared state of a [`SyncUnzipIter`](super::SyncUnzipIter).
///
/// This type provides optimized access to the iterator's elements by maintaining
/// the lock for multiple operations. This is particularly useful when you need to
/// perform multiple consecutive iterations.
///
/// # Performance
/// Using `SyncUnzipLock` can significantly improve performance when multiple
/// consecutive operations are needed, as it avoids the overhead of acquiring
/// and releasing the lock for each operation.
///
/// # Deadlock Safety
/// The lock is automatically released when the `SyncUnzipLock` is dropped.
/// To avoid deadlocks, ensure that you don't hold multiple locks simultaneously
/// and drop the lock when it's no longer needed.
///
/// # Example
/// ```
/// use unzip_iter::Unzip;
///
/// let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
/// let (left, _) = it.unzip_iter_sync();
///
/// // The lock is automatically released at the end of this block
/// {
///     let mut lock = left.lock().unwrap();
///     assert_eq!(lock.next(), Some(1));
///     assert_eq!(lock.next(), Some(2));
///     assert_eq!(lock.next(), Some(3));
/// } // lock is dropped here
/// ```
pub type SyncUnzipLock<'a, A, B, I, O> = UnzipLock<MutexGuard<'a, UnzipInner<A, B, I>>, A, B, O>;

#[cfg(test)]
mod tests {
    use crate::{unzip_iters::sync_unzip_iter::TryLockError, Unzip};

    #[test]
    fn test_continuous_next() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        // 一度のロックで複数の要素を取得
        let mut lock = left.lock().unwrap();
        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next(), Some(2));
        assert_eq!(lock.next(), Some(3));
        assert_eq!(lock.next(), None);
    }

    #[test]
    fn test_double_ended_iterator() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (_, right) = it.unzip_iter_sync();

        let mut lock = right.lock().unwrap();
        assert_eq!(lock.next(), Some("a"));
        assert_eq!(lock.next_back(), Some("c"));
        assert_eq!(lock.next(), Some("b"));
        assert_eq!(lock.next(), None);
        assert_eq!(lock.next_back(), None);
    }

    #[test]
    fn test_size_hint() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        let mut lock = left.lock().unwrap();
        assert_eq!(lock.size_hint(), (3, Some(3)));

        lock.next();
        assert_eq!(lock.size_hint(), (2, Some(2)));

        lock.next();
        assert_eq!(lock.size_hint(), (1, Some(1)));

        lock.next();
        assert_eq!(lock.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_mixed_iteration() {
        let it = vec![(1, "a"), (2, "b"), (3, "c"), (4, "d")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        // 前方と後方からの混合イテレーション
        let mut lock = left.lock().unwrap();
        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next_back(), Some(4));
        assert_eq!(lock.next(), Some(2));
        assert_eq!(lock.next_back(), Some(3));
        assert_eq!(lock.next(), None);
        assert_eq!(lock.next_back(), None);
    }

    #[test]
    fn test_lock_drop_behavior() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, right) = it.unzip_iter_sync();

        // 左側のロックを取得して一部イテレート
        {
            let mut left_lock = left.lock().unwrap();
            assert_eq!(left_lock.next(), Some(1));
            assert_eq!(left_lock.next(), Some(2));
            // ここでleft_lockがドロップされる
        }

        // 右側のロックを取得して残りをイテレート
        let mut right_lock = right.lock().unwrap();
        assert_eq!(right_lock.next(), Some("a"));
        assert_eq!(right_lock.next(), Some("b"));
        assert_eq!(right_lock.next(), Some("c"));
    }

    #[test]
    fn test_try_lock() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        let mut lock = left.try_lock().unwrap();
        assert_eq!(lock.next(), Some(1));
    }

    #[test]
    fn test_dead_lock() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        let _lock = left.lock().unwrap();

        let lock = left.try_lock().unwrap_err();
        assert_eq!(lock, TryLockError::WouldBlock);
    }
}
