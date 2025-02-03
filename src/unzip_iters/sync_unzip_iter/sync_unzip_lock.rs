use std::{
    fmt::Debug,
    iter::{FusedIterator, Iterator},
    ops::{Deref, DerefMut},
    sync::MutexGuard,
};

use crate::unzip_iters::{selector::Selector, unzip_api::UnzipIterAPI, unzip_inner::UnzipInner};

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
///     let mut lock = left.lock();
///     assert_eq!(lock.next(), Some(1));
///     assert_eq!(lock.next(), Some(2));
///     assert_eq!(lock.next(), Some(3));
/// } // lock is dropped here
/// ```
pub struct SyncUnzipLock<'a, A, B, I: Iterator<Item = (A, B)>, O> {
    selector: Selector<A, B, O>,
    lock: MutexGuard<'a, UnzipInner<A, B, I>>,
}

impl<'a, A, B, I, O> SyncUnzipLock<'a, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    pub(super) fn new(
        selector: Selector<A, B, O>,
        lock: MutexGuard<'a, UnzipInner<A, B, I>>,
    ) -> Self {
        Self { selector, lock }
    }
}

impl<A, B, I, O> UnzipIterAPI<A, B, I, O> for SyncUnzipLock<'_, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    fn get_inner(&self) -> impl std::ops::Deref<Target = UnzipInner<A, B, I>> {
        self.lock.deref()
    }

    fn get_inner_mut(&mut self) -> impl std::ops::DerefMut<Target = UnzipInner<A, B, I>> {
        self.lock.deref_mut()
    }

    fn get_queue_selector(&self) -> Selector<A, B, O> {
        self.selector
    }
}

impl<A, B, I, O> Iterator for SyncUnzipLock<'_, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next(self)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        UnzipIterAPI::size_hint(self)
    }
}

impl<A, B, I, O> DoubleEndedIterator for SyncUnzipLock<'_, A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next_back(self)
    }
}

impl<A, B, I, O> FusedIterator for SyncUnzipLock<'_, A, B, I, O> where
    I: FusedIterator<Item = (A, B)>
{
}

impl<A, B, I, O> Debug for SyncUnzipLock<'_, A, B, I, O>
where
    I: Iterator<Item = (A, B)> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SyncUnzipLock {{ ... }}")
    }
}

impl<A, B, I, O> ExactSizeIterator for SyncUnzipLock<'_, A, B, I, O> where
    I: ExactSizeIterator<Item = (A, B)>
{
}

#[cfg(test)]
mod tests {
    use crate::{unzip_iters::sync_unzip_iter::TryLockError, Unzip};

    #[test]
    fn test_continuous_next() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter_sync();

        // 一度のロックで複数の要素を取得
        let mut lock = left.lock();
        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next(), Some(2));
        assert_eq!(lock.next(), Some(3));
        assert_eq!(lock.next(), None);
    }

    #[test]
    fn test_double_ended_iterator() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (_, right) = it.unzip_iter_sync();

        let mut lock = right.lock();
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

        let mut lock = left.lock();
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
        let mut lock = left.lock();
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
            let mut left_lock = left.lock();
            assert_eq!(left_lock.next(), Some(1));
            assert_eq!(left_lock.next(), Some(2));
            // ここでleft_lockがドロップされる
        }

        // 右側のロックを取得して残りをイテレート
        let mut right_lock = right.lock();
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

        let _lock = left.lock();

        let lock = left.try_lock().unwrap_err();
        assert_eq!(lock, TryLockError::WouldBlock);
    }
}
