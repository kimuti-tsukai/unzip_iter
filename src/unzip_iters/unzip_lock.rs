use std::{
    fmt::Debug,
    iter::{ExactSizeIterator, FusedIterator},
    ops::DerefMut,
};

use crate::unzip_iters::{selector::Selector, unzip_api::UnzipIterAPI, unzip_inner::UnzipInner};

/// An internal iterator type that holds a lock on the underlying data structure.
/// This type is not meant to be used directly by users.
///
/// This iterator is created by other public iterator types in this crate and manages
/// access to the shared internal state while iterating.
///
/// # Type Parameters
///
/// * `T` - The type of the lock guard that provides mutable access to `UnzipInner`
/// * `A` - The type of the first element in the tuple
/// * `B` - The type of the second element in the tuple
/// * `I` - The type of the source iterator that yields `(A, B)` tuples
/// * `O` - The output type of this iterator
pub struct UnzipLock<T, A, B, O> {
    selector: Selector<A, B, O>,
    borrow: T,
}

impl<T, A, B, I, O> UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    I: Iterator<Item = (A, B)>,
{
    pub(super) fn new(selector: Selector<A, B, O>, borrow: T) -> Self {
        Self { selector, borrow }
    }
}

impl<T, A, B, I, O> UnzipIterAPI<A, B, I, O> for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    for<'a> I: Iterator<Item = (A, B)> + 'a,
{
    fn get_inner(&self) -> impl std::ops::Deref<Target = UnzipInner<A, B, I>> {
        self.borrow.deref()
    }

    fn get_inner_mut(&mut self) -> impl std::ops::DerefMut<Target = UnzipInner<A, B, I>> {
        self.borrow.deref_mut()
    }

    fn get_queue_selector(&self) -> Selector<A, B, O> {
        self.selector
    }
}

impl<T, A, B, I, O> Iterator for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    for<'a> I: Iterator<Item = (A, B)> + 'a,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next(self)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        UnzipIterAPI::size_hint(self)
    }
}

impl<T, A, B, I, O> DoubleEndedIterator for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    for<'a> I: DoubleEndedIterator<Item = (A, B)> + 'a,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next_back(self)
    }
}

impl<T, A, B, I, O> ExactSizeIterator for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    for<'a> I: ExactSizeIterator<Item = (A, B)> + 'a,
{
}

impl<T, A, B, I, O> FusedIterator for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    for<'a> I: FusedIterator<Item = (A, B)> + 'a,
{
}

impl<T, A, B, I, O> Debug for UnzipLock<T, A, B, O>
where
    T: DerefMut<Target = UnzipInner<A, B, I>>,
    I: Iterator<Item = (A, B)> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "UnzipLock {{ ... }}")
    }
}

#[cfg(test)]
mod tests {
    use crate::unzip_iters::{selector::Selector, unzip_inner::UnzipInner, unzip_lock::UnzipLock};

    /// テスト用の簡単なイテレータを作成するヘルパー関数
    fn create_test_iter() -> std::vec::IntoIter<(i32, String)> {
        vec![
            (1, "one".to_string()),
            (2, "two".to_string()),
            (3, "three".to_string()),
        ]
        .into_iter()
    }

    #[test]
    fn test_unzip_lock_first() {
        let iter = create_test_iter();
        let mut inner = UnzipInner::new(iter);
        let mut lock = UnzipLock::new(Selector::<i32, String, i32>::LEFT, &mut inner);

        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next(), Some(2));
        assert_eq!(lock.next(), Some(3));
        assert_eq!(lock.next(), None);
    }

    #[test]
    fn test_unzip_lock_second() {
        let iter = create_test_iter();
        let mut inner = UnzipInner::new(iter);
        let mut lock = UnzipLock::new(Selector::<i32, String, String>::RIGHT, &mut inner);

        assert_eq!(lock.next(), Some("one".to_string()));
        assert_eq!(lock.next(), Some("two".to_string()));
        assert_eq!(lock.next(), Some("three".to_string()));
        assert_eq!(lock.next(), None);
    }

    #[test]
    fn test_unzip_lock_size_hint() {
        let iter = create_test_iter();
        let mut inner = UnzipInner::new(iter);
        let lock = UnzipLock::new(Selector::<i32, String, i32>::LEFT, &mut inner);

        assert_eq!(lock.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_unzip_lock_next_back() {
        let iter = create_test_iter();
        let mut inner = UnzipInner::new(iter);
        let mut lock = UnzipLock::new(Selector::<i32, String, i32>::LEFT, &mut inner);

        assert_eq!(lock.next_back(), Some(3));
        assert_eq!(lock.next_back(), Some(2));
        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next(), None);
    }

    #[test]
    fn test_unzip_lock_mixed_iteration() {
        let iter = create_test_iter();
        let mut inner = UnzipInner::new(iter);
        let mut lock = UnzipLock::new(Selector::<i32, String, i32>::LEFT, &mut inner);

        assert_eq!(lock.next(), Some(1));
        assert_eq!(lock.next_back(), Some(3));
        assert_eq!(lock.next(), Some(2));
        assert_eq!(lock.next(), None);
        assert_eq!(lock.next_back(), None);
    }
}
