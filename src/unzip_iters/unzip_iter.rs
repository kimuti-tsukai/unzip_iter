use std::{
    cell::RefCell,
    fmt::Debug,
    iter::{ExactSizeIterator, FusedIterator},
    rc::Rc,
};

use unzip_borrow::UnzipBorrow;

use super::{
    selector::{self, Selector},
    unzip_api::{UnzipInitialize, UnzipIterAPI},
    unzip_inner::UnzipInner,
};

pub mod unzip_borrow;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Error indicating that a borrow attempt failed because the internal state is already borrowed.
///
/// This error is returned by the [`try_borrow`](UnzipIter::try_borrow) method when the internal state
/// of the iterator is already borrowed, preventing a new borrow from being created.
///
/// # Example
/// ```
/// use unzip_iter::{Unzip, unzip_iters::unzip_iter::TryBorrowError};
///
/// let it = vec![(1, "a"), (2, "b")].into_iter();
/// let (numbers, _) = it.unzip_iter();
///
/// let borrow1 = numbers.try_borrow().unwrap();
/// assert!(matches!(numbers.try_borrow(), Err(TryBorrowError)));
/// ```
pub struct TryBorrowError;

impl std::fmt::Display for TryBorrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "already borrowed")
    }
}

impl std::error::Error for TryBorrowError {}

/// An iterator that yields one side of a tuple from the original iterator.
///
/// [`UnzipIter`] is produced by the [`unzip_iter`](crate::Unzip::unzip_iter) method of the [`Unzip`](crate::Unzip) trait. It is responsible for iterating over
/// either the left or the right elements of the tuples from the original iterator.
///
/// # Example
/// ```
/// use unzip_iter::Unzip;
///
/// let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
/// let (numbers, letters) = it.unzip_iter();
///
/// assert!(numbers.eq(vec![1, 2, 3].into_iter()));
/// assert!(letters.eq(vec!["a", "b", "c"].into_iter()));
/// ```
pub struct UnzipIter<A, B, I, O> {
    queue_selector: Selector<A, B, O>,
    inner: Rc<RefCell<UnzipInner<A, B, I>>>,
}

impl<A, B, I, O> UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    /// Borrows the internal state of the iterator, returning a guard that provides
    /// optimized access to the iterator's elements.
    ///
    /// This method returns a [`UnzipBorrow`] that maintains the borrow for multiple
    /// operations, which can significantly improve performance when multiple consecutive
    /// iterations are needed.
    ///
    /// # Panics
    /// This method will panic if the internal state is already borrowed.
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    ///
    /// let it = vec![(1, "a"), (2, "b")].into_iter();
    /// let (numbers, _) = it.unzip_iter();
    ///
    /// let mut borrow = numbers.borrow();
    /// assert_eq!(borrow.next(), Some(1));
    /// assert_eq!(borrow.next(), Some(2));
    /// ```
    pub fn borrow(&self) -> UnzipBorrow<'_, A, B, I, O> {
        UnzipBorrow::new(self.queue_selector, self.inner.borrow_mut())
    }

    /// Attempts to borrow the internal state of the iterator, returning a guard that
    /// provides optimized access to the iterator's elements.
    ///
    /// Similar to [`borrow`](Self::borrow), but returns a [`Result`] instead of panicking
    /// when the internal state is already borrowed.
    ///
    /// # Returns
    /// - `Ok(UnzipBorrow)` if the borrow was successful
    /// - `Err(TryBorrowError)` if the internal state is already borrowed
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    ///
    /// let it = vec![(1, "a"), (2, "b")].into_iter();
    /// let (numbers, _) = it.unzip_iter();
    ///
    /// let borrow1 = numbers.try_borrow().unwrap();
    /// assert!(numbers.try_borrow().is_err()); // Second borrow fails
    /// ```
    pub fn try_borrow(&self) -> Result<UnzipBorrow<'_, A, B, I, O>, TryBorrowError> {
        self.inner
            .try_borrow_mut()
            .map(|borrow| UnzipBorrow::new(self.queue_selector, borrow))
            .map_err(|_| TryBorrowError)
    }
}

impl<A, B, I, O> Clone for UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)> + Clone,
    A: Clone,
    B: Clone,
{
    fn clone(&self) -> Self {
        UnzipIterAPI::clone(self)
    }
}

impl<A, B, I, O> UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    pub(crate) fn new(
        queue_selector: Selector<A, B, O>,
        rc: Rc<RefCell<UnzipInner<A, B, I>>>,
    ) -> Self {
        Self {
            queue_selector,
            inner: rc,
        }
    }
}

impl<A, B, I, O> UnzipInitialize<A, B, I, O> for UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    type Unzip = (UnzipIter<A, B, I, A>, UnzipIter<A, B, I, B>);

    fn unzip(inner: UnzipInner<A, B, I>) -> Self::Unzip {
        let rc = Rc::new(RefCell::new(inner));
        let left = UnzipIter::new(selector::left(), rc.clone());
        let right = UnzipIter::new(selector::right(), rc.clone());
        (left, right)
    }

    fn with_selector(selector: Selector<A, B, O>, inner: UnzipInner<A, B, I>) -> Self {
        Self::new(selector, Rc::new(RefCell::new(inner)))
    }
}

impl<A, B, I, O> UnzipIterAPI<A, B, I, O> for UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    fn get_inner(&self) -> impl std::ops::Deref<Target = UnzipInner<A, B, I>> {
        self.inner.borrow()
    }

    fn get_inner_mut(&mut self) -> impl std::ops::DerefMut<Target = UnzipInner<A, B, I>> {
        self.inner.borrow_mut()
    }

    fn get_queue_selector(&self) -> Selector<A, B, O> {
        self.queue_selector
    }
}

impl<A, B, I, O> Iterator for UnzipIter<A, B, I, O>
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

impl<A, B, I, O> DoubleEndedIterator for UnzipIter<A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next_back(self)
    }
}

impl<A, B, I, O> ExactSizeIterator for UnzipIter<A, B, I, O> where
    I: Iterator<Item = (A, B)> + ExactSizeIterator
{
}

impl<A, B, I, O> FusedIterator for UnzipIter<A, B, I, O> where
    I: Iterator<Item = (A, B)> + FusedIterator
{
}

impl<A, B, I, O> Debug for UnzipIter<A, B, I, O>
where
    A: Debug,
    B: Debug,
    I: Iterator<Item = (A, B)> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "UnzipIter {{ ... }}")
    }
}

#[cfg(test)]
mod tests {

    use crate::unzip_iters::{Unzip, UnzipIter};

    #[test]
    fn test_basic() {
        // 基本的なケース
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, right) = it.unzip_iter();
        assert!(left.eq(vec![1, 2, 3].into_iter()));
        assert!(right.eq(vec!["a", "b", "c"].into_iter()));

        // 異なる型のペア
        let it = vec![(true, 1.0), (false, 2.0), (true, 3.0)].into_iter();
        let (bools, nums) = it.unzip_iter();
        assert!(bools.eq(vec![true, false, true].into_iter()));
        assert!(nums.eq(vec![1.0, 2.0, 3.0].into_iter()));

        // 重複値を含むケース
        let it = vec![(1, 1), (1, 1), (2, 2)].into_iter();
        let (left, right) = it.unzip_iter();
        assert!(left.eq(vec![1, 1, 2].into_iter()));
        assert!(right.eq(vec![1, 1, 2].into_iter()));
    }

    #[test]
    fn test_empty() {
        let it = vec![].into_iter();
        let (left, right): (UnzipIter<_, _, _, i32>, UnzipIter<_, _, _, i32>) = it.unzip_iter();

        assert!(left.eq(vec![].into_iter()));
        assert!(right.eq(vec![].into_iter()));
    }

    #[test]
    fn test_len() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (left, mut right) = it.unzip_iter();

        right.next();
        assert_eq!(left.len(), 3);
        assert_eq!(right.len(), 2);

        right.next();
        right.next();
        assert_eq!(left.len(), 3);
        assert_eq!(right.len(), 0);

        right.next();
        assert_eq!(right.len(), 0);
    }

    #[test]
    fn test_next_back() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (_left, mut right) = it.unzip_iter();

        assert_eq!(right.next_back(), Some(4));
        assert_eq!(right.next_back(), Some(3));
        assert_eq!(right.next_back(), Some(2));
        assert_eq!(right.next_back(), None);
    }

    #[test]
    fn test_next_mixture() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (mut left, mut right) = it.unzip_iter();

        assert_eq!(left.next(), Some(1));
        assert_eq!(right.next_back(), Some(4));
        assert_eq!(left.next(), Some(3));
        assert_eq!(right.next(), Some(2));
        assert_eq!(left.next_back(), Some(5));
        assert_eq!(right.next_back(), Some(3));
        assert_eq!(left.next_back(), None);
        assert_eq!(right.next(), None);
    }

    #[test]
    fn test_rev_loop() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (left, right) = it.unzip_iter();

        let mut v = Vec::new();
        for (l, r) in left.zip(right.rev()) {
            v.push((l, r));
        }

        assert_eq!(v, vec![(1, 4), (3, 3), (5, 2)]);
    }

    #[test]
    fn test_not_clone() {
        #[derive(Debug, PartialEq, Eq)]
        struct NotClone;

        let it = vec![(NotClone, NotClone)].into_iter();
        let (left, right) = it.unzip_iter();

        assert!(left.eq(vec![NotClone].into_iter()));
        assert!(right.eq(vec![NotClone].into_iter()));
    }

    #[test]
    fn test_clone() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (left, right) = it.unzip_iter();
        let left_clone = left.clone();

        assert!(left.eq(vec![1, 3, 5].into_iter()));
        assert!(left_clone.eq(vec![1, 3, 5].into_iter()));
        assert!(right.eq(vec![2, 3, 4].into_iter()));
    }
}
