//! Unzip iterators
//! This module provides a trait [`Unzip`] that allows splitting an iterator over tuples into two separate iterators.
//!
//! The [`Unzip`] trait simplifies the process of working with iterators of tuples by providing a method [`unzip_iter`](crate::Unzip::unzip_iter). This method produces two independent iterators, each iterating over one side of the tuple. This can be especially useful when you need to process or collect the components of the tuples separately.
//!
//! # Example
//! ```
//! use unzip_iter::Unzip;
//!
//! let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
//! let (left, right) = it.unzip_iter();
//!
//! assert!(left.eq(vec![1, 3, 5].into_iter()));
//! assert!(right.eq(vec![2, 3, 4].into_iter()));
//! ```
//!
//! The module also provides [`SyncUnzipIter`] for thread-safe usage via [`Arc`] and [`Mutex`].

use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::Debug,
    iter::FusedIterator,
    rc::Rc,
    sync::{Arc, Mutex},
};

/// A trait to split an iterator over tuples into two separate iterators.
///
/// The [`Unzip`] trait extends any iterator over tuples `(A, B)` by providing the [`unzip_iter`](crate::Unzip::unzip_iter) method.
/// This method enables splitting the original iterator into two independent iterators: one for the left elements
/// and another for the right elements.
///
/// # Example
/// ```
/// use unzip_iter::Unzip;
///
/// let it = vec![("a", 1), ("b", 2), ("c", 3)].into_iter();
/// let (keys, values) = it.unzip_iter();
///
/// assert!(keys.eq(vec!["a", "b", "c"].into_iter()));
/// assert!(values.eq(vec![1, 2, 3].into_iter()));
/// ```
///
/// This can be particularly useful when working with collections of key-value pairs or coordinate data.
pub trait Unzip: Iterator<Item = (Self::Left, Self::Right)> + Sized {
    /// The type of the left elements in the tuple
    type Left;
    /// The type of the right elements in the tuple
    type Right;

    /// Splits the iterator into two separate iterators.
    ///
    /// # Returns
    /// A tuple of two iterators. The first iterator yields the left elements `(A)` of the tuples,
    /// and the second iterator yields the right elements `(B)` of the tuples.
    #[allow(clippy::type_complexity)]
    fn unzip_iter(
        self,
    ) -> (
        UnzipIter<Self::Left, Self::Right, Self, Self::Left>,
        UnzipIter<Self::Left, Self::Right, Self, Self::Right>,
    );

    /// Splits the iterator into two thread-safe iterators.
    ///
    /// The [`unzip_iter_sync`](crate::Unzip::unzip_iter_sync) method allows you to create two separate thread-safe iterators
    /// from an iterator over tuples `(A, B)`. These iterators can be used in multi-threaded
    /// environments where concurrent access to the original data is required.
    ///
    /// # Returns
    /// A tuple of two thread-safe iterators:
    /// - The first iterator yields the left elements `(A)` of the tuples.
    /// - The second iterator yields the right elements `(B)` of the tuples.
    ///
    /// Each iterator internally uses an `Arc<Mutex<...>>` to ensure thread-safe access
    /// to the shared state.
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    /// use std::thread;
    ///
    /// let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
    /// let (left, right) = it.unzip_iter_sync();
    ///
    /// let left_thread = thread::spawn(move || left.collect::<Vec<_>>());
    /// let right_thread = thread::spawn(move || right.collect::<Vec<_>>());
    ///
    /// assert_eq!(left_thread.join().unwrap(), vec![1, 2, 3]);
    /// assert_eq!(right_thread.join().unwrap(), vec!["a", "b", "c"]);
    /// ```
    #[allow(clippy::type_complexity)]
    fn unzip_iter_sync(
        self,
    ) -> (
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Left>,
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Right>,
    );
}

impl<I, A, B> Unzip for I
where
    I: Iterator<Item = (A, B)>,
{
    type Left = A;
    type Right = B;

    fn unzip_iter(
        self,
    ) -> (
        UnzipIter<Self::Left, Self::Right, Self, Self::Left>,
        UnzipIter<Self::Left, Self::Right, Self, Self::Right>,
    ) {
        let rc = Rc::new(RefCell::new(UnzipInner::new(self)));

        (
            UnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::left_mut,
                    sel_ref: selector::left,
                },
                inner: Rc::clone(&rc),
            },
            UnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::right_mut,
                    sel_ref: selector::right,
                },
                inner: rc,
            },
        )
    }

    fn unzip_iter_sync(
        self,
    ) -> (
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Left>,
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Right>,
    ) {
        let rc = Arc::new(Mutex::new(UnzipInner::new(self)));

        (
            SyncUnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::left_mut,
                    sel_ref: selector::left,
                },
                inner: Arc::clone(&rc),
            },
            SyncUnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::right_mut,
                    sel_ref: selector::right,
                },
                inner: rc,
            },
        )
    }
}

#[derive(Clone, Debug)]
struct Buffer<A> {
    front: VecDeque<A>,
    back: VecDeque<A>,
}

impl<A> Buffer<A> {
    fn new() -> Self {
        Self {
            front: VecDeque::new(),
            back: VecDeque::new(),
        }
    }
}

/// Init
/// ```txt
/// [] iter.left  []
/// [] iter.right []
/// ```
///
/// Next.left // Consume left and store right
/// ```txt
/// [   ] iter.left  [] // Consume value
/// [ o ] iter.right [] // Store value
/// ```
///
/// Next.left
/// ```txt
/// [     ] iter.left  []
/// [ o o ] iter.right [] // Store value on the right
/// ```
///
/// Next.right // Consume right stores
/// ```txt
/// [   ] iter.left  []
/// [ o ] iter.right [] // Consume value on front
/// ```
///
/// NextBack.right // Consume right and store left
/// ```txt
/// [   ] iter.left  [ o ] // Store value
/// [ o ] iter.right [   ] // Consume value
/// ```
///
/// Test: [`how_unzip_inner_works`](crate::tests::unzip_inner_tests::how_unzip_inner_works)
#[derive(Clone, Debug)]
struct UnzipInner<A, B, I: Iterator<Item = (A, B)>> {
    iter: I,
    left: Buffer<A>,
    right: Buffer<B>,
}

impl<A, B, I: Iterator<Item = (A, B)>> UnzipInner<A, B, I> {
    fn new(iter: I) -> Self {
        Self {
            iter,
            left: Buffer::new(),
            right: Buffer::new(),
        }
    }

    /// Push value to front buffer.
    fn next(&mut self) -> Option<()> {
        let (a, b) = self.iter.next()?;

        self.left.front.push_back(a);
        self.right.front.push_back(b);

        Some(())
    }

    /// Get next value
    fn next_either<F, O>(&mut self, f: F) -> Option<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        let q = self.select_front_queue_mut(&f);

        q.pop_front() // Get value from front buffer
            .or_else(|| {
                // If empty
                self.next()?; // Push value to front buffer

                let q = self.select_front_queue_mut(&f);
                q.pop_front() // Get value from front buffer
            })
            .or_else(|| {
                // If Iterator is empty
                let q = self.select_back_queue_mut(&f);
                q.pop_front() // Get value from back buffer
            })
    }

    /// Select front buffer
    fn select_front_queue_mut<F, O>(&mut self, selector: F) -> &mut VecDeque<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        selector(&mut self.left.front, &mut self.right.front)
    }

    /// Select front buffer
    fn select_front_queue<F, O>(&self, selector: F) -> &VecDeque<O>
    where
        for<'a> F: Fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
    {
        selector(&self.left.front, &self.right.front)
    }

    /// Select back buffer
    fn select_back_queue_mut<F, O>(&mut self, selector: F) -> &mut VecDeque<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        selector(&mut self.left.back, &mut self.right.back)
    }

    /// Select back buffer
    fn select_back_queue<F, O>(&self, selector: F) -> &VecDeque<O>
    where
        for<'a> F: Fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
    {
        selector(&self.left.back, &self.right.back)
    }
}

impl<A, B, I: DoubleEndedIterator<Item = (A, B)>> UnzipInner<A, B, I> {
    fn next_back(&mut self) -> Option<()> {
        let (a, b) = self.iter.next_back()?;

        self.left.back.push_front(a);
        self.right.back.push_front(b);

        Some(())
    }

    fn next_back_either<F, O>(&mut self, f: F) -> Option<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        let q = self.select_back_queue_mut(&f);

        q.pop_back()
            .or_else(|| {
                self.next_back();

                let q = self.select_back_queue_mut(&f);
                q.pop_back()
            })
            .or_else(|| {
                let q = self.select_front_queue_mut(&f);
                q.pop_back()
            })
    }
}

impl<A, B, I: Iterator<Item = (A, B)> + ExactSizeIterator> UnzipInner<A, B, I> {
    fn len_either<F, O>(&self, f: F) -> usize
    where
        for<'a> F: Fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
    {
        self.select_front_queue(&f).len() + self.iter.len() + self.select_back_queue(&f).len()
    }
}

#[derive(Clone, Debug)]
struct Selector<A, B, O> {
    pub(crate) sel_mut: for<'a> fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    pub(crate) sel_ref: for<'a> fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
}

mod selector {
    use std::collections::VecDeque;

    pub(crate) fn left_mut<'a, A, B>(
        l: &'a mut VecDeque<A>,
        _r: &'a mut VecDeque<B>,
    ) -> &'a mut VecDeque<A> {
        l
    }

    pub(crate) fn right_mut<'a, A, B>(
        _l: &'a mut VecDeque<A>,
        r: &'a mut VecDeque<B>,
    ) -> &'a mut VecDeque<B> {
        r
    }

    pub(crate) fn left<'a, A, B>(l: &'a VecDeque<A>, _r: &'a VecDeque<B>) -> &'a VecDeque<A> {
        l
    }

    pub(crate) fn right<'a, A, B>(_l: &'a VecDeque<A>, r: &'a VecDeque<B>) -> &'a VecDeque<B> {
        r
    }
}

/// An iterator that yields one side of a tuple from the original iterator.
///
/// [`UnzipIter`] is produced by the [`unzip_iter`](crate::Unzip::unzip_iter) method of the [`Unzip`] trait. It is responsible for iterating over
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
#[derive(Clone)]
pub struct UnzipIter<A, B, I: Iterator<Item = (A, B)>, O> {
    queue_selector: Selector<A, B, O>,
    inner: Rc<RefCell<UnzipInner<A, B, I>>>,
}

impl<A, B, I, O> Iterator for UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .borrow_mut()
            .next_either(self.queue_selector.sel_mut)
    }
}

impl<A, B, I, O> DoubleEndedIterator for UnzipIter<A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .borrow_mut()
            .next_back_either(self.queue_selector.sel_mut)
    }
}

impl<A, B, I, O> ExactSizeIterator for UnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)> + ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.inner.borrow().len_either(self.queue_selector.sel_ref)
    }
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

/// A thread-safe iterator that yields one side of a tuple from the original iterator.
///
/// [`SyncUnzipIter`] is created by the [`unzip_iter_sync`](crate::Unzip::unzip_iter_sync) method of the [Unzip] trait.
/// It allows you to process either the left or the right elements of the tuples
/// from the original iterator in a thread-safe manner. This is achieved by wrapping
/// the shared internal state with [`Arc`] and [`Mutex`].
///
/// # Thread-Safety
/// The thread-safe design enables multiple threads to access and process the
/// elements concurrently without risking data races. Each iterator locks the
/// shared state only during access, ensuring synchronization while maintaining
/// efficient access to data.
///
/// # Example
/// ```
/// use unzip_iter::{Unzip, SyncUnzipIter};
/// use std::sync::{Arc, Mutex};
/// use std::thread;
///
/// let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
/// let (left, right) = it.unzip_iter_sync();
///
/// let left_thread = thread::spawn(move || left.collect::<Vec<_>>());
/// let right_thread = thread::spawn(move || right.collect::<Vec<_>>());
///
/// assert_eq!(left_thread.join().unwrap(), vec![1, 2, 3]);
/// assert_eq!(right_thread.join().unwrap(), vec!["a", "b", "c"]);
/// ```
#[derive(Clone)]
pub struct SyncUnzipIter<A, B, I: Iterator<Item = (A, B)>, O> {
    queue_selector: Selector<A, B, O>,
    inner: Arc<Mutex<UnzipInner<A, B, I>>>,
}

impl<A, B, I, O> Iterator for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    type Item = O;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .lock()
            .expect("Failed to Lock. Iterator paniced.")
            .next_either(self.queue_selector.sel_mut)
    }
}

impl<A, B, I, O> DoubleEndedIterator for SyncUnzipIter<A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .lock()
            .expect("Failed to Lock. Iterator paniced.")
            .next_back_either(self.queue_selector.sel_mut)
    }
}

impl<A, B, I, O> ExactSizeIterator for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)> + ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.inner
            .lock()
            .expect("Failed to Lock. Iterator paniced.")
            .len_either(self.queue_selector.sel_ref)
    }
}

impl<A, B, I, O> FusedIterator for SyncUnzipIter<A, B, I, O> where
    I: Iterator<Item = (A, B)> + FusedIterator
{
}

impl<A, B, I, O> Debug for SyncUnzipIter<A, B, I, O>
where
    A: Debug,
    B: Debug,
    I: Iterator<Item = (A, B)> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SyncUnzipIter {{ ... }}")
    }
}

/// A struct that converts an iterator of references to tuples `&(A, B)`
/// into an iterator of references to the individual elements `(&A, &B)`.
///
/// This struct is primarily created using the [`IntoRefPairs::ref_pairs`] method.
pub struct RefPairs<'a, A: 'a, B: 'a, I: Iterator<Item = &'a (A, B)>> {
    iter: I,
}

impl<'a, A: 'a, B: 'a, I: Iterator<Item = &'a (A, B)>> Iterator for RefPairs<'a, A, B, I> {
    type Item = (&'a A, &'a B);

    /// Advances the iterator and returns the next pair of references to the tuple's elements.
    ///
    /// # Returns
    ///
    /// - `Some((&A, &B))` if there is another tuple in the iterator.
    /// - `None` if the iterator is exhausted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use unzip_iter::IntoRefPairs;
    /// let pairs = vec![(1, 2), (3, 4)];
    /// let mut iter = pairs.iter().ref_pairs();
    ///
    /// assert_eq!(iter.next(), Some((&1, &2)));
    /// assert_eq!(iter.next(), Some((&3, &4)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(a, b)| (a, b))
    }
}

/// A trait that provides a method to convert an iterator of references to tuples `&(A, B)`
/// into an iterator of references to the individual elements `(&A, &B)`.
/// It is same as `.map(|(a, b)| (a, b))`.
/// You can use with [`Unzip`] as below.
/// ```
/// use unzip_iter::{Unzip, IntoRefPairs};
///
/// let it = [(1, 2), (3, 3), (5, 4)].iter().ref_pairs();
///
/// let (left, right) = it.unzip_iter();
///
/// assert!(left.eq([1, 3, 5].iter()));
/// assert!(right.eq([2, 3, 4].iter()));
/// ```
pub trait IntoRefPairs<'a, A: 'a, B: 'a, I: Iterator<Item = &'a (A, B)>> {
    /// Converts the iterator into a [`RefPairs`] iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use unzip_iter::IntoRefPairs;
    /// let pairs = vec![(1, 2), (3, 4)];
    /// let ref_pairs = pairs.iter().ref_pairs();
    ///
    /// for (a, b) in ref_pairs {
    ///     println!("a: {}, b: {}", a, b);
    /// }
    /// ```
    fn ref_pairs(self) -> RefPairs<'a, A, B, I>;
}

impl<'a, A: 'a, B: 'a, I: Iterator<Item = &'a (A, B)>> IntoRefPairs<'a, A, B, I> for I {
    /// See [`IntoRefPairs::ref_pairs`].
    fn ref_pairs(self) -> RefPairs<'a, A, B, I> {
        RefPairs { iter: self }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod unzip_iter_tests {
        use super::*;

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
    }

    mod sync_unzip_iter_tests {
        use super::*;
        use std::thread;

        #[test]
        fn test_basic() {
            let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
            let inner = Arc::new(Mutex::new(UnzipInner::new(it)));

            let left_iter = SyncUnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::left_mut,
                    sel_ref: selector::left,
                },
                inner: Arc::clone(&inner),
            };

            let right_iter = SyncUnzipIter {
                queue_selector: Selector {
                    sel_mut: selector::right_mut,
                    sel_ref: selector::right,
                },
                inner,
            };

            let left_thread = thread::spawn(move || left_iter.collect::<Vec<_>>());
            let right_thread = thread::spawn(move || right_iter.collect::<Vec<_>>());

            assert_eq!(left_thread.join().unwrap(), vec![1, 3, 5]);
            assert_eq!(right_thread.join().unwrap(), vec![2, 3, 4]);
        }

        #[test]
        fn test_complex() {
            let it = vec![
                (String::from("hello"), 1),
                (String::from("world"), 2),
                (String::from("rust"), 3),
            ]
            .into_iter();

            let (left, right) = it.unzip_iter_sync();

            let left_thread =
                thread::spawn(move || left.map(|s| s.to_uppercase()).collect::<Vec<_>>());
            let right_thread = thread::spawn(move || right.map(|n| n * 2).collect::<Vec<_>>());

            assert_eq!(left_thread.join().unwrap(), vec!["HELLO", "WORLD", "RUST"]);
            assert_eq!(right_thread.join().unwrap(), vec![2, 4, 6]);
        }

        #[test]
        fn test_thread_panic() {
            let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
            let (left, mut right) = it.unzip_iter_sync();

            thread::spawn(move || {
                let mut moved = left;
                assert_eq!(moved.next(), Some(1));
                assert_eq!(moved.next(), Some(3));
                assert_eq!(moved.next(), Some(5));
                assert_eq!(moved.next(), None);
                panic!("Thread panic!");
            })
            .join()
            .unwrap_err();

            assert_eq!(right.next(), Some(2));
            assert_eq!(right.next(), Some(3));
            assert_eq!(right.next(), Some(4));
            assert_eq!(right.next(), None);
        }

        #[test]
        #[should_panic(expected = "Failed to Lock. Iterator paniced.")]
        fn test_panic_iter() {
            let it = (0..).map(|v| {
                assert!(v < 1);
                ((), ())
            });

            let (left, mut right) = it.unzip_iter_sync();
            let thread = thread::spawn(move || {
                let mut left = left;
                left.nth(1);
            });
            let _ = thread.join();
            right.next();
        }

        #[test]
        fn test_double_ended_iterator() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let (mut left, mut right) = it.unzip_iter_sync();

            assert_eq!(left.next(), Some(1));
            assert_eq!(right.next_back(), Some("c"));
            assert_eq!(left.next_back(), Some(3));
            assert_eq!(right.next(), Some("a"));
            assert_eq!(left.next(), Some(2));
            assert_eq!(right.next(), Some("b"));
            assert_eq!(left.next(), None);
            assert_eq!(right.next_back(), None);
        }

        #[test]
        fn test_concurrent_double_ended() {
            let it = (0..100).map(|i| (i, i.to_string())).collect::<Vec<_>>();
            let (left, right) = it.into_iter().unzip_iter_sync();

            let left_thread = thread::spawn(move || {
                let mut nums = Vec::new();
                let mut left = left;

                for _ in 0..25 {
                    if let Some(n) = left.next() {
                        nums.push(n);
                    }
                }

                for _ in 0..25 {
                    if let Some(n) = left.next_back() {
                        nums.push(n);
                    }
                }
                nums
            });

            let right_thread = thread::spawn(move || {
                let mut strs = Vec::new();
                let mut right = right;

                for _ in 0..25 {
                    if let Some(s) = right.next() {
                        strs.push(s);
                    }
                    if let Some(s) = right.next_back() {
                        strs.push(s);
                    }
                }
                strs
            });

            let left_result = left_thread.join().unwrap();
            let right_result = right_thread.join().unwrap();

            assert!(left_result[..25].iter().copied().eq(0..25));
            assert!(left_result[25..].iter().copied().eq((75..100).rev()));

            let right_nums: Vec<i32> = right_result.iter().map(|s| s.parse().unwrap()).collect();
            for &n in &right_nums {
                assert!((0..100).contains(&n));
            }
            assert_eq!(right_nums.len(), 50);
        }

        #[test]
        fn test_exact_size_iterator() {
            let it = vec![(1, 'a'), (2, 'b'), (3, 'c')].into_iter();
            let (mut left, mut right) = it.unzip_iter_sync();

            assert_eq!(left.len(), 3);
            assert_eq!(right.len(), 3);

            left.next();
            right.next_back();
            assert_eq!(left.len(), 2);
            assert_eq!(right.len(), 2);

            left.next();
            right.next();
            assert_eq!(left.len(), 1);
            assert_eq!(right.len(), 1);
        }
    }

    mod unzip_inner_tests {
        use super::*;

        /// Documentation test of [`UnzipInner`]
        #[test]
        fn how_unzip_inner_works() {
            let it = std::iter::repeat((0, 0));

            let left = selector::left_mut;
            let right = selector::right_mut;

            let mut iter = UnzipInner::new(it);

            iter.next_either(left);
            assert_eq!(iter.right.front, VecDeque::from([0]));

            iter.next_either(left);
            assert_eq!(iter.right.front, VecDeque::from([0, 0]));

            iter.next_either(right);
            assert_eq!(iter.right.front, VecDeque::from([0]));

            iter.next_back_either(right);
            assert_eq!(iter.left.back, VecDeque::from([0]));
            assert_eq!(iter.right.front, VecDeque::from([0]));
        }

        #[test]
        fn test_unzip_inner_basic() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let mut inner = UnzipInner::new(it);

            // next()で要素を取得
            assert!(inner.next().is_some());
            assert_eq!(inner.left.front.pop_front(), Some(1));
            assert_eq!(inner.right.front.pop_front(), Some("a"));

            // 両方のバッファが空になっていることを確認
            assert!(inner.left.front.is_empty());
            assert!(inner.right.front.is_empty());
        }

        #[test]
        fn test_unzip_inner_next_either() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let mut inner = UnzipInner::new(it);

            // 左側の要素を取得
            assert_eq!(inner.next_either(selector::left_mut), Some(1));
            // 右側のバッファには要素が残っているはず
            assert_eq!(inner.right.front.pop_front(), Some("a"));

            // 右側の要素を取得
            assert_eq!(inner.next_either(selector::right_mut), Some("b"));
            // 左側のバッファには要素が残っているはず
            assert_eq!(inner.left.front.pop_front(), Some(2));
        }

        #[test]
        fn test_unzip_inner_double_ended() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let mut inner = UnzipInner::new(it);

            // 後ろから要素を取得
            assert!(inner.next_back().is_some());
            assert_eq!(inner.left.back.pop_front(), Some(3));
            assert_eq!(inner.right.back.pop_front(), Some("c"));

            // 前から要素を取得
            assert!(inner.next().is_some());
            assert_eq!(inner.left.front.pop_front(), Some(1));
            assert_eq!(inner.right.front.pop_front(), Some("a"));

            // 残りの要素を確認
            assert!(inner.next().is_some());
            assert_eq!(inner.left.front.pop_front(), Some(2));
            assert_eq!(inner.right.front.pop_front(), Some("b"));
        }

        #[test]
        fn test_unzip_inner_buffer_management() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let mut inner = UnzipInner::new(it);

            // 前方バッファに要素を追加
            inner.next();
            inner.next();
            assert_eq!(inner.left.front.len(), 2);
            assert_eq!(inner.right.front.len(), 2);

            // 後方バッファに要素を追加
            inner.next_back();
            assert_eq!(inner.left.back.len(), 1);
            assert_eq!(inner.right.back.len(), 1);

            // バッファから要素を取得
            assert_eq!(inner.next_either(selector::left_mut), Some(1));
            assert_eq!(inner.next_either(selector::right_mut), Some("a"));
            assert_eq!(inner.next_back_either(selector::left_mut), Some(3));
            assert_eq!(inner.next_back_either(selector::right_mut), Some("c"));
        }

        #[test]
        fn test_unzip_inner_empty() {
            let it = Vec::<(i32, &str)>::new().into_iter();
            let mut inner = UnzipInner::new(it);

            assert!(inner.next().is_none());
            assert!(inner.next_back().is_none());
            assert!(inner.next_either(selector::left_mut).is_none());
            assert!(inner.next_either(selector::right_mut).is_none());
            assert!(inner.next_back_either(selector::left_mut).is_none());
            assert!(inner.next_back_either(selector::right_mut).is_none());
        }

        #[test]
        fn test_unzip_inner_exact_size() {
            let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
            let mut inner = UnzipInner::new(it);

            assert_eq!(inner.len_either(selector::left), 3);
            assert_eq!(inner.len_either(selector::right), 3);

            inner.next();
            assert_eq!(inner.len_either(selector::left), 3);

            inner.next_either(selector::left_mut);
            assert_eq!(inner.len_either(selector::left), 2);

            inner.next_back();
            assert_eq!(inner.len_either(selector::left), 2);

            inner.next_back_either(selector::left_mut);
            assert_eq!(inner.len_either(selector::left), 1);
        }
    }
}
