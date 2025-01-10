//! Unzip iterators
//! This module provides a trait `Unzip` that allows splitting an iterator over tuples into two separate iterators.
//!
//! The `Unzip` trait simplifies the process of working with iterators of tuples by providing a method `unzip_iter`. This method produces two independent iterators, each iterating over one side of the tuple. This can be especially useful when you need to process or collect the components of the tuples separately.
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
//! The module also provides `SyncUnzipIter` for thread-safe usage via `Arc` and `Mutex`.

use std::{
    cell::RefCell,
    collections::VecDeque,
    iter::FusedIterator,
    rc::Rc,
    sync::{Arc, Mutex},
};

/// A trait to split an iterator over tuples into two separate iterators.
///
/// The `Unzip` trait extends any iterator over tuples `(A, B)` by providing the `unzip_iter` method.
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
pub trait Unzip<A, B>: Iterator<Item = (A, B)> + Sized {
    /// Splits the iterator into two separate iterators.
    ///
    /// # Returns
    /// A tuple of two iterators. The first iterator yields the left elements `(A)` of the tuples,
    /// and the second iterator yields the right elements `(B)` of the tuples.
    #[allow(clippy::type_complexity)]
    fn unzip_iter(self) -> (UnzipIter<A, B, Self, A>, UnzipIter<A, B, Self, B>);

    /// Splits the iterator into two thread-safe iterators.
    ///
    /// The `unzip_iter_sync` method allows you to create two separate thread-safe iterators
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
    fn unzip_iter_sync(self) -> (SyncUnzipIter<A, B, Self, A>, SyncUnzipIter<A, B, Self, B>);
}

impl<A, B, I: Iterator<Item = (A, B)>> Unzip<A, B> for I {
    fn unzip_iter(self) -> (UnzipIter<A, B, Self, A>, UnzipIter<A, B, Self, B>) {
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

    fn unzip_iter_sync(self) -> (SyncUnzipIter<A, B, Self, A>, SyncUnzipIter<A, B, Self, B>) {
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
struct UnzipInner<A, B, I: Iterator<Item = (A, B)>> {
    iter: I,
    left: VecDeque<A>,
    right: VecDeque<B>,
}

impl<A, B, I: Iterator<Item = (A, B)>> UnzipInner<A, B, I> {
    fn new(iter: I) -> Self {
        Self {
            iter,
            left: VecDeque::new(),
            right: VecDeque::new(),
        }
    }

    fn next(&mut self) -> Option<()> {
        let (a, b) = self.iter.next()?;

        self.left.push_back(a);
        self.right.push_back(b);

        Some(())
    }

    fn next_either<F, O>(&mut self, f: F) -> Option<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        let q = self.select_queue_mut(&f);

        q.pop_front().or_else(|| {
            self.next();

            let q = self.select_queue_mut(&f);
            q.pop_front()
        })
    }

    fn select_queue_mut<F, O>(&mut self, selector: F) -> &mut VecDeque<O>
    where
        for<'a> F: Fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    {
        selector(&mut self.left, &mut self.right)
    }

    fn select_queue<F, O>(&self, selector: F) -> &VecDeque<O>
    where
        for<'a> F: Fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
    {
        selector(&self.left, &self.right)
    }
}

impl<A, B, I: Iterator<Item = (A, B)> + ExactSizeIterator> UnzipInner<A, B, I> {
    fn len_either<F, O>(&self, f: F) -> usize
    where
        for<'a> F: Fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
    {
        self.select_queue(f).len() + self.iter.len()
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
/// `UnzipIter` is produced by the `unzip_iter` method of the `Unzip` trait. It is responsible for iterating over
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
#[derive(Clone, Debug)]
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

/// A thread-safe iterator that yields one side of a tuple from the original iterator.
///
/// `SyncUnzipIter` is created by the `unzip_iter_sync` method of the `Unzip` trait.
/// It allows you to process either the left or the right elements of the tuples
/// from the original iterator in a thread-safe manner. This is achieved by wrapping
/// the shared internal state with `Arc` and `Mutex`.
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
#[derive(Clone, Debug)]
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
            .expect("Failed to Lock")
            .next_either(self.queue_selector.sel_mut)
    }
}

impl<A, B, I, O> ExactSizeIterator for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)> + ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.inner
            .lock()
            .expect("Failed to Lock")
            .len_either(self.queue_selector.sel_ref)
    }
}

impl<A, B, I, O> FusedIterator for SyncUnzipIter<A, B, I, O> where
    I: Iterator<Item = (A, B)> + FusedIterator
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unzip_iter_basic() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (left, right) = it.unzip_iter();

        assert!(left.eq(vec![1, 3, 5].into_iter()));
        assert!(right.eq(vec![2, 3, 4].into_iter()));
    }

    #[test]
    fn test_unzip_iter_empty() {
        let it = vec![].into_iter();
        let (left, right): (UnzipIter<_, _, _, i32>, UnzipIter<_, _, _, i32>) = it.unzip_iter();

        assert!(left.eq(vec![].into_iter()));
        assert!(right.eq(vec![].into_iter()));
    }

    #[test]
    fn test_sync_unzip_iter() {
        use std::thread;

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
}
