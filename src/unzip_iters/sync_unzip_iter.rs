use std::{
    fmt::Debug,
    iter::FusedIterator,
    sync::{Arc, Mutex},
};

use sync_unzip_lock::SyncUnzipLock;

use super::{
    selector::Selector,
    unzip_api::{UnzipInitialize, UnzipIterAPI},
    unzip_inner::UnzipInner,
};

use errors::*;

pub mod sync_unzip_lock;

pub mod errors {
    use std::{error::Error, fmt::Display};

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum TryLockError {
        WouldBlock,
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
}
/// A thread-safe iterator that yields one side of a tuple from the original iterator.
///
/// [`SyncUnzipIter`] is created by the [`unzip_iter_sync`](crate::Unzip::unzip_iter_sync) method of the [`Unzip`](crate::Unzip) trait.
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
/// use unzip_iter::Unzip;
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
pub struct SyncUnzipIter<A, B, I, O> {
    queue_selector: Selector<A, B, O>,
    inner: Arc<Mutex<UnzipInner<A, B, I>>>,
}

impl<A, B, I, O> Clone for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)> + Clone,
    A: Clone,
    B: Clone,
{
    fn clone(&self) -> Self {
        UnzipIterAPI::clone(self)
    }
}

impl<A, B, I, O> SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    pub(crate) fn new(
        queue_selector: Selector<A, B, O>,
        arc: Arc<Mutex<UnzipInner<A, B, I>>>,
    ) -> Self {
        Self {
            queue_selector,
            inner: arc,
        }
    }

    /// Acquires a lock on the internal state of the iterator, returning a guard that provides
    /// optimized access to the iterator's elements.
    ///
    /// This method returns a [`SyncUnzipLock`] that maintains the lock for multiple
    /// operations, which can significantly improve performance when multiple consecutive
    /// iterations are needed.
    ///
    /// # Errors
    /// Returns a [`LockError`] if another thread holding the lock panicked.
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    ///
    /// let it = vec![(1, "a"), (2, "b")].into_iter();
    /// let (numbers, _) = it.unzip_iter_sync();
    ///
    /// let mut lock = numbers.lock().unwrap();
    /// assert_eq!(lock.next(), Some(1));
    /// assert_eq!(lock.next(), Some(2));
    /// ```
    pub fn lock(&self) -> Result<SyncUnzipLock<'_, A, B, I, O>, LockError> {
        self.inner
            .lock()
            .map(|locked| SyncUnzipLock::new(self.queue_selector, locked))
            .map_err(|_| LockError)
    }

    /// Attempts to acquire a lock on the internal state of the iterator, returning a guard
    /// that provides optimized access to the iterator's elements.
    ///
    /// Similar to [`lock`](Self::lock), but returns immediately with an error if the lock
    /// cannot be acquired instead of blocking.
    ///
    /// # Returns
    /// - `Ok(SyncUnzipLock)` if the lock was successfully acquired
    /// - `Err(TryLockError::WouldBlock)` if the lock is held by another thread
    /// - `Err(TryLockError::Paniced)` if another thread holding the lock panicked
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    ///
    /// let it = vec![(1, "a"), (2, "b")].into_iter();
    /// let (numbers, _) = it.unzip_iter_sync();
    ///
    /// let lock1 = numbers.try_lock().unwrap();
    /// assert!(numbers.try_lock().is_err()); // Second lock attempt fails
    /// ```
    pub fn try_lock(&self) -> Result<SyncUnzipLock<'_, A, B, I, O>, TryLockError> {
        self.inner
            .try_lock()
            .map(|locked| SyncUnzipLock::new(self.queue_selector, locked))
            .map_err(|e| match e {
                std::sync::TryLockError::WouldBlock => TryLockError::WouldBlock,
                std::sync::TryLockError::Poisoned(_) => TryLockError::Paniced,
            })
    }

    /// Returns `true` if the internal state is poisoned.
    ///
    /// The internal state becomes poisoned when a thread holding the lock panics.
    /// This method can be used to check if it's safe to acquire the lock.
    ///
    /// # Example
    /// ```
    /// use unzip_iter::Unzip;
    /// use std::thread;
    ///
    /// let it = vec![(1, "a"), (2, "b")].into_iter();
    /// let (numbers, _) = it.unzip_iter_sync();
    ///
    /// assert!(!numbers.is_paniced());
    /// ```
    pub fn is_paniced(&self) -> bool {
        self.inner.is_poisoned()
    }
}

impl<A, B, I, O> UnzipInitialize<A, B, I, O> for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    type Unzip = (SyncUnzipIter<A, B, I, A>, SyncUnzipIter<A, B, I, B>);

    fn unzip(inner: UnzipInner<A, B, I>) -> Self::Unzip {
        let arc = Arc::new(Mutex::new(inner));
        let left = SyncUnzipIter::new(Selector::<A, B, O>::LEFT, arc.clone());
        let right = SyncUnzipIter::new(Selector::<A, B, O>::RIGHT, arc.clone());
        (left, right)
    }

    fn with_selector(selector: Selector<A, B, O>, inner: UnzipInner<A, B, I>) -> Self {
        Self::new(selector, Arc::new(Mutex::new(inner)))
    }
}

impl<A, B, I, O> UnzipIterAPI<A, B, I, O> for SyncUnzipIter<A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    fn get_inner(&self) -> impl std::ops::Deref<Target = UnzipInner<A, B, I>> {
        self.inner
            .lock()
            .expect("Failed to Lock. Iterator paniced.")
    }

    fn get_inner_mut(&mut self) -> impl std::ops::DerefMut<Target = UnzipInner<A, B, I>> {
        self.inner
            .lock()
            .expect("Failed to Lock. Iterator paniced.")
    }

    fn get_queue_selector(&self) -> Selector<A, B, O> {
        self.queue_selector
    }
}

impl<A, B, I, O> Iterator for SyncUnzipIter<A, B, I, O>
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

impl<A, B, I, O> DoubleEndedIterator for SyncUnzipIter<A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next_back(self)
    }
}

impl<A, B, I, O> ExactSizeIterator for SyncUnzipIter<A, B, I, O> where
    I: Iterator<Item = (A, B)> + ExactSizeIterator
{
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

#[cfg(test)]
mod tests {

    use crate::unzip_iters::{selector::Selector, SyncUnzipIter, Unzip, UnzipInner};
    use std::{
        sync::{Arc, Mutex},
        thread,
    };

    #[test]
    fn test_basic() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let inner = Arc::new(Mutex::new(UnzipInner::new(it)));

        let left_iter = SyncUnzipIter {
            queue_selector: Selector::<i32, i32, i32>::LEFT,
            inner: Arc::clone(&inner),
        };

        let right_iter = SyncUnzipIter {
            queue_selector: Selector::<i32, i32, i32>::RIGHT,
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

        let left_thread = thread::spawn(move || left.map(|s| s.to_uppercase()).collect::<Vec<_>>());
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

    #[test]
    fn test_clone() {
        let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
        let (left, right) = it.unzip_iter_sync();
        let left_clone = left.clone();

        assert!(left.eq(vec![1, 3, 5].into_iter()));
        assert!(left_clone.eq(vec![1, 3, 5].into_iter()));
        assert!(right.eq(vec![2, 3, 4].into_iter()));
    }
}
