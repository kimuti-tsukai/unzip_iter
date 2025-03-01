pub use sync_unzip_iter::SyncUnzipIter;
use unzip_api::UnzipInitialize;
use unzip_inner::UnzipInner;
pub use unzip_iter::UnzipIter;

pub mod unzip_iter;

pub mod sync_unzip_iter;

mod unzip_inner;

mod unzip_api;

mod unzip_lock;

mod selector;

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
        let inner = UnzipInner::new(self);

        <UnzipIter<Self::Left, Self::Right, Self, Self::Left> as UnzipInitialize<_, _, _, _>>::unzip(
            inner,
        )
    }

    fn unzip_iter_sync(
        self,
    ) -> (
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Left>,
        SyncUnzipIter<Self::Left, Self::Right, Self, Self::Right>,
    ) {
        let inner = UnzipInner::new(self);

        <SyncUnzipIter<Self::Left, Self::Right, Self, Self::Left> as UnzipInitialize<_, _, _, _>>::unzip(inner)
    }
}
