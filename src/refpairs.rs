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
    /// # use unzip_iter::refpairs::IntoRefPairs;
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
/// You can use with [`Unzip`](crate::Unzip) as below.
/// ```
/// use unzip_iter::{Unzip, refpairs::IntoRefPairs};
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
    /// # use unzip_iter::refpairs::IntoRefPairs;
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
