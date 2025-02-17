use std::ops::{Deref, DerefMut};

use super::{selector::Selector, unzip_inner::UnzipInner};

pub trait UnzipInitialize<A, B, I, O> {
    type Unzip;

    /// Create a new Unziped iterator from an UnzipInner
    fn unzip(inner: UnzipInner<A, B, I>) -> Self::Unzip;

    /// Create a new Unziped iterator from a Selector and an UnzipInner
    fn with_selector(selector: Selector<A, B, O>, inner: UnzipInner<A, B, I>) -> Self;

    fn clone(&self) -> Self
    where
        I: Iterator<Item = (A, B)>,
        UnzipInner<A, B, I>: Clone,
        Self: Sized + UnzipIterAPI<A, B, I, O>,
    {
        let inner = self.get_inner().clone();
        let selector = self.get_queue_selector();
        Self::with_selector(selector, inner)
    }
}

/// API for UnzipIter
pub trait UnzipIterAPI<A, B, I: Iterator<Item = (A, B)>, O> {
    /// Get UnzipInner
    fn get_inner(&self) -> impl Deref<Target = UnzipInner<A, B, I>>;

    /// Get UnzipInner as mutable
    fn get_inner_mut(&mut self) -> impl DerefMut<Target = UnzipInner<A, B, I>>;

    /// Get Selector
    fn get_queue_selector(&self) -> Selector<A, B, O>;

    /// Get next value
    fn next(&mut self) -> Option<O> {
        let selector = self.get_queue_selector();
        self.get_inner_mut().next_either(selector)
    }

    /// Get size hint
    fn size_hint(&self) -> (usize, Option<usize>) {
        let selector = self.get_queue_selector();
        self.get_inner().size_hint_either(selector)
    }

    /// Get next back value
    fn next_back(&mut self) -> Option<O>
    where
        I: DoubleEndedIterator<Item = (A, B)>,
    {
        let selector = self.get_queue_selector();
        self.get_inner_mut().next_back_either(selector)
    }
}
