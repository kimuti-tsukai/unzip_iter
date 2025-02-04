use std::{
    cell::RefMut,
    fmt::Debug,
    iter::{ExactSizeIterator, FusedIterator},
    ops::{Deref, DerefMut},
};

use crate::unzip_iters::{selector::Selector, unzip_api::UnzipIterAPI, unzip_inner::UnzipInner};

pub struct UnzipBorrow<'a, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    selector: Selector<A, B, O>,
    borrow: RefMut<'a, UnzipInner<A, B, I>>,
}

impl<A, B, I, O> UnzipIterAPI<A, B, I, O> for UnzipBorrow<'_, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
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

impl<A, B, I, O> Iterator for UnzipBorrow<'_, A, B, I, O>
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

impl<A, B, I, O> DoubleEndedIterator for UnzipBorrow<'_, A, B, I, O>
where
    I: DoubleEndedIterator<Item = (A, B)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        UnzipIterAPI::next_back(self)
    }
}

impl<A, B, I, O> ExactSizeIterator for UnzipBorrow<'_, A, B, I, O> where
    I: ExactSizeIterator<Item = (A, B)>
{
}

impl<A, B, I, O> FusedIterator for UnzipBorrow<'_, A, B, I, O> where I: FusedIterator<Item = (A, B)> {}

impl<A, B, I, O> Debug for UnzipBorrow<'_, A, B, I, O>
where
    I: Iterator<Item = (A, B)> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "UnzipBorrow {{ ... }}")
    }
}
