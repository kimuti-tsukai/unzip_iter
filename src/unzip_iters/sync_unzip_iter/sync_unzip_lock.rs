use std::{ops::{Deref, DerefMut}, sync::MutexGuard};

use crate::unzip_iters::{selector::Selector, unzip_api::UnzipIterAPI, unzip_inner::UnzipInner};

pub struct SyncUnzipLock<'a, A, B, I: Iterator<Item = (A, B)>, O> {
    selector: Selector<A, B, O>,
    lock: MutexGuard<'a, UnzipInner<A, B, I>>,
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