use std::collections::VecDeque;

#[derive(Debug)]
pub struct Selector<A, B, O> {
    pub sel_mut: for<'a> fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    pub sel_ref: for<'a> fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
}

pub const fn left<A, B>() -> Selector<A, B, A> {
    Selector {
        sel_mut: |l, _| l,
        sel_ref: |l, _| l,
    }
}

pub const fn right<A, B>() -> Selector<A, B, B> {
    Selector {
        sel_mut: |_, r| r,
        sel_ref: |_, r| r,
    }
}

impl<A, B, O> Clone for Selector<A, B, O> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A, B, O> Copy for Selector<A, B, O> {}
