use std::collections::VecDeque;

#[derive(Debug)]
pub struct Selector<A, B, O> {
    pub sel_mut: for<'a> fn(&'a mut VecDeque<A>, &'a mut VecDeque<B>) -> &'a mut VecDeque<O>,
    pub sel_ref: for<'a> fn(&'a VecDeque<A>, &'a VecDeque<B>) -> &'a VecDeque<O>,
}

impl<A, B, O> Clone for Selector<A, B, O> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A, B, O> Copy for Selector<A, B, O> {}

pub fn left_mut<'a, T, U>(l: &'a mut T, _r: &'a mut U) -> &'a mut T {
    l
}

pub fn right_mut<'a, T, U>(_l: &'a mut T, r: &'a mut U) -> &'a mut U {
    r
}

pub fn left<'a, T, U>(l: &'a T, _r: &'a U) -> &'a T {
    l
}

pub fn right<'a, T, U>(_l: &'a T, r: &'a U) -> &'a U {
    r
}
