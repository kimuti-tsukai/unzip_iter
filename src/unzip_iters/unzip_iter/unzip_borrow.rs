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

impl<'a, A, B, I, O> UnzipBorrow<'a, A, B, I, O>
where
    I: Iterator<Item = (A, B)>,
{
    pub(super) fn new(
        selector: Selector<A, B, O>,
        borrow: RefMut<'a, UnzipInner<A, B, I>>,
    ) -> Self {
        Self { selector, borrow }
    }
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

#[cfg(test)]
mod tests {
    use crate::Unzip;

    #[test]
    fn test_continuous_next() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter();

        // 一度の借用で複数の要素を取得
        let mut borrow = left.borrow();
        assert_eq!(borrow.next(), Some(1));
        assert_eq!(borrow.next(), Some(2));
        assert_eq!(borrow.next(), Some(3));
        assert_eq!(borrow.next(), None);
    }

    #[test]
    fn test_double_ended_iterator() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (_, right) = it.unzip_iter();

        let mut borrow = right.borrow();
        assert_eq!(borrow.next(), Some("a"));
        assert_eq!(borrow.next_back(), Some("c"));
        assert_eq!(borrow.next(), Some("b"));
        assert_eq!(borrow.next(), None);
        assert_eq!(borrow.next_back(), None);
    }

    #[test]
    fn test_size_hint() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter();

        let mut borrow = left.borrow();
        assert_eq!(borrow.size_hint(), (3, Some(3)));

        borrow.next();
        assert_eq!(borrow.size_hint(), (2, Some(2)));

        borrow.next();
        assert_eq!(borrow.size_hint(), (1, Some(1)));

        borrow.next();
        assert_eq!(borrow.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_mixed_iteration() {
        let it = vec![(1, "a"), (2, "b"), (3, "c"), (4, "d")].into_iter();
        let (left, _) = it.unzip_iter();

        // 前方と後方からの混合イテレーション
        let mut borrow = left.borrow();
        assert_eq!(borrow.next(), Some(1));
        assert_eq!(borrow.next_back(), Some(4));
        assert_eq!(borrow.next(), Some(2));
        assert_eq!(borrow.next_back(), Some(3));
        assert_eq!(borrow.next(), None);
        assert_eq!(borrow.next_back(), None);
    }

    #[test]
    fn test_borrow_drop_behavior() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, right) = it.unzip_iter();

        // 左側の借用を取得して一部イテレート
        {
            let mut left_borrow = left.borrow();
            assert_eq!(left_borrow.next(), Some(1));
            assert_eq!(left_borrow.next(), Some(2));
            // ここでleft_borrowがドロップされる
        }

        // 右側の借用を取得して残りをイテレート
        let mut right_borrow = right.borrow();
        assert_eq!(right_borrow.next(), Some("a"));
        assert_eq!(right_borrow.next(), Some("b"));
        assert_eq!(right_borrow.next(), Some("c"));
    }

    #[test]
    #[should_panic(expected = "already borrowed")]
    fn test_double_borrow() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let (left, _) = it.unzip_iter();

        let _borrow1 = left.borrow();
        let _borrow2 = left.borrow(); // これはパニックを引き起こすはず
    }
}
