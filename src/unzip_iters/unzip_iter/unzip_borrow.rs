use std::cell::RefMut;

use crate::unzip_iters::{unzip_inner::UnzipInner, unzip_lock::UnzipLock};

/// A guard that holds a borrow on the internal state of a [`UnzipIter`](super::UnzipIter).
///
/// This type provides optimized access to the iterator's elements by maintaining
/// the borrow for multiple operations. This is particularly useful when you need to
/// perform multiple consecutive iterations.
///
/// # Performance
/// Using `UnzipBorrow` can significantly improve performance when multiple
/// consecutive operations are needed, as it avoids the overhead of borrowing
/// and releasing for each operation.
///
/// # Borrow Safety
/// The borrow is automatically released when the `UnzipBorrow` is dropped.
/// To avoid panics, ensure that you don't hold multiple borrows simultaneously
/// and drop the borrow when it's no longer needed.
///
/// # Example
/// ```
/// use unzip_iter::Unzip;
///
/// let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
/// let (left, _) = it.unzip_iter();
///
/// // The borrow is automatically released at the end of this block
/// {
///     let mut borrow = left.borrow();
///     assert_eq!(borrow.next(), Some(1));
///     assert_eq!(borrow.next(), Some(2));
///     assert_eq!(borrow.next(), Some(3));
/// } // borrow is dropped here
/// ```
pub type UnzipBorrow<'a, A, B, I, O> = UnzipLock<RefMut<'a, UnzipInner<A, B, I>>, A, B, O>;

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
