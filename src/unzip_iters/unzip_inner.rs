use std::collections::VecDeque;

use super::selector::Selector;

#[derive(Clone, Debug)]
struct Buffer<A> {
    front: VecDeque<A>,
    back: VecDeque<A>,
}

impl<A> Buffer<A> {
    fn new() -> Self {
        Self {
            front: VecDeque::new(),
            back: VecDeque::new(),
        }
    }
}

/// Init
/// ```txt
/// [] iter.left  []
/// [] iter.right []
/// ```
///
/// Next.left // Consume left and store right
/// ```txt
/// [   ] iter.left  [] // Consume value
/// [ o ] iter.right [] // Store value
/// ```
///
/// Next.left
/// ```txt
/// [     ] iter.left  []
/// [ o o ] iter.right [] // Store value on the right
/// ```
///
/// Next.right // Consume right stores
/// ```txt
/// [   ] iter.left  []
/// [ o ] iter.right [] // Consume value on front
/// ```
///
/// NextBack.right // Consume right and store left
/// ```txt
/// [   ] iter.left  [ o ] // Store value
/// [ o ] iter.right [   ] // Consume value
/// ```
///
/// Test: `how_unzip_inner_works`
#[derive(Clone, Debug)]
pub struct UnzipInner<A, B, I> {
    iter: I,
    left: Buffer<A>,
    right: Buffer<B>,
}

impl<A, B, I: Iterator<Item = (A, B)>> UnzipInner<A, B, I> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            left: Buffer::new(),
            right: Buffer::new(),
        }
    }

    /// Push value to front buffer.
    pub fn next(&mut self) -> Option<()> {
        let (a, b) = self.iter.next()?;

        self.left.front.push_back(a);
        self.right.front.push_back(b);

        Some(())
    }

    /// Get next value
    pub fn next_either<O>(&mut self, f: Selector<A, B, O>) -> Option<O> {
        let q = self.select_front_queue_mut(f);

        q.pop_front() // Get value from front buffer
            .or_else(|| {
                // If empty
                self.next()?; // Push value to front buffer

                let q = self.select_front_queue_mut(f);
                q.pop_front() // Get value from front buffer
            })
            .or_else(|| {
                // If Iterator is empty
                let q = self.select_back_queue_mut(f);
                q.pop_front() // Get value from back buffer
            })
    }

    /// Select front buffer
    pub fn select_front_queue_mut<O>(&mut self, selector: Selector<A, B, O>) -> &mut VecDeque<O> {
        (selector.sel_mut)(&mut self.left.front, &mut self.right.front)
    }

    /// Select front buffer
    pub fn select_front_queue<O>(&self, selector: Selector<A, B, O>) -> &VecDeque<O> {
        (selector.sel_ref)(&self.left.front, &self.right.front)
    }

    /// Select back buffer
    pub fn select_back_queue_mut<O>(&mut self, selector: Selector<A, B, O>) -> &mut VecDeque<O> {
        (selector.sel_mut)(&mut self.left.back, &mut self.right.back)
    }

    /// Select back buffer
    pub fn select_back_queue<O>(&self, selector: Selector<A, B, O>) -> &VecDeque<O> {
        (selector.sel_ref)(&self.left.back, &self.right.back)
    }

    pub fn size_hint_either<O>(&self, f: Selector<A, B, O>) -> (usize, Option<usize>)
    {
        let (min, max) = self.iter.size_hint();

        let buffer_len = self.select_front_queue(f).len() + self.select_back_queue(f).len();
        let min = min + buffer_len;
        let max = max.map(|max| max + buffer_len);

        (min, max)
    }
}

impl<A, B, I: DoubleEndedIterator<Item = (A, B)>> UnzipInner<A, B, I> {
    pub fn next_back(&mut self) -> Option<()> {
        let (a, b) = self.iter.next_back()?;

        self.left.back.push_front(a);
        self.right.back.push_front(b);

        Some(())
    }

    pub fn next_back_either<O>(&mut self, f: Selector<A, B, O>) -> Option<O>
    {
        let q = self.select_back_queue_mut(f);

        q.pop_back()
            .or_else(|| {
                self.next_back();

                let q = self.select_back_queue_mut(f);
                q.pop_back()
            })
            .or_else(|| {
                let q = self.select_front_queue_mut(f);
                q.pop_back()
            })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use crate::unzip_iters::{selector, UnzipInner};

    /// Documentation test of [`UnzipInner`]
    #[test]
    fn how_unzip_inner_works() {
        let left = selector::left();
        let right = selector::right();

        let it = std::iter::repeat((0, 0));

        let mut iter = UnzipInner::new(it);

        iter.next_either(left);
        assert_eq!(iter.right.front, VecDeque::from([0]));

        iter.next_either(left);
        assert_eq!(iter.right.front, VecDeque::from([0, 0]));

        iter.next_either(right);
        assert_eq!(iter.right.front, VecDeque::from([0]));

        iter.next_back_either(right);
        assert_eq!(iter.left.back, VecDeque::from([0]));
        assert_eq!(iter.right.front, VecDeque::from([0]));
    }

    #[test]
    fn test_unzip_inner_basic() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let mut inner = UnzipInner::new(it);

        // next()で要素を取得
        assert!(inner.next().is_some());
        assert_eq!(inner.left.front.pop_front(), Some(1));
        assert_eq!(inner.right.front.pop_front(), Some("a"));

        // 両方のバッファが空になっていることを確認
        assert!(inner.left.front.is_empty());
        assert!(inner.right.front.is_empty());
    }

    #[test]
    fn test_unzip_inner_next_either() {
        let left = selector::left();
        let right = selector::right();

        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let mut inner = UnzipInner::new(it);

        // 左側の要素を取得
        assert_eq!(inner.next_either(left), Some(1));
        // 右側のバッファには要素が残っているはず
        assert_eq!(inner.right.front.pop_front(), Some("a"));

        // 右側の要素を取得
        assert_eq!(inner.next_either(right), Some("b"));
        // 左側のバッファには要素が残っているはず
        assert_eq!(inner.left.front.pop_front(), Some(2));
    }

    #[test]
    fn test_unzip_inner_double_ended() {
        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let mut inner = UnzipInner::new(it);

        // 後ろから要素を取得
        assert!(inner.next_back().is_some());
        assert_eq!(inner.left.back.pop_front(), Some(3));
        assert_eq!(inner.right.back.pop_front(), Some("c"));

        // 前から要素を取得
        assert!(inner.next().is_some());
        assert_eq!(inner.left.front.pop_front(), Some(1));
        assert_eq!(inner.right.front.pop_front(), Some("a"));

        // 残りの要素を確認
        assert!(inner.next().is_some());
        assert_eq!(inner.left.front.pop_front(), Some(2));
        assert_eq!(inner.right.front.pop_front(), Some("b"));
    }

    #[test]
    fn test_unzip_inner_buffer_management() {
        let left = selector::left();
        let right = selector::right();

        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let mut inner = UnzipInner::new(it);

        // 前方バッファに要素を追加
        inner.next();
        inner.next();
        assert_eq!(inner.left.front.len(), 2);
        assert_eq!(inner.right.front.len(), 2);

        // 後方バッファに要素を追加
        inner.next_back();
        assert_eq!(inner.left.back.len(), 1);
        assert_eq!(inner.right.back.len(), 1);

        // バッファから要素を取得
        assert_eq!(inner.next_either(left), Some(1));
        assert_eq!(inner.next_either(right), Some("a"));
        assert_eq!(inner.next_back_either(left), Some(3));
        assert_eq!(inner.next_back_either(right), Some("c"));
    }

    #[test]
    fn test_unzip_inner_empty() {
        let left = selector::left();
        let right = selector::right();

        let it = Vec::<(i32, &str)>::new().into_iter();
        let mut inner = UnzipInner::new(it);

        assert!(inner.next().is_none());
        assert!(inner.next_back().is_none());
        assert!(inner.next_either(left).is_none());
        assert!(inner.next_either(right).is_none());
        assert!(inner.next_back_either(left).is_none());
        assert!(inner.next_back_either(right).is_none());
    }

    #[test]
    fn test_unzip_inner_exact_size() {
        let left = selector::left();
        let right = selector::right();

        let it = vec![(1, "a"), (2, "b"), (3, "c")].into_iter();
        let mut inner = UnzipInner::new(it);

        assert_eq!(inner.size_hint_either(left), (3, Some(3)));
        assert_eq!(inner.size_hint_either(right), (3, Some(3)));

        inner.next();
        assert_eq!(inner.size_hint_either(left), (3, Some(3)));

        inner.next_either(left);
        assert_eq!(inner.size_hint_either(left), (2, Some(2)));

        inner.next_back();
        assert_eq!(inner.size_hint_either(left), (2, Some(2)));

        inner.next_back_either(left);
        assert_eq!(inner.size_hint_either(left), (1, Some(1)));
    }
}
