# Unzip iterators

This module provides a trait [`Unzip`] that allows splitting an iterator over tuples into two separate iterators.

The [`Unzip`] trait simplifies the process of working with iterators of tuples by providing a method [`unzip_iter`](crate::Unzip::unzip_iter). This method produces two independent iterators, each iterating over one side of the tuple. This can be especially useful when you need to process or collect the components of the tuples separately.

# Example
```rust
use unzip_iter::Unzip;

let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
let (left, right) = it.unzip_iter();

assert!(left.eq(vec![1, 3, 5].into_iter()));
assert!(right.eq(vec![2, 3, 4].into_iter()));
```

If you want to splitting an iterator over tuples into more than two iterators, you can do as follows:
```rust
use unzip_iter::Unzip;

let it = vec![(1, 2, 3), (4, 5, 6), (7, 8, 9)].into_iter();

let tuple_iter = it.map(|(a, b, c)| (a, (b, c)));
let (left, right) = tuple_iter.unzip_iter();
let (middle, right) = right.unzip_iter();

assert!(left.eq(vec![1, 4, 7].into_iter()));
assert!(middle.eq(vec![2, 5, 8].into_iter()));
assert!(right.eq(vec![3, 6, 9].into_iter()));
```

The module also provides [`SyncUnzipIter`](crate::unzip_iters::sync_unzip_iter::SyncUnzipIter) for thread-safe usage via [`Arc`](std::sync::Arc) and [`Mutex`](std::sync::Mutex).

# Performance Considerations
When calling `next()` multiple times in succession, it's recommended to use `lock()` or `borrow()` methods
to avoid repeated locking/unlocking overhead. For example:
```rust
use unzip_iter::Unzip;

let it = vec![(1, 2), (3, 4)].into_iter();
let (left, right) = it.unzip_iter();

// More efficient way when calling next() multiple times
let mut left_guard = left.borrow(); // or lock() for SyncUnzipIter
let first = left_guard.next();
let second = left_guard.next();
drop(left_guard);
```