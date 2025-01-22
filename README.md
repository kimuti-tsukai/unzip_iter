# Unzip iterators
This module provides a trait `Unzip` that allows splitting an iterator over tuples into two separate iterators.

The `Unzip` trait simplifies the process of working with iterators of tuples by providing a method `unzip_iter`. This method produces two independent iterators, each iterating over one side of the tuple. This can be especially useful when you need to process or collect the components of the tuples separately.

# Example
```rs
use unzip_iter::Unzip;

let it = vec![(1, 2), (3, 3), (5, 4)].into_iter();
let (left, right) = it.unzip_iter();

assert!(left.eq(vec![1, 3, 5].into_iter()));
assert!(right.eq(vec![2, 3, 4].into_iter()));
```

The module also provides `SyncUnzipIter` for thread-safe usage via `Arc` and `Mutex`.