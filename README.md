# Atomic extensions

[![docs](https://docs.rs/atomic-ext/badge.svg)](https://docs.rs/arc-ext)

## AtomicArc

[AtomicArc](https://docs.rs/atomic-ext/latest/atomic_ext/struct.AtomicArc.html) is a lightweight atomic pointer to `Arc`.

The implementation is based on "split reference counting", which has similar performance with `Arc`.

### Example

```rust
use std::sync::{atomic::Ordering, Arc},

use atomic_ext::AtomicArc;

let a = Arc::new(1);
let b = Arc::new(2);
let x = AtomicArc::new(a);
let c = x.load(Ordering::Acquire);
assert_eq!(c, a);
let c = x.swap(b, Ordering::AcqRel);
assert_eq!(c, a);
let c = x.load(Ordering::Acquire);
assert_eq!(c, b);
```