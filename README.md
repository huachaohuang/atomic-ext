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
let x = AtomicArc::new(a);
let b = x.load(Ordering::Acquire);
let c = x.swap(Some(Arc::new(2)), Ordering::AcqRel);
```