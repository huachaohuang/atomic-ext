# Atomic extensions

[![docs](https://docs.rs/atomic-ext/badge.svg)](https://docs.rs/arc-ext)

## [AtomicArc](https://docs.rs/atomic-ext/latest/atomic_ext/struct.AtomicArc.html): A lightweight atomic pointer to `Arc`.

Example

```rust
use std::sync::{atomic::Ordering, Arc},

use atomic_ext::AtomicArc;

let a = Arc::new(1);
let x = AtomicArc::new(a);
let b = x.load(Ordering::Acquire);
let c = x.swap(Some(Arc::new(2)), Ordering::AcqRel);
```