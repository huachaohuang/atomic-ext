use std::{
    alloc::Layout,
    cmp::max,
    marker::PhantomData,
    ptr::NonNull,
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering},
        Arc,
    },
};

/// A lightweight atomic pointer to [`Arc`].
///
/// **Note**: The imlementation manipuates the internal reference count of the
/// original [`Arc`] for optimization. This means that the result of
/// [`Arc::strong_count`] is incorrect, until the [`Arc`] gets rid of
/// this pointer's control (with [`AtomicArc::swap`]). Users who depend on the
/// correctness of [`Arc::strong_count`] should be careful.
///
/// # Limitations
///
/// The implementation borrows some bits from the `Arc` pointer as an external
/// reference count (a technique called "split reference counting"). It
/// will panic in some extreame scenario when the reference count is increased
/// more than a threshold (2^15) at the same time. This is almost impossible
/// unless someone creates more than 2^15 threads to load the same pointer at
/// the same time.
///
/// # Examples
///
/// ```
/// use std::{
///     sync::{atomic::Ordering, Arc},
///     thread,
/// };
///
/// use atomic_ext::AtomicArc;
///
/// let a = Arc::new(1);
/// let b = Arc::new(2);
/// let x = Arc::new(AtomicArc::new(a));
/// {
///     let x = x.clone();
///     thread::spawn(move || {
///         x.swap(b, Ordering::AcqRel) // Returns `a`
///     });
/// }
/// {
///     let x = x.clone();
///     thread::spawn(move || {
///         x.load(Ordering::Acquire) // Returns either `a` or `b`
///     });
/// };
/// ```
pub struct AtomicArc<T> {
    state: AtomicU64,
    phantom: PhantomData<*mut Arc<T>>,
}

impl<T> AtomicArc<T> {
    /// Constructs a new [`AtomicArc`].
    pub fn new(value: Arc<T>) -> Self {
        let state = new_state(value);
        Self {
            state: AtomicU64::new(state),
            phantom: PhantomData,
        }
    }

    /// Loads an [`Arc`] from the pointer.
    ///
    /// The fast path uses just one atomic operation to load the [`Arc`] and
    /// increase its reference count.
    pub fn load(&self, order: Ordering) -> Arc<T> {
        let state = self.state.fetch_add(1, order);
        let (addr, count) = unpack_state(state);
        if count >= RESERVED_COUNT {
            panic!("external reference count overflow");
        }
        if count >= RESERVED_COUNT / 2 {
            self.push_count(addr);
        }
        unsafe { Arc::from_raw(addr as _) }
    }

    /// Stores an [`Arc`] into the pointer, returning the previous [`Arc`].
    pub fn swap(&self, value: Arc<T>, order: Ordering) -> Arc<T> {
        let state = self.state.swap(new_state(value), order);
        let (addr, count) = unpack_state(state);
        unsafe {
            decrease_count::<T>(addr, RESERVED_COUNT - count);
            Arc::from_raw(addr as _)
        }
    }

    /// Pushes the external reference count back to the original [`Arc`].
    fn push_count(&self, expect_addr: usize) {
        let mut state = self.state.load(Ordering::Acquire);
        let new_state = pack_state(expect_addr);
        loop {
            let (addr, count) = unpack_state(state);
            if addr != expect_addr || count < RESERVED_COUNT / 2 {
                // Someone else has changed the address or the reference count.
                break;
            }
            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => unsafe {
                    increase_count::<T>(addr, count);
                },
                Err(actual) => state = actual,
            }
        }
    }
}

unsafe impl<T> Sync for AtomicArc<T> {}
unsafe impl<T> Send for AtomicArc<T> {}

const RESERVED_COUNT: usize = 0x8000;

fn new_state<T>(value: Arc<T>) -> u64 {
    let addr = Arc::into_raw(value) as usize;
    unsafe {
        increase_count::<T>(addr, RESERVED_COUNT);
        pack_state(addr)
    }
}

fn pack_state(addr: usize) -> u64 {
    let addr = addr as u64;
    assert_eq!(addr >> 48, 0);
    addr << 16
}

fn unpack_state(state: u64) -> (usize, usize) {
    ((state >> 16) as usize, (state & 0xFFFF) as usize)
}

/// Constructs the same layout with [`std::sync::Arc`] so that we can manipulate
/// the internal reference count.
#[repr(C)]
struct ArcInner {
    count: AtomicUsize,
    weak_count: AtomicUsize,
}

unsafe fn inner_ptr<T>(addr: usize) -> NonNull<ArcInner> {
    let align = align_of::<T>();
    let layout = Layout::new::<ArcInner>();
    let offset = max(layout.size(), align);
    NonNull::new_unchecked((addr - offset) as _)
}

unsafe fn increase_count<T>(addr: usize, count: usize) {
    let ptr = inner_ptr::<T>(addr);
    ptr.as_ref().count.fetch_add(count, Ordering::Release);
}

unsafe fn decrease_count<T>(addr: usize, count: usize) {
    let ptr = inner_ptr::<T>(addr);
    ptr.as_ref().count.fetch_sub(count, Ordering::Release);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let x = AtomicArc::new(Arc::new(1234));
        let a = x.load(Ordering::Acquire);
        assert_eq!(*a, 1234);
        assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 1);
        let b = x.swap(Arc::new(5678), Ordering::AcqRel);
        assert_eq!(Arc::strong_count(&a), 2);
        assert_eq!(Arc::strong_count(&b), 2);
        let c = x.load(Ordering::Acquire);
        assert_eq!(*c, 5678);
        assert_eq!(Arc::strong_count(&c), RESERVED_COUNT + 1);
    }

    #[test]
    fn push_count() {
        let x = AtomicArc::new(Arc::new(1));
        let mut v = Vec::new();
        for _ in 0..(RESERVED_COUNT / 2) {
            let a = x.load(Ordering::Relaxed);
            assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 1);
            v.push(a);
        }
        // This load will push the external count back to the `Arc`.
        let a = x.load(Ordering::Relaxed);
        assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + v.len() + 2);
        let b = x.swap(Arc::new(2), Ordering::Relaxed);
        assert_eq!(Arc::strong_count(&b), v.len() + 2);
    }
}
