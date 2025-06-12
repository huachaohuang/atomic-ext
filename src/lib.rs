use std::{
    alloc::Layout,
    marker::PhantomData,
    ptr,
    ptr::NonNull,
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering},
        Arc,
    },
};

/// A raw atomic pointer.
struct AtomicPtr<T> {
    state: AtomicU64,
    phantom: PhantomData<Arc<T>>,
}

impl<T> AtomicPtr<T> {
    /// Creates an [`AtomicPtr`].
    fn new(value: *const T) -> Self {
        let state = new_state(value);
        Self {
            state: AtomicU64::new(state),
            phantom: PhantomData,
        }
    }

    /// Loads an [`Arc`] pointer.
    fn load(&self, order: Ordering) -> *const T {
        let state = self.state.fetch_add(1, order);
        let (addr, count) = unpack_state(state);
        if count >= RESERVED_COUNT {
            panic!("external reference count overflow");
        }
        if count >= RESERVED_COUNT / 2 {
            self.push_count(addr);
        }
        addr as _
    }

    /// Stores an [`Arc`] pointer and returns the previous pointer.
    fn swap(&self, value: *const T, order: Ordering) -> *const T {
        let state = self.state.swap(new_state(value), order);
        let (addr, count) = unpack_state(state);
        unsafe {
            decrease_count::<T>(addr, RESERVED_COUNT - count);
            addr as _
        }
    }

    /// Stores an [`Arc`] pointer if the current value is the same as `current`.
    fn compare_exchange(
        &self,
        current: *const T,
        new: *const T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*const T, *const T> {
        let new_state = pack_state(new.addr());
        let mut state = self.state.load(failure);
        loop {
            let (addr, count) = unpack_state(state);
            if addr != current.addr() {
                unsafe {
                    increase_count::<T>(addr, 1);
                }
                return Err(addr as _);
            }
            match self
                .state
                .compare_exchange_weak(state, new_state, success, failure)
            {
                Ok(_) => {
                    unsafe {
                        decrease_count::<T>(addr, RESERVED_COUNT - count);
                        increase_count::<T>(new.addr(), RESERVED_COUNT + 1);
                    }
                    return Ok(addr as _);
                }
                Err(now_state) => state = now_state,
            }
        }
    }

    /// Pushes the external reference count back to the original [`Arc`].
    fn push_count(&self, expect_addr: usize) {
        let mut current = self.state.load(Ordering::Acquire);
        let desired = pack_state(expect_addr);
        loop {
            let (addr, count) = unpack_state(current);
            if addr != expect_addr || count < RESERVED_COUNT / 2 {
                // Someone else has changed the address or the reference count.
                break;
            }
            match self.state.compare_exchange_weak(
                current,
                desired,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => unsafe {
                    increase_count::<T>(addr, count);
                },
                Err(actual) => current = actual,
            }
        }
    }
}

impl<T> Drop for AtomicPtr<T> {
    fn drop(&mut self) {
        let state = self.state.load(Ordering::Acquire);
        let (addr, count) = unpack_state(state);
        unsafe {
            // +1 to drop the reference this pionter holds when it is created.
            decrease_count::<T>(addr, RESERVED_COUNT + 1 - count);
        }
    }
}

impl<T> Default for AtomicPtr<T> {
    fn default() -> Self {
        Self {
            state: AtomicU64::new(0),
            phantom: PhantomData,
        }
    }
}

/// An atomic pointer for [`Arc`].
///
/// **Note**: The implementation manipulates the internal reference count of the
/// original [`Arc`] for optimization. This means that the result of
/// [`Arc::strong_count`] is incorrect, until the [`Arc`] gets rid of
/// this pointer's control (with [`AtomicArc::swap`]). Users who depend on the
/// correctness of [`Arc::strong_count`] should be careful.
///
/// # Limitations
///
/// The implementation borrows some bits from the `Arc` pointer as an external
/// reference count (a technique called "split reference counting"). It
/// will panic in some extreme scenario when the reference count is increased
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
pub struct AtomicArc<T>(AtomicPtr<T>);

impl<T> AtomicArc<T> {
    /// Creates a [`AtomicArc`] with the value.
    pub fn new(value: Arc<T>) -> Self {
        Self(AtomicPtr::new(Arc::into_raw(value)))
    }

    /// Loads an [`Arc`] from the pointer.
    ///
    /// The fast path uses just one atomic operation to load the [`Arc`] and
    /// increase its reference count.
    pub fn load(&self, order: Ordering) -> Arc<T> {
        let ptr = self.0.load(order);
        unsafe { Arc::from_raw(ptr) }
    }

    /// Stores an [`Arc`] into the pointer, returning the previous value.
    pub fn swap(&self, value: Arc<T>, order: Ordering) -> Arc<T> {
        let new = Arc::into_raw(value);
        let current = self.0.swap(new, order);
        unsafe { Arc::from_raw(current) }
    }

    /// Stores an [`Arc`] into the pointer if the current value is the same as
    /// `current`.
    pub fn compare_exchange(
        &self,
        current: &Arc<T>,
        new: &Arc<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Arc<T>, Arc<T>> {
        let new = Arc::as_ptr(new);
        let current = Arc::as_ptr(current);
        self.0
            .compare_exchange(current, new, success, failure)
            .map(|ptr| unsafe { Arc::from_raw(ptr) })
            .map_err(|ptr| unsafe { Arc::from_raw(ptr) })
    }
}

/// An atomic pointer for [`Option<Arc>`].
///
/// This is similar to [`AtomicArc`], but allows null values.
pub struct AtomicOptionArc<T>(AtomicPtr<T>);

impl<T> AtomicOptionArc<T> {
    /// Creates a [`AtomicOptionArc`] with the value.
    pub fn new(value: Arc<T>) -> Self {
        Self(AtomicPtr::new(Arc::into_raw(value)))
    }

    /// Loads an [`Arc`] from the pointer.
    ///
    /// Returns [`None`] if the pointer is null.
    pub fn load(&self, order: Ordering) -> Option<Arc<T>> {
        let ptr = self.0.load(order);
        unsafe { Self::from_ptr(ptr) }
    }

    /// Stores an [`Arc`] into the pointer, returning the previous value.
    pub fn swap(&self, value: Option<Arc<T>>, order: Ordering) -> Option<Arc<T>> {
        let new = Self::into_ptr(value);
        let current = self.0.swap(new, order);
        unsafe { Self::from_ptr(current) }
    }

    /// Stores an [`Arc`] into the pointer if the current value is the same as
    /// `current`.
    pub fn compare_exchange(
        &self,
        current: Option<&Arc<T>>,
        new: Option<&Arc<T>>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Option<Arc<T>>, Option<Arc<T>>> {
        let new = new.map(Arc::as_ptr).unwrap_or(ptr::null());
        let current = current.map(Arc::as_ptr).unwrap_or(ptr::null());
        self.0
            .compare_exchange(current, new, success, failure)
            .map(|ptr| unsafe { Self::from_ptr(ptr) })
            .map_err(|ptr| unsafe { Self::from_ptr(ptr) })
    }

    fn into_ptr(value: Option<Arc<T>>) -> *const T {
        value.map(Arc::into_raw).unwrap_or(ptr::null())
    }

    unsafe fn from_ptr(ptr: *const T) -> Option<Arc<T>> {
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { Arc::from_raw(ptr) })
        }
    }
}

impl<T> Default for AtomicOptionArc<T> {
    fn default() -> Self {
        Self(AtomicPtr::new(ptr::null()))
    }
}

const RESERVED_COUNT: usize = 0x8000;

fn new_state<T>(ptr: *const T) -> u64 {
    let addr = ptr.addr();
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
    let layout = Layout::new::<ArcInner>();
    let (_, offset) = layout.extend(Layout::new::<T>()).unwrap();
    NonNull::new_unchecked((addr - offset) as _)
}

unsafe fn increase_count<T>(addr: usize, count: usize) {
    if addr != 0 {
        let ptr = inner_ptr::<T>(addr);
        ptr.as_ref().count.fetch_add(count, Ordering::Release);
    }
}

unsafe fn decrease_count<T>(addr: usize, count: usize) {
    if addr != 0 {
        let ptr = inner_ptr::<T>(addr);
        ptr.as_ref().count.fetch_sub(count, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arc() {
        let a = Arc::new(1);
        let b = Arc::new(2);
        let x = AtomicArc::new(a.clone());
        {
            let c = x.load(Ordering::Acquire);
            assert_eq!(c, a);
            assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 2);
        }
        {
            let c = x.swap(b.clone(), Ordering::AcqRel);
            assert_eq!(c, a);
            assert_eq!(Arc::strong_count(&a), 2);
            assert_eq!(Arc::strong_count(&b), RESERVED_COUNT + 2);
            let c = x.load(Ordering::Acquire);
            assert_eq!(c, b);
            assert_eq!(Arc::strong_count(&b), RESERVED_COUNT + 2);
        }
        {
            let c = x
                .compare_exchange(&b, &a, Ordering::AcqRel, Ordering::Acquire)
                .unwrap();
            assert_eq!(c, b);
            assert_eq!(Arc::strong_count(&b), 2);
            assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 2);
            let c = x
                .compare_exchange(&b, &a, Ordering::AcqRel, Ordering::Acquire)
                .unwrap_err();
            assert_eq!(c, a);
            assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 3);
        }
        drop(x);
        assert_eq!(Arc::strong_count(&a), 1);
        assert_eq!(Arc::strong_count(&b), 1);
    }

    #[test]
    fn test_option_arc() {
        let a = Arc::new(1);
        let b = Arc::new(2);
        let x = AtomicOptionArc::new(a.clone());
        {
            let c = x.load(Ordering::Acquire);
            assert_eq!(c, Some(a.clone()));
        }
        {
            let c = x.swap(Some(b.clone()), Ordering::AcqRel);
            assert_eq!(c, Some(a.clone()));
            let c = x.load(Ordering::Acquire);
            assert_eq!(c, Some(b.clone()));
        }
        {
            let c = x
                .compare_exchange(Some(&b), None, Ordering::AcqRel, Ordering::Relaxed)
                .unwrap();
            assert_eq!(c, Some(b.clone()));
            let c = x
                .compare_exchange(Some(&b), None, Ordering::AcqRel, Ordering::Relaxed)
                .unwrap_err();
            assert_eq!(c, None);
        }
        assert_eq!(x.load(Ordering::Acquire), None);
        assert_eq!(Arc::strong_count(&a), 1);
        assert_eq!(Arc::strong_count(&b), 1);
    }

    #[test]
    fn test_push_count() {
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
