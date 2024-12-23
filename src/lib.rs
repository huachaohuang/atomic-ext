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

pub struct AtomicArc<T> {
    state: AtomicU64,
    phantom: PhantomData<*mut Arc<T>>,
}

impl<T> AtomicArc<T> {
    pub fn new(value: Arc<T>) -> Self {
        let state = new_state(value);
        Self {
            state: AtomicU64::new(state),
            phantom: PhantomData,
        }
    }

    pub fn load(&self, order: Ordering) -> Arc<T> {
        let mut state = self.state.fetch_add(1, order);
        let (addr, mut count) = unpack_state(state);
        if count > RESERVED_COUNT {
            panic!("external reference count overflow");
        }
        if count > RESERVED_COUNT / 2 {
            // Push the external reference count back
            let new_state = pack_state(addr);
            loop {
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::AcqRel,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => unsafe {
                        increase_count::<T>(addr, count);
                    },
                    Err(new_state) => {
                        let (new_addr, new_count) = unpack_state(new_state);
                        if new_addr != addr || new_count < RESERVED_COUNT / 2 {
                            // Someone else has changed the address or the reference count.
                            break;
                        }
                        state = new_state;
                        count = new_count;
                    }
                }
            }
        }
        unsafe { Arc::from_raw(addr as _) }
    }

    pub fn swap(&self, value: Arc<T>, order: Ordering) -> Arc<T> {
        let state = self.state.swap(new_state(value), order);
        let (addr, count) = unpack_state(state);
        unsafe {
            decrease_count::<T>(addr, RESERVED_COUNT - count);
            Arc::from_raw(addr as _)
        }
    }
}

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
    fn test() {
        let x = AtomicArc::new(Arc::new(1));
        let a = x.load(Ordering::Acquire);
        assert_eq!(Arc::strong_count(&a), RESERVED_COUNT + 1);
        let b = x.swap(Arc::new(2), Ordering::AcqRel);
        assert_eq!(Arc::strong_count(&a), 2);
        assert_eq!(Arc::strong_count(&b), 2);
    }
}
