use std::{
    cell::LazyCell,
    collections::HashSet,
    sync::{LazyLock, Mutex},
};

use crate::make_send::UnsafeMakeSend;

static LIVE_MINOR_ALLOCATIONS: Mutex<UnsafeMakeSend<LazyCell<HashSet<*mut u8>>>> =
    Mutex::new(UnsafeMakeSend::new(LazyCell::new(|| HashSet::new())));

static LIVE_MAJOR_ALLOCATIONS: Mutex<UnsafeMakeSend<LazyCell<HashSet<*mut u8>>>> =
    Mutex::new(UnsafeMakeSend::new(LazyCell::new(|| HashSet::new())));

pub fn reset_tracked_allocations(include_major_heap: bool) {
    unsafe {
        LIVE_MINOR_ALLOCATIONS.lock().unwrap().get_mut().clear();
    }
    if include_major_heap {
        unsafe {
            LIVE_MAJOR_ALLOCATIONS.lock().unwrap().get_mut().clear();
        }
    }
}

pub fn register_major_heap_allocation(data_pointer: *mut u8) {
    unsafe {
        LIVE_MAJOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .insert(data_pointer);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_register_allocation(data_pointer: *mut u8) {
    unsafe {
        LIVE_MINOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .insert(data_pointer);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_check_allocation_integrity(data_pointer: *mut u8) {
    let is_valid_minor = unsafe {
        LIVE_MINOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .contains(&data_pointer)
    };
    let is_valid_major = unsafe {
        LIVE_MAJOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .contains(&data_pointer)
    };
    if is_valid_minor && is_valid_major {
        panic!("Data pointer tracked in both minor and major heap: {data_pointer:?}");
    }
    if !is_valid_minor && !is_valid_major {
        panic!(
            "Heap integrity check failed. Data pointer {data_pointer:?} does not point to a valid allocation."
        );
    }
}
