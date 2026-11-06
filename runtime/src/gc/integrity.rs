use std::{
    cell::LazyCell,
    collections::HashSet,
    sync::Mutex,
};

use crate::{
    heap::{HeapObject, HeapObjectHandle},
    make_send::UnsafeMakeSend,
};

static LIVE_MINOR_ALLOCATIONS: Mutex<UnsafeMakeSend<LazyCell<HashSet<*mut HeapObject>>>> =
    Mutex::new(UnsafeMakeSend::new(LazyCell::new(|| HashSet::new())));

static LIVE_MAJOR_ALLOCATIONS: Mutex<UnsafeMakeSend<LazyCell<HashSet<*mut HeapObject>>>> =
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

pub fn register_major_heap_allocation(data_pointer: *mut HeapObject) {
    unsafe {
        LIVE_MAJOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .insert(data_pointer);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_register_allocation(data_pointer: *mut HeapObject) {
    unsafe {
        LIVE_MINOR_ALLOCATIONS
            .lock()
            .unwrap()
            .get_mut()
            .insert(data_pointer);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_check_allocation_integrity(data_pointer: *mut HeapObject) {
    if data_pointer.is_null() {
        return;
    }
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

#[unsafe(no_mangle)]
pub extern "C" fn vega_debug_recursive_integrity_check(heap_object: *mut HeapObject) {
    vega_check_allocation_integrity(heap_object);
    // We cannot actually do this recursively since that could cause us to stack overflow, so we
    // use an explicit stack instead.
    let mut pending_objects = vec![heap_object];
    loop {
        match pending_objects.pop() {
            None => break,
            Some(heap_object) => unsafe {
                vega_check_allocation_integrity(heap_object);
                match HeapObject::as_handle(heap_object) {
                    HeapObjectHandle::Boxed(boxed_handle) => {
                        for i in 0..boxed_handle.layout.boxed_count {
                            pending_objects.push(*boxed_handle.boxed_element(i));
                        }
                    }
                    HeapObjectHandle::Array(array_handle) => {
                        if array_handle.layout.element_boxed_count > 0 {
                            for element_index in 0..array_handle.length() {
                                for boxed_index in 0..array_handle.layout.element_boxed_count {
                                    pending_objects.push(
                                        *array_handle.boxed_element(element_index, boxed_index),
                                    )
                                }
                            }
                        }
                    }
                    HeapObjectHandle::StaticArray(static_array_handle) => {
                        if static_array_handle.layout.element_boxed_count > 0 {
                            for element_index in 0..static_array_handle.length() {
                                for boxed_index in 0..static_array_handle.layout.element_boxed_count
                                {
                                    pending_objects.push(
                                        *static_array_handle
                                            .boxed_element(element_index, boxed_index),
                                    )
                                }
                            }
                        }
                    }
                    HeapObjectHandle::ForwardPointer(forward_pointer) => {
                        panic!("integrity check encountered forward pointer: {forward_pointer:?}")
                    }
                    HeapObjectHandle::Null => {}
                }
            },
        }
    }
}
