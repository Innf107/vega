use std::sync::Mutex;

use crate::{gc::block_allocator, heap::HeapObject, owning_list::OwningList};

#[repr(C)]
pub struct ThreadState {
    pub allocation_pointer: *mut HeapObject,
    pub allocation_limit: *mut HeapObject,
}

unsafe impl Send for OwningList<ThreadState> {}

static THREADS: Mutex<OwningList<ThreadState>> = Mutex::new(OwningList::new());

// Create a new thread and register it with the runtime.
// Completed threads should properly be disposed of again using
// vega_destroy_thread
#[allow(static_mut_refs)]
pub extern "C" fn vega_create_thread() -> *mut ThreadState {
    let allocation_block = block_allocator::allocate_block();
    let thread_state = ThreadState {
        allocation_pointer: allocation_block.first_heap_object_pointer(),
        allocation_limit: allocation_block.allocation_limit(),
    };

    {
        let mut thread_list = THREADS.lock().unwrap();
        thread_list.append(thread_state)
    }
}

// Destroy a previously created thread and unregister it from the runtime.
pub extern "C" fn vega_destroy_thread(thread: *mut ThreadState) {
    let mut thread_list = THREADS.lock().unwrap();
    unsafe { thread_list.delete_by_pointer(thread) };
}
