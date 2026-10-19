use std::{ptr::null_mut, sync::Mutex};

use crate::{
    gc::{block_allocator, roots::ShadowStackFrame},
    heap::HeapObject,
    owning_list::OwningList,
};

#[repr(C)]
pub struct ThreadState {
    pub shadow_stack_pointer: *mut ShadowStackFrame,
    pub allocation_pointer: *mut HeapObject,
    pub allocation_limit: *mut HeapObject,
}

unsafe impl Send for OwningList<ThreadState> {}

static THREADS: Mutex<OwningList<ThreadState>> = Mutex::new(OwningList::new());

// Create the state for a new thread and register it with the runtime.
// Completed threads should properly be disposed of again using
// vega_destroy_thread
#[allow(static_mut_refs)]
#[unsafe(no_mangle)]
pub extern "C" fn vega_create_thread_state() -> *mut ThreadState {
    let allocation_block = block_allocator::allocate_block();
    let thread_state = ThreadState {
        // the initial shadow stack pointer is null so that the GC knows to stop once it is hit
        shadow_stack_pointer: null_mut(),
        allocation_pointer: allocation_block.first_heap_object_pointer(),
        allocation_limit: allocation_block.allocation_limit(),
    };

    {
        let mut thread_list = THREADS.lock().unwrap();
        thread_list.append(thread_state)
    }
}

// Destroy a previously created thread and unregister it from the runtime.
#[unsafe(no_mangle)]
pub extern "C" fn vega_destroy_thread(thread: *mut ThreadState) {
    let mut thread_list = THREADS.lock().unwrap();
    unsafe { thread_list.delete_by_pointer(thread) };
}
