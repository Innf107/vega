use block_allocator::{BLOCK_SIZE, BlockList, allocate_block_list};
use libc::{_SC_PAGESIZE, sysconf};
use roots::{ShadowStackFrame, for_stack_roots};

use crate::{
    either::Either,
    heap::{ForwardPointer, HeapObject, HeapObjectHandle, InfoTable},
};

pub mod block_allocator;
pub mod roots;

pub struct AllocationArea {
    blocks: BlockList,
}

static mut NURSERY: AllocationArea = AllocationArea {
    blocks: unsafe { BlockList::dummy() },
};

pub fn initialize_heap(nursery_size_in_blocks: usize) {
    let page_size = unsafe { sysconf(_SC_PAGESIZE) } as usize;
    assert!(
        page_size >= BLOCK_SIZE,
        "The system page size ({page_size}) is smaller than the vega runtime's block size ({BLOCK_SIZE}). This is currently unsupported by the memory manager. If you're seeing this, open an issue."
    );

    unsafe { NURSERY.blocks = allocate_block_list(nursery_size_in_blocks) };
}

pub fn allocate_in(area: &AllocationArea, info_table: &'static InfoTable) {
    todo!()
}

pub fn collect_garbage(shadow_stack_pointer: *const ShadowStackFrame) {
    for_stack_roots(shadow_stack_pointer, |stack_root| unsafe {
        let from_object = HeapObject::from_data(*stack_root);

        let relocated_heap_object = evacuate(from_object);
        *stack_root = HeapObject::data(relocated_heap_object);
    });
    todo!("scavenge")
}

/// SAFETY: heap_object must point to a valid heap object or a forward pointer
pub unsafe fn evacuate(heap_object: *const HeapObject) -> *const HeapObject {
    let header = unsafe { HeapObject::header(heap_object) };
    match header.info_table_or_forward_pointer() {
        Either::Left(_) => unsafe { evacuate(heap_object) },
        // If we hit a forward pointer, we don't need to evacuate anything anymore but we do need
        // to relocate it
        Either::Right(ForwardPointer {
            to_space_allocation,
        }) => to_space_allocation,
    }
}

/// This takes a previously evacuated heap object and evacuates all its
/// referenced heap pointers.
/// This should eventually be called on every evacuated heap
/// object, but we cannot call it *immediately* since that will make us run out of stack space.
/// Instead, we (sequentially) scavenge to-space objects that have already been evacuated.
/// Once every object has been scavenged, garbage collection has completed.
///
/// SAFETY: the pointer has to point to a valid heap object.
/// In particular, it must *NOT* point to a forwarding pointer
pub unsafe fn scavenge(heap_object: *const HeapObject) {
    // SAFETY:
    let handle = unsafe { HeapObject::as_handle(heap_object) };
    match handle {
        HeapObjectHandle::Null => {
            panic!("Trying to scavenge Null heap object. This should not have been evacuated.")
        }
        HeapObjectHandle::ForwardPointer(forward_pointer) => {
            panic!(
                "Trying to scavenge ForwardPointer {:?}",
                forward_pointer.to_space_allocation
            )
        }
        HeapObjectHandle::Boxed(boxed) => {
            for i in 0..boxed.layout.boxed_count {
                unsafe {
                    // this is a pointer to the element (which is itself another pointer to the data segment of a heap object)
                    let element_pointer = boxed.boxed_element(i);
                    let relocated_pointer = evacuate(HeapObject::from_data(*element_pointer));

                    *element_pointer = HeapObject::data(relocated_pointer)
                };
            }
        }
        HeapObjectHandle::Array(array) => {
            if array.layout.element_boxed_count > 0 {
                for element_index in 0..array.length() {
                    for boxed_index in 0..array.layout.element_boxed_count {
                        unsafe {
                            let element_pointer = array.boxed_element(element_index, boxed_index);
                            let relocated_pointer =
                                evacuate(HeapObject::from_data(*element_pointer));
                            *element_pointer = HeapObject::data(relocated_pointer)
                        }
                    }
                }
            }
        }
        // We do need to scavenge static arrays, but only to
        HeapObjectHandle::StaticArray(static_array) => {
            if static_array.layout.element_boxed_count > 0 {
                for element_index in 0..static_array.length() {
                    for boxed_index in 0..static_array.layout.element_boxed_count {
                        unsafe {
                            let element_pointer =
                                static_array.boxed_element(element_index, boxed_index);
                            let relocated_pointer =
                                evacuate(HeapObject::from_data(*element_pointer));
                            *element_pointer = HeapObject::data(relocated_pointer)
                        }
                    }
                }
            }
        }
    }
}
