use std::sync::Mutex;

use block::{BLOCK_SIZE, BlockList, BlockPointer};
use libc::{_SC_PAGESIZE, sysconf};
use roots::{ShadowStackFrame, for_stack_roots};

use crate::{
    either::Either,
    gc::block::BlockDescriptor,
    heap::{
        ForwardPointer, GenerationIndex, Header, HeapObject, HeapObjectHandle, InfoTable,
        round_up_to_heap_alignment,
    },
    make_send::UnsafeMakeSend,
    settings::RuntimeSettings,
};

pub mod block;
pub mod block_allocator;
pub mod roots;

pub struct Generation {
    used_blocks: Mutex<UnsafeMakeSend<BlockList>>,
    pending_blocks: Mutex<UnsafeMakeSend<BlockList>>,
    max_block_count: usize,
    index: GenerationIndex,
}

impl Generation {
    const fn new(index: GenerationIndex, max_block_count: usize) -> Self {
        Generation {
            used_blocks: unsafe { Mutex::new(UnsafeMakeSend::new(BlockList::new())) },
            pending_blocks: unsafe { Mutex::new(UnsafeMakeSend::new(BlockList::new())) },
            max_block_count,
            index,
        }
    }
}

static mut NURSERY: Generation = Generation::new(GenerationIndex::MINOR, 0);
static mut MAJOR_HEAP: Generation = Generation::new(GenerationIndex::MAJOR, 0);

pub fn initialize_gc(settings: &RuntimeSettings) {
    let page_size = unsafe { sysconf(_SC_PAGESIZE) } as usize;
    assert!(
        page_size >= BLOCK_SIZE,
        "The system page size ({page_size}) is smaller than the vega runtime's block size ({BLOCK_SIZE}). This is currently unsupported by the memory manager. If you're seeing this, open an issue."
    );

    assert!(settings.nursery_size_in_blocks > 0);
    assert!(settings.initial_major_heap_size_in_blocks > 0);
    unsafe {
        NURSERY.max_block_count = settings.nursery_size_in_blocks;
        MAJOR_HEAP.max_block_count = settings.initial_major_heap_size_in_blocks;
    }
}

// The thread-local state carried by each GC thread during a collection.
// In particular, this tells it where to evacuate objects to.
struct GCState {
    allocation_pointer: *mut HeapObject,
    allocation_limit: *const HeapObject,
    allocation_block: BlockPointer,
    target_generation: &'static Generation,
}

#[allow(static_mut_refs)]
pub fn collect_garbage(shadow_stack_pointer: *const ShadowStackFrame) {
    let mut state = {
        let allocation_block = block_allocator::allocate_block();

        GCState {
            allocation_pointer: allocation_block.first_heap_object_pointer(),
            allocation_limit: allocation_block.allocation_limit(),
            allocation_block,
            target_generation: unsafe { &MAJOR_HEAP },
        }
    };
    for_stack_roots(shadow_stack_pointer, |stack_root| unsafe {
        let from_object = HeapObject::from_data(*stack_root);

        let relocated_heap_object = evacuate(&mut state, from_object);
        *stack_root = HeapObject::data(relocated_heap_object);
    });

    loop {
        // TODO: this will be much more interesting once it is multi-threaded
        let block = unsafe {
            let mut pending_set_guard = MAJOR_HEAP.pending_blocks.lock().unwrap();
            let pending_set = pending_set_guard.get_mut();
            pending_set.pop_back()
        };
        match block {
            None => break, // We are done for now. In the future, we will wait until either all threads are done or more work is being added
            Some(block) => unsafe {
                for heap_object in block.iter_heap_objects() {
                    scavenge(&mut state, heap_object.cast_const());
                }
            },
        }
    }
}

/// SAFETY: heap_object must point to a valid heap object or a forward pointer
unsafe fn evacuate(state: &mut GCState, heap_object: *const HeapObject) -> *const HeapObject {
    match unsafe { HeapObject::as_handle(heap_object) } {
        // Null pointers and static arrays are not actually allocated on the heap and never move,
        // so we don't need to evacuate them.
        // We do need to *scavenge* static arrays, but we need to do that as roots anyway, since
        // a static array being unreachable from the heap doesn't mean that it isn't still reachable from *code*.
        HeapObjectHandle::Null | HeapObjectHandle::StaticArray(_) => heap_object,
        HeapObjectHandle::Boxed(_) | HeapObjectHandle::Array(_) => {
            let size = unsafe { HeapObject::total_stride(heap_object) };
            let to_space_allocation: *mut HeapObject = allocate_for_evacuation(state, size);

            // We need to cast here, since copy_to expects an *element* count rather than a byte count
            unsafe {
                heap_object
                    .cast::<u8>()
                    .copy_to(to_space_allocation.cast::<u8>(), size);
            }

            // SAFETY: this is only safe as long as evacuation is entirely single-threaded.
            // When we have parallel collection, we need to replace this with a proper locking protocol
            unsafe {
                HeapObject::set_header_unsynchronized(
                    to_space_allocation,
                    HeapObject::header(to_space_allocation).set_generation(GenerationIndex::MAJOR),
                )
            }
            unsafe {
                HeapObject::override_with_forward_pointer_unsynchronized(
                    heap_object as *mut HeapObject,
                    ForwardPointer {
                        to_space_allocation,
                    },
                )
            };

            to_space_allocation
        }
        // If we hit a forward pointer, we don't need to evacuate anything anymore but we do need
        // to relocate it
        HeapObjectHandle::ForwardPointer(ForwardPointer {
            to_space_allocation,
        }) => to_space_allocation,
    }
}

/// This takes a previously evacuated heap object (in to-space) and evacuates all its
/// referenced heap pointers.
/// This should eventually be called on every evacuated heap
/// object, but we cannot call it *immediately* since that will make us run out of stack space.
/// Instead, we (sequentially) scavenge to-space objects that have already been evacuated.
/// Once every object has been scavenged, garbage collection has completed.
///
/// SAFETY: the pointer has to point to a valid heap object.
/// In particular, it must *NOT* point to a forwarding pointer
unsafe fn scavenge(state: &mut GCState, heap_object: *const HeapObject) {
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
                    let relocated_pointer =
                        evacuate(state, HeapObject::from_data(*element_pointer));

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
                                evacuate(state, HeapObject::from_data(*element_pointer));
                            *element_pointer = HeapObject::data(relocated_pointer)
                        }
                    }
                }
            }
        }
        // Even though we don't need to evacuate static arrays, we do need to scavenge them (if they contain boxed pointers)
        HeapObjectHandle::StaticArray(static_array) => {
            if static_array.layout.element_boxed_count > 0 {
                for element_index in 0..static_array.length() {
                    for boxed_index in 0..static_array.layout.element_boxed_count {
                        unsafe {
                            let element_pointer =
                                static_array.boxed_element(element_index, boxed_index);
                            let relocated_pointer =
                                evacuate(state, HeapObject::from_data(*element_pointer));
                            *element_pointer = HeapObject::data(relocated_pointer)
                        }
                    }
                }
            }
        }
    }
}

#[inline]
fn allocate_for_evacuation(gc_state: &mut GCState, size: usize) -> *mut HeapObject {
    unsafe {
        debug_assert!(gc_state.allocation_limit > gc_state.allocation_pointer);
        if gc_state
            .allocation_limit
            .byte_offset_from_unsigned(gc_state.allocation_pointer)
            < size
        {
            let pointer = gc_state.allocation_pointer;
            gc_state.allocation_pointer = gc_state
                .allocation_pointer
                .byte_add(round_up_to_heap_alignment(size));
            pointer
        } else {
            let filled_block = gc_state.allocation_block;

            // We need to make sure that we clearly mark the end of this block so that
            // the heap objects can be traversed properly when scavenging
            if filled_block
                .allocation_limit()
                .offset_from(gc_state.allocation_pointer)
                >= size_of::<Header>() as isize
            {
                *(gc_state.allocation_pointer.cast::<Header>()) = Header::end_of_block_header();
            }

            // This block has been filled as much as we can so we move it into the pending set that will be
            // scavenged in a moment
            {
                let mut pending_blocks = gc_state.target_generation.pending_blocks.lock().unwrap();
                pending_blocks.get_mut().append(filled_block);
            }
            let new_block = block_allocator::allocate_block();
            gc_state.allocation_block = new_block;
            gc_state.allocation_pointer = new_block.first_heap_object_pointer();
            gc_state.allocation_limit = new_block.allocation_limit();

            // Now that we have a new block, we can unconditionally allocate a heap object from it
            let pointer = gc_state.allocation_pointer;
            gc_state.allocation_pointer = gc_state
                .allocation_pointer
                .byte_add(round_up_to_heap_alignment(size));
            pointer
        }
    }
}
