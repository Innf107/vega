use std::{cmp::max, hint::cold_path, mem::swap, thread};

use block::{BLOCK_SIZE, BlockList};
use libc::{_SC_PAGESIZE, sysconf};
use roots::{ShadowStackFrame, for_stack_roots};

use crate::{
    gc::{
        block::BlockPointer,
        generations::{MAJOR_HEAP, initialize_generations, major_heap, nursery},
        integrity::{
            register_major_heap_allocation, reset_tracked_allocations,
            vega_check_allocation_integrity, vega_debug_recursive_integrity_check,
        },
        roots::debug_stack_roots,
    },
    heap::{
        AllocationState, ForwardPointer, GenerationIndex, HEAP_ALIGNMENT, HeapObject,
        HeapObjectHandle, finish_block, round_up_to_heap_alignment,
    },
    settings::{RuntimeSettings, settings},
    thread::ThreadState,
};

pub mod block;
pub mod block_allocator;
pub mod generations;
pub mod integrity;
pub mod roots;

pub fn initialize_gc(settings: &RuntimeSettings) {
    let page_size = unsafe { sysconf(_SC_PAGESIZE) } as usize;
    assert!(
        page_size >= BLOCK_SIZE,
        "The system page size ({page_size}) is smaller than the vega runtime's block size ({BLOCK_SIZE}). This is currently unsupported by the memory manager. If you're seeing this, open an issue."
    );
    initialize_generations(settings);
}

// The thread-local state carried by each GC thread during a collection.
// In particular, this tells it where to evacuate objects to.
struct GCState {
    allocation_pointer: *mut HeapObject,
    allocation_limit: *mut HeapObject,
    collect_major_heap: bool,
}
impl GCState {
    fn has_empty_allocation_block(&self) -> bool {
        return unsafe {
            self.allocation_limit
                .byte_offset_from_unsigned(self.allocation_pointer)
                == BlockPointer::SIZE_FOR_ALLOCATION
        };
    }
}
impl AllocationState for GCState {
    fn allocation_pointer(&mut self) -> &mut *mut HeapObject {
        &mut self.allocation_pointer
    }

    fn allocation_limit(&mut self) -> &mut *mut HeapObject {
        &mut self.allocation_limit
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_collect_garbage(
    thread_state: &mut ThreadState,
    force_major_collection: bool,
) {
    collect_garbage(thread_state, force_major_collection);
}

pub fn collect_garbage(thread_state: &mut ThreadState, force_major_collection: bool) {
    let shadow_stack_pointer = thread_state.shadow_stack_pointer;
    let collect_major_heap = force_major_collection
        || unsafe {
            major_heap().max_block_count
                - major_heap()
                    .used_blocks
                    .lock()
                    .unwrap()
                    .get()
                    .size_in_blocks()
                < nursery().max_block_count
        };
    // println!("GC start (major: {collect_major_heap}, forced: {force_major_collection})");

    if settings().root_integrity {
        for_stack_roots(shadow_stack_pointer, |pointer_to_root| {
            vega_debug_recursive_integrity_check(unsafe { *pointer_to_root });
        });
    }

    if settings().liveness_integrity {
        cold_path();
        reset_tracked_allocations(collect_major_heap);
    }

    let mut gc_state = {
        let allocation_block = block_allocator::allocate_block();

        GCState {
            allocation_pointer: allocation_block.first_heap_object_pointer(),
            allocation_limit: allocation_block.allocation_limit(),
            collect_major_heap,
        }
    };
    // sanity check that GCState::has_empty_allocation_block works correctly
    debug_assert!(gc_state.has_empty_allocation_block());

    if settings().debug_stack_roots {
        println!("~~~~~~GC (major: {collect_major_heap})~~~~~~~");
        debug_stack_roots(shadow_stack_pointer);
        println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
    }

    // TODO: every mutator thread needs to commit its current allocation block before we do a GC.
    // It's okay if we overrun the nursery limit here since we are about to clear it out anyway.
    finish_block(thread_state, &nursery().used_blocks, |_, _| {});

    for_stack_roots(shadow_stack_pointer, |stack_root| unsafe {
        let relocated_heap_object = evacuate(&mut gc_state, *stack_root);
        *stack_root = relocated_heap_object;
    });

    loop {
        // TODO: this will be much more interesting once it is multi-threaded
        let block = unsafe {
            let mut pending_set_guard = major_heap().pending_blocks.lock().unwrap();
            let pending_set = pending_set_guard.get_mut();
            pending_set.pop_back()
        };
        match block {
            None => {
                if gc_state.has_empty_allocation_block() {
                    unsafe {
                        let block =
                            BlockPointer::from_heap_object_pointer(gc_state.allocation_pointer);
                        block_allocator::free_block(block);
                    }
                    // We are done for now. In the future, we will wait until either all threads are done or more work is being added
                    break;
                } else {
                    // The pending set is empty but we still have evacuated heap objects in our gc thread's state that we haven't committed yet.

                    // TODO: This will cause a ton of fragmentation if we have something like a long singly linked list, since
                    // we will evacuate a single object, exhaust our pending set and immediately have to commit the entire block
                    // for just one object.
                    finish_block(
                        &mut gc_state,
                        &major_heap().pending_blocks,
                        |heap_size, gc_state| {
                            debug_assert!(
                                gc_state.collect_major_heap
                                    || (heap_size
                                        <= major_heap().max_block_count
                                            - nursery().max_block_count)
                            );
                        },
                    );
                }
            }
            Some(block) => unsafe {
                for heap_object in block.iter_heap_objects() {
                    scavenge(&mut gc_state, heap_object);
                }
                major_heap()
                    .to_space
                    .lock()
                    .unwrap()
                    .get_mut()
                    .append(block);
            },
        }
    }

    unsafe {
        // We do en-masse promotion so we can immediately give all nursery blocks back to the block allocator
        let used_blocks = std::mem::replace(
            nursery().used_blocks.lock().unwrap().get_mut(),
            BlockList::new(),
        );
        block_allocator::free_block_list(used_blocks);
    }
    unsafe {
        let mut used = major_heap().used_blocks.lock().unwrap();
        let mut to_space = major_heap().to_space.lock().unwrap();
        swap(&mut *used, &mut *to_space);
        let previously_used_blocks = std::mem::replace(to_space.get_mut(), BlockList::new());
        block_allocator::free_block_list(previously_used_blocks);
    }

    if collect_major_heap {
        let current_size = major_heap().max_block_count;
        let live_size = unsafe {
            major_heap()
                .used_blocks
                .lock()
                .unwrap()
                .get()
                .size_in_blocks()
        };
        let scale_factor = settings().major_heap_scaling_factor;
        let nursery_capacity = nursery().max_block_count;

        // TODO: it would be nice to also scale the heap down occasionally but we should be a bit more careful about that
        let new_major_size = max(
            current_size,
            (scale_factor * ((live_size + nursery_capacity) as f64)) as usize,
        );

        // SAFETY: this is fine since GC has finished and every other thread is still blocked in a safe point
        // so we are the only thread operating on the MAJOR heap.
        unsafe {
            MAJOR_HEAP.max_block_count = new_major_size;
        }
    }

    // We do en-masse promotion so the nursery should be empty after every GC
    debug_assert_eq!(
        unsafe { nursery().used_blocks.lock().unwrap().get().size_in_blocks() },
        0
    );

    if settings().root_integrity {
        for_stack_roots(shadow_stack_pointer, |pointer_to_root| {
            vega_debug_recursive_integrity_check(unsafe { *pointer_to_root });
        });
    }

    // println!("GC end");
    // TODO: release other threads *now*, doing so earlier could race the resizing above.
}

/// SAFETY: heap_object must point to a valid heap object or a forward pointer
unsafe fn evacuate(state: &mut GCState, heap_object: *mut HeapObject) -> *mut HeapObject {
    if !state.collect_major_heap
        && unsafe { HeapObject::header(heap_object).generation().is_major() }
    {
        // We won't collect this generation so we just leave it where it is and do as little work as possible.
        return heap_object;
    }

    match unsafe { HeapObject::as_handle(heap_object) } {
        // Null pointers and static arrays are not actually allocated on the heap and never move,
        // so we don't need to evacuate them.
        // We do need to *scavenge* static arrays, but we need to do that as roots anyway, since
        // a static array being unreachable from the heap doesn't mean that it isn't still reachable from *code*.
        HeapObjectHandle::Null | HeapObjectHandle::StaticArray(_) => heap_object,
        HeapObjectHandle::Boxed(_) | HeapObjectHandle::Array(_) => {
            if settings().evacuation_integrity {
                cold_path();
                vega_check_allocation_integrity(heap_object);
            }
            let size = unsafe { HeapObject::total_stride(heap_object) };
            let to_space_allocation: *mut HeapObject = allocate_for_evacuation(state, size);

            // We need to cast here, since copy_to expects an *element* count rather than a byte count
            unsafe {
                heap_object
                    .cast::<u8>()
                    // TODO: use copy_to_non_overlapping
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
unsafe fn scavenge(state: &mut GCState, heap_object: *mut HeapObject) {
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
                    let relocated_pointer = evacuate(state, *element_pointer);

                    *element_pointer = relocated_pointer;
                };
            }
        }
        HeapObjectHandle::Array(array) => {
            if array.layout.element_boxed_count > 0 {
                for element_index in 0..array.length() {
                    for boxed_index in 0..array.layout.element_boxed_count {
                        unsafe {
                            let element_pointer = array.boxed_element(element_index, boxed_index);
                            let relocated_pointer = evacuate(state, *element_pointer);
                            *element_pointer = relocated_pointer
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
                            let relocated_pointer = evacuate(state, *element_pointer);
                            *element_pointer = relocated_pointer
                        }
                    }
                }
            }
        }
    }
}

#[inline]
fn allocate_for_evacuation(gc_state: &mut GCState, size: usize) -> *mut HeapObject {
    debug_assert!(size.is_multiple_of(HEAP_ALIGNMENT));
    unsafe {
        debug_assert!(gc_state.allocation_limit > gc_state.allocation_pointer);
        if gc_state
            .allocation_limit
            .byte_offset_from_unsigned(gc_state.allocation_pointer)
            < size
        {
            cold_path();
            finish_block(
                gc_state,
                &major_heap().pending_blocks,
                // We don't need any limit checks during garbage collection.
                // We always make sure that a minor collection has enough space in the major generation.
                // If there is not enough space, we trigger a full GC
                |heap_size, gc_state| {
                    debug_assert!(
                        gc_state.collect_major_heap
                            || (heap_size
                                <= major_heap().max_block_count - nursery().max_block_count)
                    );
                },
            );
        }
        debug_assert!(
            gc_state
                .allocation_limit
                .byte_offset_from_unsigned(gc_state.allocation_pointer)
                >= size
        );
        debug_assert!(
            gc_state
                .allocation_pointer
                .addr()
                .is_multiple_of(HEAP_ALIGNMENT)
        );

        let pointer = gc_state.allocation_pointer;
        gc_state.allocation_pointer = gc_state
            .allocation_pointer
            .byte_add(round_up_to_heap_alignment(size));

        debug_assert!(
            gc_state
                .allocation_pointer
                .addr()
                .is_multiple_of(HEAP_ALIGNMENT)
        );

        if settings().liveness_integrity {
            cold_path();
            register_major_heap_allocation(pointer);
        }

        pointer
    }
}
