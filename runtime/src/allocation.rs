use std::{ffi::c_void, hint::cold_path, sync::Mutex};

use crate::{
    gc::{
        block::{BLOCK_SIZE, BlockList, BlockPointer},
        block_allocator, collect_garbage,
        generations::{major_heap, nursery},
    },
    heap::{
        ArrayHeapObject, GenerationIndex, HEAP_ALIGNMENT, Header, HeapObject, InfoTable,
        round_up_to_heap_alignment,
    },
    make_send::UnsafeMakeSend,
    thread::ThreadState,
};

// I would prefer to manually pass these as references into finish_block, but
// rust's borrow checker doesn't like it if we do that while also borrowing the
// state for the block_limit_check function.
// That's why we use a trait so that we can explicitly give the callback a temporary
// handle on our state.
pub trait AllocationState {
    fn allocation_pointer(&mut self) -> &mut *mut HeapObject;
    fn allocation_limit(&mut self) -> &mut *mut HeapObject;

    fn has_empty_allocation_block(&mut self) -> bool {
        return unsafe {
            self.allocation_limit()
                .byte_offset_from_unsigned(*self.allocation_pointer())
                == BlockPointer::SIZE_FOR_ALLOCATION
        };
    }
}

// Finish the current block and allocate a new one from the block allocator.
// This is shared between GC and mutator allocation.
// The arguments should typically be pointers to the allocation pointer and limit of their respective state objects.
#[inline]
pub fn finish_block<State: AllocationState>(
    state: &mut State,
    target_list: &'static Mutex<UnsafeMakeSend<BlockList>>,
    mut block_limit_check: impl for<'a> FnMut(usize, &'a mut State),
) {
    unsafe {
        debug_assert!(
            BlockPointer::from_heap_object_pointer(*state.allocation_pointer()).is_unlinked()
        );
        let filled_block = BlockPointer::from_heap_object_pointer(*state.allocation_pointer());
        debug_assert!(filled_block.allocation_limit() == *state.allocation_limit());
        debug_assert!(
            filled_block.first_heap_object_pointer() <= *state.allocation_pointer()
                && *state.allocation_pointer() <= *state.allocation_limit()
        );

        // We need to make sure that we clearly mark the end of this block so that
        // the heap objects can be traversed properly when scavenging
        if filled_block
            .allocation_limit()
            .byte_offset_from(*state.allocation_pointer())
            >= size_of::<Header>() as isize
        {
            HeapObject::set_header_unsynchronized(
                *state.allocation_pointer(),
                Header::end_of_block_header(),
            );
        }

        let size = {
            let mut pending_blocks = target_list.lock().unwrap();
            pending_blocks.get_mut().append(filled_block);
            pending_blocks.get().size_in_blocks()
        };
        // We allocate the new block before the GC check since we already added it to the pending set.
        // If we didn't do it this way, the GC would try to add it to the pending set again
        // and then fail a debug assertion because it is not unlinked.
        //
        // Since the block is still empty, the GC will just leave it alone and we can use it after
        // the collection is done.
        let new_block = block_allocator::allocate_block();
        *state.allocation_pointer() = new_block.first_heap_object_pointer();
        *state.allocation_limit() = new_block.allocation_limit();

        block_limit_check(size, state);
    }
}

// Allocate 'byte_count' bytes in the current allocation pointer.
// This does *not* include the size of a heap object header
// and the returned memory is not initialized in any way.
#[inline]
pub fn allocate_generic<State: AllocationState>(
    state: &mut State,
    byte_count: usize,
    target_list: &'static Mutex<UnsafeMakeSend<BlockList>>,
    block_limit_check: impl for<'a> FnMut(usize, &'a mut State),
) -> *mut HeapObject {
    let allocation_size = round_up_to_heap_alignment(byte_count);

    let remaining_size_in_block =
        unsafe { (*state.allocation_limit()).byte_offset_from(*state.allocation_pointer()) };
    if remaining_size_in_block <= allocation_size as isize {
        cold_path();
        let previous_allocation_pointer = *state.allocation_pointer();

        finish_block(state, target_list, block_limit_check);
        // In the edge case that the allocation *exactly* fills up the rest of the block,
        // we still need to allocate a new block since otherwise the allocation pointer would
        // point to the start of the next object, but we *can* return a pointer to the old block
        // since there is (just barely) enough space left for the allocation.
        //
        // We don't need to increment the allocation pointer here, since that one already points to
        // the start of the new block allocated by finish_block.
        if remaining_size_in_block == allocation_size as isize {
            return previous_allocation_pointer;
        }
    }
    debug_assert!(
        unsafe { (*state.allocation_limit()).byte_offset_from(*state.allocation_pointer()) }
            >= byte_count as isize
    );

    let pointer = *state.allocation_pointer();
    unsafe {
        *state.allocation_pointer() = (*state.allocation_pointer()).byte_add(allocation_size);
    };
    debug_assert!(
        (*state.allocation_pointer())
            .addr()
            .is_multiple_of(HEAP_ALIGNMENT)
    );
    pointer
}

// Allocate 'byte_count' bytes in the current allocation block.
// This does *not* include the size of a heap object header
// and the returned memory is not initialized in any way.
#[inline]
pub fn allocate_mutator(thread_state: &mut ThreadState, byte_count: usize) -> *mut HeapObject {
    allocate_generic(
        thread_state,
        byte_count,
        &nursery().used_blocks,
        |nursery_size, thread_state| {
            if nursery_size >= nursery().max_block_count {
                cold_path();
                collect_garbage(thread_state, false);
            }
        },
    )
}

/// Allocate a box for the given info table and return a pointer to the (uninitialized) *data*.
/// To access the heap object header, use [HeapObject::from_data].
// TODO: eventually we will want to inline this directly into the generated code but
// it's simpler to keep it as a rust function for now
// SAFETY: this assumes that info_table points to a boxed heap object info table
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_boxed(
    thread_state: &mut ThreadState,
    info_table: &'static InfoTable,
) -> *mut HeapObject {
    // vega_debug_stack_roots(shadow_stack_pointer);
    let layout = unsafe { info_table.layout.boxed };

    // TODO: do something different for large objects
    // There are two aspects to this: If an object is too large to fit in a block,
    // we need to put it in some sort of special large-object space.
    // But if it only takes up *most* of a block, we should give it its own block
    // (with a special info table so the GC only re-links the block without copying anything)
    // and then keep using the current block for other allocations

    assert!(HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes < BLOCK_SIZE);

    let object_pointer = allocate_mutator(
        thread_state,
        HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes,
    );

    let header = Header::new(info_table, GenerationIndex::MINOR);
    debug_assert_eq!(header.generation(), GenerationIndex::MINOR);
    unsafe {
        HeapObject::set_header_unsynchronized(object_pointer, header);
    }
    object_pointer
}

/// SAFETY: This assumes that array_info_table points to a valid array info table (with object_type = Array)
/// If the element type of this array constains boxed pointers, ALL the elements of the array must be written to
/// before the next garbage collection. Otherwise the GC will try to follow uninitialized pointers.
///
/// If you need an array that can survive across a garbage collection, try [allocate_zero_initialized_array]
pub unsafe fn allocate_uninitialized_array(
    thread_state: &mut ThreadState,
    array_info_table: &'static InfoTable,
    length_in_elements: usize,
) -> *mut ArrayHeapObject {
    let stride_in_bytes = unsafe { array_info_table.layout.array.element_stride_in_bytes };
    let size_in_bytes = length_in_elements * stride_in_bytes;

    let object_pointer =
        allocate_mutator(thread_state, size_of::<ArrayHeapObject>() + size_in_bytes)
            as *mut ArrayHeapObject;

    let header = Header::new(array_info_table, GenerationIndex::MINOR);
    unsafe {
        HeapObject::set_header_unsynchronized(ArrayHeapObject::as_base(object_pointer), header);
        (*object_pointer).length = length_in_elements;
    }
    object_pointer
}

/// See [allocate_uninitialized_array]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_uninitialized_array(
    thread_state: &mut ThreadState,
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut HeapObject {
    let object_pointer: *mut ArrayHeapObject =
        unsafe { allocate_uninitialized_array(thread_state, array_info_table, size_in_elements) };
    ArrayHeapObject::as_base(object_pointer)
}

/// SAFETY: The resulting array is safe insofar that the garbage collector can safely traverse it, even if it contains boxed
/// pointers and in that there will not be any real uninitialized memory in it. (unlike vega_allocate_uninitialized_array)
/// However, the resulting bit pattern might not map onto a legal value for the actual vega type of the elements,
/// so *accessing* any of the elements of this array is generally *NOT* safe.
///
/// Also, this assumes that array_info_table points to a valid array info table (with object_type = Array)
pub unsafe fn allocate_zero_initialized_array(
    thread_state: &mut ThreadState,
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut ArrayHeapObject {
    let array =
        unsafe { allocate_uninitialized_array(thread_state, array_info_table, size_in_elements) };
    let size_in_bytes =
        size_in_elements * unsafe { array_info_table.layout.array.element_stride_in_bytes };
    unsafe {
        libc::memset(
            ArrayHeapObject::contents(array) as *mut c_void,
            0,
            size_in_bytes,
        )
    };
    array
}

/// See [allocate_zero_initialized_array]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_zero_initialized_array(
    thread_state: &mut ThreadState,
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut HeapObject {
    let array = unsafe {
        allocate_zero_initialized_array(thread_state, array_info_table, size_in_elements)
    };
    ArrayHeapObject::as_base(array)
}
