use std::{
    ffi::c_void,
    hint::cold_path,
    ptr::{addr_of, null, null_mut},
};

use crate::{
    either::Either,
    gc::{
        Generation, NURSERY,
        block::{BLOCK_SIZE, BlockPointer},
        block_allocator,
    },
    tagged_pointer::TaggedPointer,
    thread_state::ThreadState,
};
use std::fmt::Debug;

pub const HEAP_ALIGNMENT: usize = 8;

pub fn round_up_to_heap_alignment(value: usize) -> usize {
    let aligned_down = value & !(HEAP_ALIGNMENT - 1);
    if value == aligned_down {
        aligned_down
    } else {
        aligned_down + HEAP_ALIGNMENT
    }
}

/// The type of Vega heap objects.
/// The fields of this type only contain the heap header
#[repr(C)]
pub struct HeapObject {
    header: Header,
}
impl HeapObject {
    pub const HEADER_SIZE_IN_BYTES: usize = size_of::<HeapObject>();

    // SAFETY: the pointer needs to be either a null pointer or a valid pointer pointing to
    // the data section of a valid heap object. In particular it must *not* point to a forward pointer object.
    pub unsafe fn from_data(data_pointer: *const u8) -> *const HeapObject {
        if data_pointer == null() {
            null()
        } else {
            unsafe {
                let heap_object_pointer =
                    data_pointer.byte_sub(HeapObject::HEADER_SIZE_IN_BYTES) as *const HeapObject;

                // The argument must not be a forward pointer
                debug_assert!(matches!(
                    HeapObject::header(heap_object_pointer).info_table_or_forward_pointer(),
                    Either::Left(_)
                ));

                heap_object_pointer
            }
        }
    }

    pub fn data(object: *const HeapObject) -> *mut u8 {
        unsafe { object.byte_add(HeapObject::HEADER_SIZE_IN_BYTES) as *mut u8 }
    }

    // A textual description of this heap object's object type for use in debugging.
    //
    // SAFETY: the pointer must point to a valid heap object or forward pointer or be a null pointer.
    pub unsafe fn object_type_description(object: *const HeapObject) -> &'static str {
        match unsafe { HeapObject::as_handle(object) } {
            HeapObjectHandle::Boxed(_) => "Boxed",
            HeapObjectHandle::Array(_) => "Array",
            HeapObjectHandle::StaticArray(_) => "StaticArray",
            HeapObjectHandle::ForwardPointer(_) => "ForwardPointer",
            HeapObjectHandle::Null => "Null",
        }
    }

    // SAFETY: the heap object pointer needs to be either a null pointer or a pointer to a valid heap object
    pub unsafe fn header(object: *const HeapObject) -> Header {
        if object == null() {
            STATIC_NULL_HEADER
        } else {
            unsafe { (*object).header }
        }
    }

    // SAFETY: This function must not race with any other accesses to the header.
    // TODO: This is really only safe in a single-threaded context and we should get
    // rid of it once we parallelize the GC
    pub unsafe fn set_header_unsynchronized(object: *mut HeapObject, header: Header) {
        debug_assert!(object != null_mut());
        unsafe { (*object).header = header }
    }

    pub unsafe fn override_with_forward_pointer_unsynchronized(
        object: *mut HeapObject,
        pointer: ForwardPointer,
    ) {
        unsafe { (*object).header = Header::new_forward_pointer(pointer) }
    }

    pub unsafe fn as_array_object_unchecked(object: *const HeapObject) -> *const ArrayHeapObject {
        object as *const ArrayHeapObject
    }

    /// SAFETY: the pointer needs to point to a valid heap object (including forward pointers and null)
    pub unsafe fn as_handle(object: *const HeapObject) -> HeapObjectHandle {
        let header = unsafe { Self::header(object) };
        match header.info_table_or_forward_pointer() {
            Either::Right(forward_pointer) => HeapObjectHandle::ForwardPointer(forward_pointer),
            Either::Left(info_table) => match info_table.object_type {
                ObjectType::Boxed => {
                    let layout = unsafe { &info_table.layout.boxed };
                    HeapObjectHandle::Boxed(BoxedHandle { object, layout })
                }
                ObjectType::Array => {
                    let array_object = unsafe { HeapObject::as_array_object_unchecked(object) };
                    let layout = unsafe { &info_table.layout.array };
                    HeapObjectHandle::Array(ArrayHandle {
                        object: array_object,
                        layout,
                    })
                }
                ObjectType::StaticArray => {
                    let array_object = unsafe { HeapObject::as_array_object_unchecked(object) };
                    let layout = unsafe { &info_table.layout.array };
                    HeapObjectHandle::StaticArray(StaticArrayHandle {
                        object: array_object,
                        layout,
                    })
                }
                ObjectType::Null => HeapObjectHandle::Null,
            },
        }
    }

    // SAFETY: the pointer must point to a valid heap object.
    // This will panic if passed a forward pointer
    pub unsafe fn total_stride(object: *const HeapObject) -> usize {
        match unsafe { HeapObject::as_handle(object) } {
            HeapObjectHandle::Boxed(boxed_handle) => boxed_handle.stride(),
            HeapObjectHandle::Array(array_handle) => array_handle.stride(),
            HeapObjectHandle::StaticArray(static_array_handle) => static_array_handle.stride(),
            HeapObjectHandle::Null => {
                // There isn't really a *good* reason to call total_size on something that could be Null but there might eventually
                // be an edge case where this is better than panicking
                round_up_to_heap_alignment(HeapObject::HEADER_SIZE_IN_BYTES)
            }
            HeapObjectHandle::ForwardPointer(forward_pointer) => {
                panic!("HeapObject::total_size called on a forward pointer: {forward_pointer:?}")
            }
        }
    }
}

/// A HeapObjectHandle is a more rust-friendly view onto a heap object.
/// In particular, this will allow certain operations only on certain kinds of heap objects
pub enum HeapObjectHandle {
    Boxed(BoxedHandle),
    Array(ArrayHandle),
    StaticArray(StaticArrayHandle),
    ForwardPointer(ForwardPointer),
    Null,
}
impl Debug for ForwardPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_space_allocation.fmt(f)
    }
}

pub struct BoxedHandle {
    pub object: *const HeapObject,
    pub layout: &'static BoxedLayout,
}
impl BoxedHandle {
    /// Return a mutable pointer to the boxed element at the given index.
    /// SAFETY: the index must be in (0, self.layout.boxed_count)
    pub unsafe fn boxed_element(&self, index: usize) -> *mut *const u8 {
        debug_assert!(index < self.layout.boxed_count);
        // In values at-rest, boxed elements are stored first.
        // See Note [At-rest vs in-flight] in src/Vega/Compilation/LLVM/Layout.hs
        let start_of_boxed_elements = HeapObject::data(self.object) as *mut *const u8;
        unsafe { start_of_boxed_elements.add(index) }
    }

    // The full size of this heap object including the header, rounded up to heap alignment
    pub fn stride(&self) -> usize {
        round_up_to_heap_alignment(HeapObject::HEADER_SIZE_IN_BYTES + self.layout.size_in_bytes)
    }
}
pub struct ArrayHandle {
    pub object: *const ArrayHeapObject,
    pub layout: &'static ArrayLayout,
}
impl ArrayHandle {
    pub fn length(&self) -> usize {
        unsafe { (*(self.object)).length }
    }

    // The total size of this heap object including the object header, rounded up to heap alignment
    pub fn stride(&self) -> usize {
        let length_counter_size = size_of::<usize>();
        round_up_to_heap_alignment(
            HeapObject::HEADER_SIZE_IN_BYTES
                + length_counter_size
                + self.length() * self.layout.element_stride_in_bytes,
        )
    }

    pub unsafe fn boxed_element(&self, element_index: usize, boxed_index: usize) -> *mut *const u8 {
        debug_assert!(element_index < self.length());
        debug_assert!(boxed_index < self.layout.element_boxed_count);

        let content_pointer = ArrayHeapObject::contents(self.object);
        let element_pointer = unsafe {
            content_pointer.byte_add(element_index * self.layout.element_stride_in_bytes)
                as *mut *const u8
        };
        // Values at-rest store their boxed elements first, so we can treat the element pointer as
        // the pointer to the first boxed element.
        // See Note [At-rest vs in-flight] in src/Vega/Compilation/LLVM/Layout.hs
        unsafe { element_pointer.add(boxed_index) }
    }
}

pub struct StaticArrayHandle {
    pub object: *const ArrayHeapObject,
    pub layout: &'static ArrayLayout,
}

impl StaticArrayHandle {
    pub fn length(&self) -> usize {
        unsafe { (*(self.object)).length }
    }

    // The total size of this heap object including the object header, rounded up to heap alignment
    pub fn stride(&self) -> usize {
        let length_counter_size = size_of::<usize>();
        round_up_to_heap_alignment(
            HeapObject::HEADER_SIZE_IN_BYTES
                + length_counter_size
                + self.length() * self.layout.element_stride_in_bytes,
        )
    }

    pub unsafe fn boxed_element(&self, element_index: usize, boxed_index: usize) -> *mut *const u8 {
        debug_assert!(element_index < self.length());
        debug_assert!(boxed_index < self.layout.element_boxed_count);

        let content_pointer = ArrayHeapObject::contents(self.object);
        let element_pointer = unsafe {
            content_pointer.byte_add(element_index * self.layout.element_stride_in_bytes)
                as *mut *const u8
        };
        // Values at-rest store their boxed elements first, so we can treat the element pointer as
        // the pointer to the first boxed element.
        // See Note [At-rest vs in-flight] in src/Vega/Compilation/LLVM/Layout.hs
        unsafe { element_pointer.add(boxed_index) }
    }
}

pub struct ForwardPointer {
    pub to_space_allocation: *const HeapObject,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct InfoTable {
    pub object_type: ObjectType,
    pub layout: Layout,
}

/**
Layout:

Normal heap object:
```rs
64                  3          2            1   0
┌───────────────────┬──────────┬────────────┬───┐
│info table pointer │ (unused) │ generation │ 0 │
└───────────────────┴──────────┴────────────┴───┘
```
Forward pointer:
```rs
64                  3                       1   0
┌───────────────────┬───────────────────────┬───┐
│ forward pointer   │ (unused)              │ 1 │
└───────────────────┴───────────────────────┴───┘
```
*/

const FORWARD_POINTER_TAG: u8 = 0;
const GENERATION_TAG: u8 = 1;

#[derive(Clone, Copy)]
pub struct Header {
    info_table_pointer_with_tags: TaggedPointer<InfoTable, HEAP_ALIGNMENT>,
}
impl Header {
    pub fn new(info_table: &'static InfoTable, generation: GenerationIndex) -> Self {
        let info_table_pointer_with_tags = TaggedPointer::new(info_table as *const InfoTable)
            .set_tag::<GENERATION_TAG>(generation.is_major());
        Self {
            info_table_pointer_with_tags,
        }
    }
    pub fn new_forward_pointer(pointer: ForwardPointer) -> Self {
        let info_table_pointer_with_tags =
            TaggedPointer::new(pointer.to_space_allocation as *const InfoTable)
                .set_tag::<FORWARD_POINTER_TAG>(true);
        Self {
            info_table_pointer_with_tags,
        }
    }
    pub const fn end_of_block_header() -> Self {
        Header {
            info_table_pointer_with_tags: TaggedPointer::new_without_assertion(null()),
        }
    }
    pub fn is_end_of_block_header(&self) -> bool {
        self.info_table_pointer_with_tags.pointer().is_null()
    }
    pub fn info_table_or_forward_pointer(self) -> Either<&'static InfoTable, ForwardPointer> {
        let actual_pointer = self.info_table_pointer_with_tags.pointer();
        // The last bit indicates if this is a forward pointer
        if self
            .info_table_pointer_with_tags
            .get_tag::<FORWARD_POINTER_TAG>()
        {
            Either::Right(ForwardPointer {
                to_space_allocation: actual_pointer as *const HeapObject,
            })
        } else {
            // If this is a real info table pointer, then we can assume that it is statically allocated and will live forever
            // so it is definitely safe to convert it to a &'static InfoTable
            Either::Left(unsafe { &*actual_pointer })
        }
    }

    pub fn generation(self) -> GenerationIndex {
        if self
            .info_table_pointer_with_tags
            .get_tag::<GENERATION_TAG>()
        {
            GenerationIndex::MINOR
        } else {
            GenerationIndex::MAJOR
        }
    }
    pub fn set_generation(self, generation: GenerationIndex) -> Self {
        Self {
            info_table_pointer_with_tags: self
                .info_table_pointer_with_tags
                .set_tag::<GENERATION_TAG>(generation.is_major()),
        }
    }
}

#[derive(Clone, Copy)]
pub struct GenerationIndex {
    is_major: bool,
}
impl GenerationIndex {
    pub fn as_usize(self) -> usize {
        if self.is_major { 1 } else { 0 }
    }
    pub fn is_major(self) -> bool {
        self.is_major
    }
    pub const MAJOR: Self = GenerationIndex { is_major: true };
    pub const MINOR: Self = GenerationIndex { is_major: false };
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union Layout {
    pub boxed: BoxedLayout,
    pub array: ArrayLayout,
    pub null: (),
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct BoxedLayout {
    /// The full size of the object data including boxed pointers (but not including the header)
    pub size_in_bytes: usize,
    /// The number of boxed pointers in the layout. These are always the first elements
    pub boxed_count: usize,
}
impl BoxedLayout {
    /// The size of the unboxed part of the layout, i.e. the size of everything that is not a boxed pointer
    pub fn unboxed_size_in_bytes(&self) -> usize {
        self.size_in_bytes - self.boxed_count * size_of::<*const u8>()
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ArrayLayout {
    pub element_stride_in_bytes: usize,
    pub element_boxed_count: usize,
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub enum ObjectType {
    Boxed,
    Array,
    // StaticArray also uses the regular ArrayLayout
    StaticArray,
    // Object type for boxed pointers that don't actually point
    // to real heap objects.
    // INVARIANT: STATIC_NULL_INFO_TABLE is the only info table with a Null tag
    Null,
}

static STATIC_NULL_INFO_TABLE: InfoTable = InfoTable {
    object_type: ObjectType::Null,
    layout: Layout { null: () },
};

const STATIC_NULL_HEADER: Header = Header {
    // It is okay to keep the tags here at 0.
    // This means that it is not a forward pointer (obviously)
    // and at the minor generation (irrelevant for a static heap object)
    info_table_pointer_with_tags: TaggedPointer::new_without_assertion(addr_of!(
        STATIC_NULL_INFO_TABLE
    )),
};

#[repr(C)]
pub struct ArrayHeapObject {
    pub base: HeapObject,
    pub length: usize,
}

impl ArrayHeapObject {
    pub fn as_base(object: *const ArrayHeapObject) -> *const HeapObject {
        object as *const HeapObject
    }
    pub fn contents(object: *const ArrayHeapObject) -> *mut u8 {
        unsafe { object.byte_add(size_of::<ArrayHeapObject>()) as *mut u8 }
    }
}

// Finish the current block and allocate a new one from the block allocator.
// This is shared between GC and mutator allocation.
// The arguments should typically be pointers to the allocation pointer and limit of their respective state objects.
#[inline]
pub fn finish_block(
    allocation_pointer: &mut *mut HeapObject,
    allocation_limit: &mut *mut HeapObject,
    target_generation: &'static Generation,
) {
    unsafe {
        // TOOD: i don't love the duplication between this and gc::allocate_for_evacuation
        let filled_block = BlockPointer::from_heap_object_pointer(*allocation_pointer);
        debug_assert!(filled_block.allocation_limit() == *allocation_limit);
        debug_assert!(
            filled_block.first_heap_object_pointer() <= *allocation_pointer
                && allocation_pointer <= allocation_limit
        );

        // We need to make sure that we clearly mark the end of this block so that
        // the heap objects can be traversed properly when scavenging
        if filled_block
            .allocation_limit()
            .offset_from(*allocation_pointer)
            >= size_of::<Header>() as isize
        {
            HeapObject::set_header_unsynchronized(
                *allocation_pointer,
                Header::end_of_block_header(),
            );
        }

        {
            let mut pending_blocks = target_generation.pending_blocks.lock().unwrap();
            pending_blocks.get_mut().append(filled_block);
        }

        let new_block = block_allocator::allocate_block();

        *allocation_pointer = new_block.first_heap_object_pointer();
        *allocation_limit = new_block.allocation_limit();
    }
}

// Allocate 'byte_count' bytes in the current allocation block.
// This does *not* include the size of a heap object header
// and the returned memory is not initialized in any way.
#[inline]
#[allow(static_mut_refs)]
pub fn allocate_generic(thread_state: &mut ThreadState, byte_count: usize) -> *mut HeapObject {
    let remaining_size_in_block = unsafe {
        thread_state
            .allocation_limit
            .offset_from(thread_state.allocation_pointer)
    };
    if remaining_size_in_block < byte_count as isize {
        cold_path();
        finish_block(
            &mut thread_state.allocation_pointer,
            &mut thread_state.allocation_limit,
            unsafe { &NURSERY },
        );
    }
    debug_assert!(
        unsafe {
            thread_state
                .allocation_limit
                .offset_from(thread_state.allocation_pointer)
        } >= byte_count as isize
    );

    let pointer = thread_state.allocation_pointer;
    thread_state.allocation_pointer =
        unsafe { thread_state.allocation_pointer.byte_add(byte_count) };
    pointer
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
) -> *mut u8 {
    // vega_debug_stack_roots(shadow_stack_pointer);
    let layout = unsafe { info_table.layout.boxed };

    // TODO: do something different for large objects
    // There are two aspects to this: If an object is too large to fit in a block,
    // we need to put it in some sort of special large-object space.
    // But if it only takes up *most* of a block, we should give it its own block
    // (with a special info table so the GC only re-links the block without copying anything)
    // and then keep using the current block for other allocations

    assert!(HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes < BLOCK_SIZE);

    let object_pointer = allocate_generic(
        thread_state,
        HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes,
    );

    let header = Header::new(info_table, GenerationIndex::MINOR);
    unsafe {
        *object_pointer = HeapObject { header };
    };
    HeapObject::data(object_pointer)
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
    let stride_in_bytes = unsafe { (*array_info_table).layout.array.element_stride_in_bytes };
    let size_in_bytes = length_in_elements * stride_in_bytes;

    let object_pointer = allocate_generic(
        thread_state,
        size_of::<ArrayHeapObject>() + size_in_bytes as usize,
    ) as *mut ArrayHeapObject;

    let header = Header::new(array_info_table, GenerationIndex::MINOR);
    unsafe { (*object_pointer).base = HeapObject { header } };

    unsafe { (*object_pointer).length = length_in_elements };
    object_pointer
}

/// See [allocate_uninitialized_array]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_uninitialized_array(
    thread_state: &mut ThreadState,
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut u8 {
    let object_pointer = unsafe {
        allocate_uninitialized_array(thread_state, array_info_table, size_in_elements)
    };
    HeapObject::data(ArrayHeapObject::as_base(object_pointer))
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
    let array = unsafe {
        allocate_uninitialized_array(thread_state, array_info_table, size_in_elements)
    };
    let size_in_bytes =
        size_in_elements * unsafe { (*array_info_table).layout.array.element_stride_in_bytes };
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
) -> *mut u8 {
    let array = unsafe {
        allocate_zero_initialized_array(thread_state, array_info_table, size_in_elements)
    };
    HeapObject::data(ArrayHeapObject::as_base(array))
}
