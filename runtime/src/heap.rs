use std::{
    ffi::c_void,
    ptr::{addr_of, null},
};

use crate::either::Either;

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
                let heap_object_pointer = data_pointer.byte_sub(HeapObject::HEADER_SIZE_IN_BYTES);

                heap_object_pointer as *const HeapObject
            }
        }
    }

    pub fn data(object: *const HeapObject) -> *mut u8 {
        unsafe { object.byte_add(HeapObject::HEADER_SIZE_IN_BYTES) as *mut u8 }
    }

    // SAFETY: the heap object pointer needs to be either a null pointer or a pointer to a valid heap object
    pub unsafe fn header(object: *const HeapObject) -> Header {
        if object == null() {
            STATIC_NULL_HEADER
        } else {
            unsafe { (*object).header }
        }
    }

    pub unsafe fn as_array_object_unchecked(object: *const HeapObject) -> *const ArrayHeapObject {
        object as *const ArrayHeapObject
    }

    /// SAFETY: the pointer needs to point to a valid heap object (including forward pointers)
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
}
pub struct ArrayHandle {
    pub object: *const ArrayHeapObject,
    pub layout: &'static ArrayLayout,
}
impl ArrayHandle {
    pub fn length(&self) -> usize {
        unsafe { (*(self.object)).length }
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
63                  3        2            1   0
┌───────────────────┬────────┬────────────┬───┐
│info table pointer │ unused │ generation │ 0 │
└───────────────────┴────────┴────────────┴───┘
```
Forward pointer:
```rs
63                3        1
┌─────────────────┬────────┬───┐
│ forward pointer │ unused │ 1 │
└─────────────────┴────────┴───┘
```
*/

#[derive(Clone, Copy)]
pub struct Header {
    raw_pointer_with_tags: *const InfoTable,
}
impl Header {
    pub fn new(info_table: &'static InfoTable, generation: Generation) -> Self {
        let raw_pointer_with_tags = (info_table as *const InfoTable)
            .map_addr(|address| address | (generation.as_usize() << 1));
        Header {
            raw_pointer_with_tags,
        }
    }

    pub fn info_table_or_forward_pointer(self) -> Either<&'static InfoTable, ForwardPointer> {
        let actual_pointer: *const InfoTable = self
            .raw_pointer_with_tags
            .map_addr(|address| address & !0b111);
        // The last bit indicates if this is a forward pointer
        if self.raw_pointer_with_tags.addr() & 1 == 1 {
            Either::Right(ForwardPointer {
                to_space_allocation: actual_pointer as *const HeapObject,
            })
        } else {
            // If this is a real info table pointer, then we can assume that it is statically allocated and will live forever
            // so it is definitely safe to convert it to a &'static InfoTable
            Either::Left(unsafe { &*actual_pointer })
        }
    }

    pub fn generation(&self) -> Generation {
        if self.raw_pointer_with_tags.addr() & 0b10 == 0 {
            Generation::MINOR
        } else {
            Generation::MAJOR
        }
    }
}

#[derive(Clone, Copy)]
pub struct Generation {
    is_major: bool,
}
impl Generation {
    pub fn as_usize(self) -> usize {
        if self.is_major { 1 } else { 0 }
    }
    pub fn is_major(self) -> bool {
        self.is_major
    }
    pub const MAJOR: Self = Generation { is_major: true };
    pub const MINOR: Self = Generation { is_major: false };
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
    /// The full size of the object data including boxed pointers
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
    raw_pointer_with_tags: addr_of!(STATIC_NULL_INFO_TABLE),
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

/// Allocate a box for the given info table and return a pointer to the (uninitialized) *data*.
/// To access the heap object header, use [HeapObject::from_data].
// TODO: eventually we will want to inline this directly into the generated code but
// it's simpler to keep it as a rust function for now
// SAFETY: this assumes that info_table points to a boxed heap object info table
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_boxed(info_table: &'static InfoTable) -> *mut u8 {
    let layout = unsafe { info_table.layout.boxed };

    let object_pointer = unsafe {
        libc::malloc(HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes) as *mut HeapObject
    };

    let header = Header::new(info_table, Generation::MINOR);
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
    array_info_table: &'static InfoTable,
    length_in_elements: usize,
) -> *mut ArrayHeapObject {
    let stride_in_bytes = unsafe { (*array_info_table).layout.array.element_stride_in_bytes };
    let size_in_bytes = length_in_elements * stride_in_bytes;

    let object_pointer =
        unsafe { libc::malloc(size_of::<ArrayHeapObject>() + size_in_bytes as usize) }
            as *mut ArrayHeapObject;

    let header = Header::new(array_info_table, Generation::MINOR);
    unsafe { (*object_pointer).base = HeapObject { header } };
    
    unsafe { (*object_pointer).length = length_in_elements };
    object_pointer
}

/// See [allocate_uninitialized_array]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_uninitialized_array(
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut u8 {
    let object_pointer =
        unsafe { allocate_uninitialized_array(array_info_table, size_in_elements) };
    HeapObject::data(ArrayHeapObject::as_base(object_pointer))
}

/// SAFETY: The resulting array is safe insofar that the garbage collector can safely traverse it, even if it contains boxed
/// pointers and in that there will not be any real uninitialized memory in it. (unlike vega_allocate_uninitialized_array)
/// However, the resulting bit pattern might not map onto a legal value for the actual vega type of the elements,
/// so *accessing* any of the elements of this array is generally *NOT* safe.
///
/// Also, this assumes that array_info_table points to a valid array info table (with object_type = Array)
pub unsafe fn allocate_zero_initialized_array(
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut ArrayHeapObject {
    let array = unsafe { allocate_uninitialized_array(array_info_table, size_in_elements) };
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
    array_info_table: &'static InfoTable,
    size_in_elements: usize,
) -> *mut u8 {
    let array = unsafe { allocate_zero_initialized_array(array_info_table, size_in_elements) };
    HeapObject::data(ArrayHeapObject::as_base(array))
}
