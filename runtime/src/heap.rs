use std::slice;

/// The type of Vega heap objects.
/// The fields of this type only contain the heap header
#[repr(C)]
pub struct HeapObject {
    info_table: *const InfoTable,
}
impl HeapObject {
    pub const HEADER_SIZE_IN_BYTES: usize = size_of::<HeapObject>();

    pub fn from_data(object: *const u8) -> *const HeapObject {
        unsafe { object.byte_sub(HeapObject::HEADER_SIZE_IN_BYTES) as *const HeapObject }
    }

    pub fn data(object: *const HeapObject) -> *mut u8 {
        unsafe { object.byte_add(HeapObject::HEADER_SIZE_IN_BYTES) as *mut u8 }
    }
}

#[repr(C)]
pub struct InfoTable {
    object_type: ObjectType,
    layout: Layout,
}

#[repr(C)]
pub union Layout {
    boxed: BoxedLayout,
    array: ArrayLayout,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct BoxedLayout {
    /// The full size of the object data including boxed pointers
    size_in_bytes: usize,
    /// The number of boxed pointers in the layout. These are always the first elements
    boxed_count: usize,
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
    size_in_elements: usize,
    element_stride_in_bytes: usize,
    element_boxed_count: usize,
}

#[repr(C)]
pub enum ObjectType {
    Boxed,
    Array,
}

/// Allocate a box for the given info table and return a pointer to the (uninitialized) *data*.
/// To access the heap object header, use [HeapObject::from_data].
// TODO: eventually we will want to inline this directly into the generated code but
// it's simpler to keep it as a rust function for now
// SAFETY: this assumes that info_table points to a boxed heap object info table
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_allocate_boxed(info_table: *const InfoTable) -> *mut u8 {
    let layout = unsafe { (*info_table).layout.boxed };

    println!(
        "size: {}, boxed: {}",
        layout.size_in_bytes, layout.boxed_count
    );

    unsafe { libc::malloc(HeapObject::HEADER_SIZE_IN_BYTES + layout.size_in_bytes) as *mut u8 }
}

