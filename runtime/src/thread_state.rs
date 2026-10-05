use crate::heap::HeapObject;

pub struct ThreadState {
    pub allocation_pointer: *mut HeapObject,
    pub allocation_limit: *mut HeapObject,
}
