use std::{
    io::Error,
    ptr::{NonNull, null, null_mut},
};

use libc::{_SC_PAGESIZE, MAP_ANONYMOUS, PROT_READ, PROT_WRITE, mmap, sysconf};

use crate::{heap::HeapObject, primitive::vega_errno};

pub const BLOCK_SIZE: usize = 4096;
const BLOCK_DESCRIPTOR_MASK: usize = !(BLOCK_SIZE - 1);

pub struct BlockDescriptor {
    pub next: Option<BlockPointer>,
}

#[derive(Clone, Copy)]
pub struct BlockPointer {
    contents: NonNull<u8>,
}
impl BlockPointer {
    pub fn descriptor(self) -> *mut BlockDescriptor {
        // The descriptor is stored immediately at the start of the block
        self.contents.as_ptr() as *mut BlockDescriptor
    }
    /// SAFETY: the pointer must point to a valid dynamically allocated heap object.
    /// In particular, passing a statically allocated heap object (like a static array), a pointer to the null object
    /// or a null pointer is *not* valid.
    pub unsafe fn from_heap_object_pointer(heap_object: *const HeapObject) -> Self {
        // Blocks are always aligned to BLOCK_SIZE, so we can mask off the last few bits
        // to get a pointer to the start of the block
        let content_ptr =
            heap_object.map_addr(|address| address & BLOCK_DESCRIPTOR_MASK) as *mut u8;
        let contents = unsafe { NonNull::new_unchecked(content_ptr) };
        BlockPointer { contents }
    }

    /// Return a pointer to the space for the first heap object.
    /// There is *NOT* necessarily a valid heap object there.
    ///
    /// In particular, if this block has just been allocated, the
    /// "object" this points to is just going to be uninitialized memory.
    pub fn first_heap_object_pointer(self) -> *mut HeapObject {
        // BlockDescriptor is at least 8 byte aligned, so this will give us
        // an 8 byte aligned pointer (which is what we need for a heap object)
        unsafe {
            self.contents
                .byte_add(size_of::<BlockDescriptor>())
                .as_ptr() as *mut HeapObject
        }
    }
}

#[derive(Clone, Copy)]
pub struct BlockList {
    first: BlockPointer,
    last: BlockPointer,
}
impl BlockList {
    /// Return a dummy block list that is technically initialized, but not actually valid.
    /// SAFETY: The result must be overridden by something real before
    /// calling any functions on it.
    pub const unsafe fn dummy() -> Self {
        BlockList {
            first: BlockPointer {
                contents: NonNull::dangling(),
            },
            last: BlockPointer {
                contents: NonNull::dangling(),
            },
        }
    }
}

pub fn allocate_page_aligned_memory(size_in_bytes: usize) -> *const u8 {
    let memory = unsafe {
        mmap(
            null_mut(),
            size_in_bytes,
            PROT_READ | PROT_WRITE,
            MAP_ANONYMOUS,
            -1,
            0,
        )
    };
    if memory.addr() as isize == -1 {
        panic!("memory allocation failed: {}", Error::last_os_error());
    }
    memory as *const u8
}

pub fn allocate_block() -> BlockPointer {
    let block_memory = allocate_page_aligned_memory(BLOCK_SIZE);
    todo!()
}

pub fn allocate_block_list(count: usize) -> BlockList {
    todo!()
}
