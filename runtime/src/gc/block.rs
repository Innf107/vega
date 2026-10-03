use std::{debug_assert_matches, ptr::NonNull};

use crate::heap::{Header, HeapObject};
use std::fmt::Debug;

pub const BLOCK_SIZE: usize = 4096;
const BLOCK_DESCRIPTOR_MASK: usize = !(BLOCK_SIZE - 1);

pub struct BlockDescriptor {
    pub next: Option<BlockPointer>,
    pub previous: Option<BlockPointer>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BlockPointer {
    pub(super) contents: NonNull<u8>,
}
impl BlockPointer {
    pub fn descriptor(&self) -> *mut BlockDescriptor {
        // The descriptor is stored immediately at the start of the block
        self.contents.cast::<BlockDescriptor>().as_ptr()
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

    // Iterate over the heap objects in this block pointer.
    // This will only work correctly if the block is either completely filled
    // (such that there wouldn't be any space left for another header)
    // or ends in a Descriptor::end_of_block_header()
    pub unsafe fn iter_heap_objects(self) -> HeapObjectIterator {
        HeapObjectIterator {
            current: self.first_heap_object_pointer(),
            limit: self.allocation_limit(),
        }
    }

    pub fn allocation_limit(self) -> *mut HeapObject {
        unsafe { self.contents.byte_add(BLOCK_SIZE).as_ptr() as *mut HeapObject }
    }

    // Remove a block descriptor from its current list
    pub fn unlink(self) {
        unsafe {
            let next = (*self.descriptor()).next;
            let previous = (*self.descriptor()).previous;
            match next {
                None => {}
                Some(next_pointer) => (*next_pointer.descriptor()).previous = previous,
            }
            match previous {
                None => {}
                Some(previous_pointer) => (*previous_pointer.descriptor()).next = next,
            }

            (*self.descriptor()).next = None;
            (*self.descriptor()).previous = None;
        }
    }
}
impl Debug for BlockPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.contents.fmt(f)
    }
}

pub struct HeapObjectIterator {
    current: *mut HeapObject,
    limit: *mut HeapObject,
}
impl Iterator for HeapObjectIterator {
    type Item = *mut HeapObject;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.limit.byte_offset_from(self.current) < (size_of::<Header>() as isize) {
                return None;
            } else if HeapObject::header(self.current).is_end_of_block_header() {
                return None;
            } else {
                let heap_object: *mut HeapObject = self.current;
                self.current = self.current.byte_add(HeapObject::total_stride(heap_object));
                Some(heap_object)
            }
        }
    }
}

pub struct NonEmptyBlockList {
    first: BlockPointer,
    last: BlockPointer,
    length_in_blocks: usize,
}
impl NonEmptyBlockList {
    pub fn append(&mut self, block: BlockPointer) {
        let descriptor = block.descriptor();
        unsafe {
            debug_assert_matches!((*descriptor).next, None);
            debug_assert_matches!((*descriptor).previous, None);

            let previous = self.last;
            debug_assert_matches!((*previous.descriptor()).next, None);

            (*descriptor).previous = Some(previous);

            (*previous.descriptor()).next = Some(block);

            self.last = previous;
        }
        self.length_in_blocks += 1;
    }
}

pub struct BlockList {
    contents: Option<NonEmptyBlockList>,
}
impl BlockList {
    pub const fn new() -> Self {
        BlockList { contents: None }
    }

    pub fn append(&mut self, block: BlockPointer) {
        unsafe {
            debug_assert_matches!((*block.descriptor()).previous, None);
            debug_assert_matches!((*block.descriptor()).next, None);
        }
        match self.contents {
            Some(ref mut non_empty_block_list) => non_empty_block_list.append(block),
            None => {
                self.contents = Some(NonEmptyBlockList {
                    first: block,
                    last: block,
                    length_in_blocks: 1,
                })
            }
        }
    }
    pub fn pop_back(&mut self) -> Option<BlockPointer> {
        match self.contents {
            None => None,
            Some(ref mut non_empty_block_list) => {
                let last_block = non_empty_block_list.last;
                debug_assert_matches!(unsafe { (*last_block.descriptor()).next }, None);
                match unsafe { (*last_block.descriptor()).previous } {
                    None => {
                        // This is the only block in the list
                        debug_assert_eq!(non_empty_block_list.first, non_empty_block_list.last);

                        self.contents = None;
                        Some(last_block)
                    }
                    Some(previous) => {
                        unsafe {
                            debug_assert_eq!((*previous.descriptor()).next, Some(last_block));

                            (*previous.descriptor()).next = None;
                            (*last_block.descriptor()).previous = None;
                        }

                        Some(last_block)
                    }
                }
            }
        }
    }
}
