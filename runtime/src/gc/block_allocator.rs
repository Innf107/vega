use std::{
    io::Error,
    ptr::{NonNull, null_mut},
    sync::Mutex,
};

use libc::{MAP_ANONYMOUS, PROT_READ, PROT_WRITE, mmap};

use crate::{
    gc::block::{BLOCK_SIZE, BlockList, BlockPointer},
    heap::{Header, HeapObject},
    make_send::UnsafeMakeSend,
    settings::settings,
};

fn allocate_page_aligned_memory(size_in_bytes: usize) -> NonNull<u8> {
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
    unsafe { NonNull::new_unchecked(memory as *mut u8) }
}

struct BlockAllocator {
    free_blocks: Mutex<UnsafeMakeSend<BlockList>>,
}

static GLOBAL_BLOCK_ALLOCATOR: BlockAllocator = BlockAllocator {
    free_blocks: Mutex::new(UnsafeMakeSend::new(BlockList::new())),
};

#[allow(static_mut_refs)]
pub fn allocate_block() -> BlockPointer {
    let mut free_blocks_guard = GLOBAL_BLOCK_ALLOCATOR.free_blocks.lock().unwrap();
    let free_blocks = unsafe { free_blocks_guard.get_mut() };

    match free_blocks.pop_back() {
        Some(block) => block,
        None => {
            // We could in principle release the lock here while we allocate new blocks, but if we did, that would only
            // lead to more memory than necessary being allocated by any racing threads.
            let underlying_memory =
                allocate_page_aligned_memory(settings().block_allocation_batch_size * BLOCK_SIZE);

            let mut new_block_list = BlockList::new();
            for i in 0..settings().block_allocation_batch_size {
                let pointer_to_start_of_block =
                    unsafe { underlying_memory.byte_add(i * BLOCK_SIZE) };
                let block = BlockPointer {
                    contents: pointer_to_start_of_block,
                };

                unsafe {
                    HeapObject::set_header_unsynchronized(
                        block.first_heap_object_pointer(),
                        Header::end_of_block_header(),
                    );
                }

                new_block_list.append(block);
            }

            free_blocks.concat(new_block_list);

            free_blocks
                .pop_back()
                .expect("free_blocks is empty after allocating new blocks from the OS")
        }
    }
}

// SAFETY: The freed block must not already be free
// and there cannot be any racing accesses to its BlockList
// while this function is called.
pub unsafe fn free_block(block: BlockPointer) {
    block.unlink();

    let mut free_blocks_guard = GLOBAL_BLOCK_ALLOCATOR.free_blocks.lock().unwrap();
    unsafe { free_blocks_guard.get_mut().append(block) };
}
