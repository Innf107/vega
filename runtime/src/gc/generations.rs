use std::sync::Mutex;

use crate::{gc::block::BlockList, make_send::UnsafeMakeSend, settings::RuntimeSettings};

pub struct Nursery {
    pub used_blocks: Mutex<UnsafeMakeSend<BlockList>>,
    pub max_block_count: usize,
}

const INITIALIZED_LATER: usize = 0xBADBADBAD;

// Fields that are set to `INITIALIZED_LATER` are actually overridden a bit later by `initialize_generations`
// once we have parsed the runtime settings.
pub static mut NURSERY: Nursery = Nursery {
    used_blocks: Mutex::new(UnsafeMakeSend::new(BlockList::new())),
    max_block_count: INITIALIZED_LATER,
};

#[allow(static_mut_refs)]
pub fn nursery() -> &'static Nursery {
    // read-only accesses to the nursery are fine as long as we make sure not to
    // restrict mutable accesses to places where we know that immutable ones won't happen.
    unsafe { &NURSERY }
}

pub struct MajorHeap {
    pub used_blocks: Mutex<UnsafeMakeSend<BlockList>>,
    pub pending_blocks: Mutex<UnsafeMakeSend<BlockList>>,
    // Only used during a GC. Should be empty otherwise
    pub to_space: Mutex<UnsafeMakeSend<BlockList>>,
    pub max_block_count: usize,
}

pub static mut MAJOR_HEAP: MajorHeap = MajorHeap {
    used_blocks: Mutex::new(UnsafeMakeSend::new(BlockList::new())),
    pending_blocks: Mutex::new(UnsafeMakeSend::new(BlockList::new())),
    to_space: Mutex::new(UnsafeMakeSend::new(BlockList::new())),
    max_block_count: INITIALIZED_LATER,
};

#[allow(static_mut_refs)]
pub fn major_heap() -> &'static MajorHeap {
    unsafe { &MAJOR_HEAP }
}

pub fn initialize_generations(settings: &RuntimeSettings) {
    assert!(settings.nursery_size_in_blocks > 0);
    assert!(settings.initial_major_heap_size_in_blocks > 0);
    assert!(settings.major_heap_scaling_factor >= 1.0);
    unsafe {
        NURSERY.max_block_count = settings.nursery_size_in_blocks;
        MAJOR_HEAP.max_block_count = settings.initial_major_heap_size_in_blocks;
    }
}
