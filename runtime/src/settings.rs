pub struct RuntimeSettings {
    pub nursery_size_in_blocks: usize,
    pub initial_major_heap_size_in_blocks: usize,
    // The number of blocks to allocate from the operating system at once.
    // Larger sizes will reduce the number of mmap calls performed
    pub block_allocation_batch_size: usize,
}

pub const fn default_runtime_settings() -> RuntimeSettings {
    RuntimeSettings {
        nursery_size_in_blocks: 1024,
        initial_major_heap_size_in_blocks: 1024,
        block_allocation_batch_size: 256,
    }
}

static mut SETTINGS: RuntimeSettings = default_runtime_settings();

// Access the settings passed to the runtime at startup.
//
// This is technically only safe if it doesn't race a call to 'parse_runtime_settings'.
// Since that function is called at startup, this will never happen though.
#[allow(static_mut_refs)]
pub fn settings() -> &'static RuntimeSettings {
    unsafe { &SETTINGS }
}

pub fn parse_runtime_settings() -> &'static RuntimeSettings {
    todo!()
}
