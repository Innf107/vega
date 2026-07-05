// This parses the LLVM stack map format described at https://llvm.org/docs/StackMaps.html#stack-map-format

use std::{cell::OnceCell, collections::HashMap, ptr::addr_of};

unsafe extern "C" {
    unsafe static __LLVM_STACKMAPS: LLVMStackMap;
}

// This isn't *actually* mutable, we just need to initialize it once at the start, but it will never be mutated after that.
static mut STACK_MAP: OnceCell<HashMap<usize, StackMapEntry>> = OnceCell::new();

pub struct StackMapEntry {}

// SAFETY: initialize_stack_roots must have been called before
pub unsafe fn get_stack_map() -> &'static HashMap<usize, StackMapEntry> {
    #[allow(static_mut_refs)]
    unsafe {
        STACK_MAP.get().unwrap_unchecked()
    }
}

pub fn initialize_stack_roots() {
    let version = unsafe { __LLVM_STACKMAPS.header.version };
    let num_functions = unsafe { __LLVM_STACKMAPS.num_functions };
    let num_constants = unsafe { __LLVM_STACKMAPS.num_constants };
    let num_records = unsafe { __LLVM_STACKMAPS.num_records };
    println!(
        "stack map version: {version}, num_functions: {num_functions}, num_constants: {num_constants}, num_records: {num_records}"
    );

    let mut stack_map = HashMap::new();

    let mut current_stack_size_record_pointer =
        unsafe { addr_of!(__LLVM_STACKMAPS).add(1) as *const StkSizeRecord };
    let mut current_record_pointer = unsafe {
        addr_of!(__LLVM_STACKMAPS)
            .add(1)
            .byte_add(__LLVM_STACKMAPS.num_functions as usize * size_of::<StkSizeRecord>())
            .byte_add(__LLVM_STACKMAPS.num_constants as usize * size_of::<u64>())
            as *const StkMapRecordPrefix
    };
    let mut current_record_index = 0;
    for _record_index in 0..unsafe { __LLVM_STACKMAPS.num_records } {
        // If we reached the end of all records for this function, we continue to the next.
        // This is a while loop in case any functions contain 0 records and will need to be skipped immediately
        while current_record_index >= unsafe { (*current_stack_size_record_pointer).record_count } {
            current_record_index = 0;
            current_stack_size_record_pointer = unsafe { current_stack_size_record_pointer.add(1) };
        }
        let absolute_instruction_pointer = unsafe {
            (*current_stack_size_record_pointer).function_address
                + ((*current_record_pointer).instruction_offset as u64)
        };

        let entry = StackMapEntry {};

        stack_map.insert(absolute_instruction_pointer as usize, entry);


        let record_count_for_this_function = unsafe { (*current_stack_size_record_pointer).record_count };
        let function_address = unsafe {(*current_stack_size_record_pointer).function_address};
        println!("inserting entry for IP {absolute_instruction_pointer} (record index {current_record_index}/{record_count_for_this_function}): function address: {function_address}");


        current_record_index += 1;
        // We need to align some intermediate locations to increment the current record pointer here
        unsafe {
            let unaligned_suffix_pointer = current_record_pointer
                .byte_add(size_of::<StkMapRecordPrefix>())
                .byte_add((*current_record_pointer).num_locations as usize * size_of::<Location>())
                as *const StkMapRecordSuffix;
            let suffix_pointer = unaligned_suffix_pointer
                .byte_add((unaligned_suffix_pointer as *const u8).align_offset(8));
            let unaligned_end_pointer = suffix_pointer
                .byte_add(size_of::<StkMapRecordSuffix>())
                .byte_add((*suffix_pointer).num_live_outs as usize * size_of::<LiveOuts>())
                as *const StkMapRecordPrefix;
            current_record_pointer = unaligned_end_pointer
                .byte_add((unaligned_end_pointer as *const u8).align_offset(8));
        }
    }

    #[allow(static_mut_refs)]
    unsafe {
        STACK_MAP
            .set(stack_map)
            .unwrap_or_else(|_| panic!("stack root map initialized more than once"))
    };
}

#[repr(C)]
struct LLVMStackMap {
    pub header: Header,
    pub num_functions: u32,
    pub num_constants: u32,
    pub num_records: u32,
}

impl LLVMStackMap {}

struct StkSizeRecord {
    function_address: u64,
    stack_size: u64,
    record_count: u64,
}

#[repr(C)]
struct Header {
    version: u8,
    _reserved1: u8,
    _reserved2: u16,
}

#[repr(C)]
struct StkMapRecordPrefix {
    patch_point_id: u64,
    instruction_offset: u32,
    _reserved: u16,
    num_locations: u16,
}
struct StkMapRecordSuffix {
    _padding: u16,
    num_live_outs: u16,
}

#[repr(C)]
struct Location {
    kind: u8,
    _reserved: u8,
    location_size: u16,
    dwarf_regnum: u16,
    _reserved2: u16,
    offset_or_small_constant: i32,
}

#[repr(C)]
struct LiveOuts {
    dwarf_regnum: u16,
    _reserved: u8,
    size_in_bytes: u8,
}
