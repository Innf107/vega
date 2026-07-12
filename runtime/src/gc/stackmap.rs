// This parses the LLVM stack map format described at https://llvm.org/docs/StackMaps.html#stack-map-format

use core::slice;
use std::{cell::OnceCell, collections::HashMap, ptr::addr_of};

unsafe extern "C" {
    unsafe static __LLVM_STACKMAPS: LLVMStackMap;
}

// This isn't *actually* mutable, we just need to initialize it once at the start, but it will never be mutated after that.
static mut STACK_MAP: OnceCell<HashMap<usize, StackMapEntry>> = OnceCell::new();

#[derive(Debug)]
pub struct StackMapEntry {
    pub relocation_pairs: Box<[RelocationPair]>,
}

#[derive(Debug)]
pub struct RelocationPair {
    pub base_pointer_offset: i32,
    pub derived_pointer_offset: i32,
    pub number_of_derived_pointers: u16,
}

// SAFETY: initialize_stack_roots must have been called before
pub unsafe fn get_stack_map() -> &'static HashMap<usize, StackMapEntry> {
    #[allow(static_mut_refs)]
    unsafe {
        STACK_MAP.get().unwrap_unchecked()
    }
}

pub fn initialize_stack_roots() {
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

        let location_pointer = unsafe { current_record_pointer.add(1) as *const Location };
        let num_locations = unsafe { (*current_record_pointer).num_locations } as usize;
        let locations = unsafe { slice::from_raw_parts(location_pointer, num_locations) };
        // locations[0] is the calling convention. We don't actually need it but it might be useful for debugging
        assert!(locations[0].kind == LocationKind::Constant);
        // locations[1] contains the flags passed to this statepoint.
        // This is usually 0, but might be 1 if we're in a GC transition
        // (i.e. if this function is a non-gc function that was called from a gc function)
        assert!(locations[1].kind == LocationKind::Constant);

        // locations[2] contains the number of deopt locations.
        // We don't use deoptimization so this should always be 0
        assert!(locations[2].kind == LocationKind::Constant);
        assert!(locations[2].offset_or_small_constant == 0);

        // The remaining locations all come in pairs
        assert!((locations.len() - 3) % 2 == 0);
        let relocation_pairs = (0..((locations.len() - 3) / 2))
            .map(|i| {
                let base_pointer_location = &locations[3 + 2 * i];
                let derived_pointer_location = &locations[3 + 2 * i + 1];

                assert!(base_pointer_location.kind == LocationKind::Indirect);
                assert!(derived_pointer_location.kind == LocationKind::Indirect);

                // There should be exactly one base pointer
                assert!(base_pointer_location.location_size == 8);

                // There may be more than one derived pointer, but the total size in bytes is divisible by 8 since
                // every pointer is exactly 8 bytes large.
                assert!(derived_pointer_location.location_size % 8 == 0);
                RelocationPair {
                    base_pointer_offset: base_pointer_location.offset_or_small_constant,
                    derived_pointer_offset: derived_pointer_location.offset_or_small_constant,
                    number_of_derived_pointers: (derived_pointer_location.location_size / 8) as u16,
                }
            })
            .collect::<Box<[RelocationPair]>>();

        let entry = StackMapEntry { relocation_pairs };

        stack_map.insert(absolute_instruction_pointer as usize, entry);

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

#[repr(C)]
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

#[repr(C)]
struct StkMapRecordSuffix {
    _padding: u16,
    num_live_outs: u16,
}

#[repr(C)]
struct Location {
    kind: LocationKind,
    _reserved: u8,
    location_size: u16,
    dwarf_regnum: u16,
    _reserved2: u16,
    offset_or_small_constant: i32,
}

#[repr(u8)]
#[derive(PartialEq, Eq)]
#[allow(unused)]
enum LocationKind {
    Register = 1,
    Direct = 2,
    Indirect = 3,
    Constant = 4,
    ConstIndex = 5,
}

#[repr(C)]
struct LiveOuts {
    dwarf_regnum: u16,
    _reserved: u8,
    size_in_bytes: u8,
}
