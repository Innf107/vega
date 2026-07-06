use crate::{
    gc::stackmap::{StackMapEntry, get_stack_map},
    heap::HeapObject,
};
use std::{arch::asm, io::{self, Write}};

#[unsafe(no_mangle)]
pub extern "C" fn vega_debug_stack_roots() {
    for_stack_roots(
        |StackRoot {
             base_pointer,
             derived_pointer_count,
             derived_pointers,
            }| {
            print!("  {base_pointer:?}");
            io::stdout().flush().unwrap();
            // we split these up such that if the pointer is invalid, it will still be printed before panicking.
            let base_heap_object = unsafe { HeapObject::from_data(base_pointer) };
            let object_type = unsafe { (*HeapObject::info_table(base_heap_object)).object_type };
            print!("({object_type:?}) ~> [");
            for i in 0..derived_pointer_count {
                let pointer_location = unsafe { derived_pointers.add(i as usize) };
                let pointer_value = unsafe { *pointer_location };
                print!("{pointer_location:?}({pointer_value:?})");
                if i < derived_pointer_count - 1 {
                    print!(", ");
                }
            }
            println!("]")
        },
        |instruction_pointer, has_info| {
            if has_info {
                println!("{instruction_pointer:#x}:")
            } else {
                println!("{instruction_pointer:#x}: No stack map info")
            }
        },
    )
}

pub struct StackRoot {
    // The *value* of the base pointer that should be used as a stack root for garbage collection.
    // This value should *not* be updated if its allocation is moved.
    // There will be an entry in `derived_pointers` for it.`
    pub base_pointer: *const u8,
    // A pointer pointing to an array of pointers derived from the base pointer.
    // After moving the allocation that the base pointer points to, these need to be updated
    // based on their offset from the base pointer.
    pub derived_pointers: *mut *const u8,
    // The number of poniters pointed to by `derived_pointers`
    pub derived_pointer_count: u16,
}

// We add the inline(always) so that the call to this in debug_stack_roots doesn't get its own stack frame
// and doesn't clutter the displayed stack trace
#[inline(always)]
pub fn for_stack_roots(
    mut on_stack_root: impl FnMut(StackRoot),
    mut on_stack_frame: impl FnMut(usize, bool),
) {
    let mut current_rbp: usize;

    unsafe { asm!("mov {}, rbp", out(reg) current_rbp) }

    while current_rbp != 0 {
        let rip_ptr = (current_rbp + 8) as *const usize;
        let instruction_pointer = unsafe { *rip_ptr };
        let roots = unsafe { get_stack_map() };
        match roots.get(&instruction_pointer) {
            None => on_stack_frame(instruction_pointer, false),
            Some(StackMapEntry { relocation_pairs }) => {
                on_stack_frame(instruction_pointer, true);
                for relocation_pair in relocation_pairs {
                    let base_pointer = unsafe {
                        *(current_rbp as *const *const u8)
                            .byte_offset(relocation_pair.base_pointer_offset as isize)
                    };
                    let derived_pointers = unsafe {
                        (current_rbp as *mut *const u8)
                            .byte_offset(relocation_pair.derived_pointer_offset as isize)
                    };

                    let base_offset = relocation_pair.base_pointer_offset;
                    let stack_pointer = unsafe { (current_rbp as *const *const u8)
                            .byte_offset(relocation_pair.base_pointer_offset as isize) };
                    println!("  rbp: {current_rbp:#x}, base_offset: {base_offset}, stack_pointer: {stack_pointer:?}, base_pointer: {base_pointer:?}");
                    on_stack_root(StackRoot {
                        base_pointer,
                        derived_pointers,
                        derived_pointer_count: relocation_pair.number_of_derived_pointers,
                    })
                }
            }
        }

        current_rbp = unsafe { *(current_rbp as *const usize) }
    }
}
