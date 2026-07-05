use std::{arch::asm};
use crate::gc::stackmap::{get_stack_map};


#[unsafe(no_mangle)]
pub extern "C" fn vega_debug_stack_roots() {
    let mut current_rbp : usize;

    unsafe { asm!("mov {}, rbp", out(reg) current_rbp) }

    while current_rbp != 0 {
        let rip_ptr = (current_rbp + 8) as *const usize;
        let instruction_pointer = unsafe { *rip_ptr };
        let roots = unsafe { get_stack_map() };
        match roots.get(&instruction_pointer) {
            None => println!("IP {instruction_pointer:#x}: No stack map info"),
            Some(entry) => {
                println!("IP {instruction_pointer:#x}: {entry:?}")
            }
        }

        current_rbp = unsafe { *(current_rbp as *const usize) }
    }
}

