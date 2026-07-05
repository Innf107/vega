use std::{arch::asm, cell::OnceCell, collections::HashMap};
use crate::gc::stackmap::{get_stack_map};


#[unsafe(no_mangle)]
pub extern "C" fn vega_debug_stack_roots() {
    let mut current_rbp : usize;

    unsafe { asm!("mov {}, rbp", out(reg) current_rbp) }

    while current_rbp != 0 {
        println!("base pointer: {current_rbp}");

        let rip_ptr = (current_rbp + 8) as *const usize;
        let instruction_pointer = unsafe { *rip_ptr };
        println!("instruction pointer: {instruction_pointer}");
        let roots = unsafe { get_stack_map() };
        match roots.get(&instruction_pointer) {
            None => println!("WARNING: No stack root info for instruction pointer {instruction_pointer}"),
            Some(_) => {

            }
        }

        current_rbp = unsafe { *(current_rbp as *const usize) }
    }
}

