use std::arch::asm;


pub extern "C" fn debug_stack_roots() {
    let mut current_rbp : usize;

    unsafe { asm!("mov {}, rbp", out(reg) current_rbp) }

    while current_rbp != 0 {
        println!("base pointer: {current_rbp}")
    }
}

