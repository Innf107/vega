use crate::{
    either::Either,
    heap::{HeapObject, HeapObjectHandle},
};
use std::{
    arch::asm,
    io::{self, Write},
    ptr::null,
};

#[repr(C)]
pub struct ShadowStackFrame {
    previous: *const ShadowStackFrame,
    size: u64,
    // this should really have a `pointers : [*const u8]` member but the
    // compiler doesn't like it if we use a slice in FFI
}

pub fn for_stack_roots(
    shadow_stack_pointer: *const ShadowStackFrame,
    mut on_root: impl FnMut(*mut *const u8),
) {
    let mut frame = shadow_stack_pointer;
    while frame != null() {
        unsafe {
            let size = (*frame).size;
            let pointers = frame.byte_add(size_of::<ShadowStackFrame>()) as *mut *const u8;
            for i in 0..(size as usize) {
                on_root(pointers.add(i));
            }
            frame = (*frame).previous;
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vega_debug_stack_roots(shadow_stack_pointer: *const ShadowStackFrame) {
    let mut frame = shadow_stack_pointer;
    while frame != null() {
        unsafe {
            let size = (*frame).size;
            println!("frame({size})@{frame:?}");
            let pointers = frame.byte_add(size_of::<ShadowStackFrame>()) as *mut *const u8;
            for i in 0..(size as usize) {
                let pointer_to_data_pointer = pointers.add(i);
                print!("   {pointer_to_data_pointer:?}(");
                let object_type_description = HeapObject::object_type_description(HeapObject::from_data(*pointer_to_data_pointer));
                println!("{object_type_description})");
            }
            frame = (*frame).previous;
        }
    }
}
