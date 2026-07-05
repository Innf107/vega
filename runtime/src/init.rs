use crate::gc::stackmap::initialize_stack_roots;

#[unsafe(no_mangle)]
pub extern "C" fn vega_initialize() {
    initialize_stack_roots();
}
