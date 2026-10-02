use crate::{gc::initialize_gc, settings::parse_runtime_settings};


#[unsafe(no_mangle)]
pub extern "C" fn vega_initialize() {
    let settings = parse_runtime_settings();
    initialize_gc(settings);
}
