use std::io::Error;

// We will probably replace this with some actual vega code at some point,
// but for now this makes for a very easy way of writing tests
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_debug_int(int: i64) {
    println!("{}", int);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vega_errno() -> i32 {
    Error::last_os_error().raw_os_error().unwrap()
}
