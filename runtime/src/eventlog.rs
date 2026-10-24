use std::{fs::File, io::Write, sync::{Mutex, MutexGuard}};

static mut EVENT_LOG_OUTPUT: Option<Mutex<File>> = None;


#[allow(static_mut_refs)]
fn lock_output() -> MutexGuard<'static, File> {
    match unsafe { &EVENT_LOG_OUTPUT } {
        None => panic!("trying to write to an uninitialized event log output"),
        Some(mutex) => {
            mutex.lock().unwrap()
        }
    }
}

pub fn emit_garbage_collection_start(is_major: bool) {
    let mut output = lock_output();
    writeln!(output, "{{ \"event\": \"garbage_collection_start\", \"is_major\": {is_major} }}").unwrap()
}
pub fn emit_garbage_collection_end() {
    let mut output = lock_output();
    writeln!(output, "{{ \"event\": \"garbage_collection_end\" }}").unwrap();
}

