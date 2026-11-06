use std::{env, mem::MaybeUninit, process::exit};

use argh::FromArgs;

#[derive(FromArgs, Debug)]
/// Arguments passed to the vega runtime
pub struct RuntimeSettings {
    /// the size of the nursery in 4KB blocks. default: 1024
    #[argh(option, long = "nursery-size", default = "1024")]
    pub nursery_size_in_blocks: usize,
    /// the initial size of the major heap in 4KB blocks. default: 4096
    #[argh(option, long = "initial-major-size", default = "4096")]
    pub initial_major_heap_size_in_blocks: usize,
    /// the number of blocks to allocate from the operating system at once.
    /// Larger sizes will reduce the number of mmap calls performed.
    /// default: 256
    #[argh(option, long = "block-batch-size", default = "256")]
    pub block_allocation_batch_size: usize,

    /// the amount by which to scale the major heap based on the live set size after each major collection.
    /// The major heap will always contain at least enough space for this, but will not scale down to match it.
    /// default: 3.0
    #[argh(option, long = "major-scale", default = "3.0")]
    pub major_heap_scaling_factor: f64,

    /// the name of the file that the event log should be written to.
    /// Use `-` for stdout or "" (empty string) to disable the event log.
    /// default: ""
    #[argh(option, long = "event-log-output", default = "String::new()")]
    pub event_log_output: String,

    /// emit stack roots to the event log at every garbage collection for debugging purposes.
    #[argh(switch, long = "debug-stack-roots")]
    pub debug_stack_roots: bool,

    /// print more detail about the heap object stored at each stack root.
    /// This can be useful for figuring out if the objects look wrong at a glance
    /// even if they have a sensible info table.
    #[argh(switch, long = "detailed-stack-roots")]
    pub detailed_stack_roots: bool,

    /// hide the object types of heap objects. The object types are usually useful information but
    /// determining them can sometimes segfault.
    #[argh(switch, long = "hide-stack-root-types")]
    pub hide_stack_root_types: bool,

    /// make heap integrity checks include liveness analysis from garbage collection.
    /// (incompatible with --evacuation-integrity for now)
    #[argh(switch, long = "liveness-integrity")]
    pub liveness_integrity: bool,

    /// add integrity checks to every evacuated heap object during garbage collection
    /// (incompatible with --liveness-integrity for now)
    #[argh(switch, long = "evacuation-integrity")]
    pub evacuation_integrity: bool,

    /// add recursive integrity checks to every stack root before and after each garbage collection
    /// (implies --liveness-integrity)
    #[argh(switch, long = "root-integrity")]
    pub root_integrity: bool,
}

static mut SETTINGS: MaybeUninit<RuntimeSettings> = MaybeUninit::zeroed();

// Access the settings passed to the runtime at startup.
//
// This is technically only safe if it doesn't race a call to 'parse_runtime_settings'.
// Since that function is called at startup, this will never happen though.
#[allow(static_mut_refs)]
pub fn settings() -> &'static RuntimeSettings {
    unsafe { &SETTINGS.assume_init_ref() }
}

#[allow(static_mut_refs)]
pub fn parse_runtime_settings() -> &'static RuntimeSettings {
    let executable_name = env::args().next().unwrap();
    let name_with_rts_specifier = format!("{executable_name} +RTS");
    let command_name: [&str; _] = [&name_with_rts_specifier];

    let mut real_arguments = Vec::new();
    let mut parsed_as_rts_flag = false;
    for argument in env::args() {
        match argument.as_str() {
            "+RTS" => {
                parsed_as_rts_flag = true;
            }
            "-RTS" => {
                parsed_as_rts_flag = false;
            }
            "--RTS" => {
                // -- We stop parsing any runtime flags after a --RTS so we can just exit here
                break;
            }
            _ => {
                if parsed_as_rts_flag {
                    real_arguments.push(argument)
                }
            }
        }
    }
    let argument_slice: Vec<&str> = real_arguments
        .iter()
        .map(|argument| argument.as_str())
        .collect();

    let mut settings = match RuntimeSettings::from_args(&command_name, &argument_slice) {
        Ok(settings) => settings,
        Err(early_exit) => match early_exit.status {
            Ok(()) => {
                println!("{}", early_exit.output);
                exit(0)
            }
            Err(()) => {
                // Horrible hack to get argh to display the help text if an error occurs
                let help_text = RuntimeSettings::from_args(&command_name, &["--help"])
                    .unwrap_err()
                    .output;
                eprintln!("{executable_name} +RTS: {}\n{help_text}", early_exit.output);
                exit(1)
            }
        },
    };
    if settings.root_integrity {
        settings.liveness_integrity = true;
    }
    if settings.liveness_integrity && settings.evacuation_integrity {
        eprintln!(
            "{executable_name} +RTS: Flags '--liveness-integrity' and '--evacuation-integrity' are incompatible"
        );
        exit(1)
    }

    unsafe {
        SETTINGS.write(settings);

        &SETTINGS.assume_init_ref()
    }
}
