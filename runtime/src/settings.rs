use std::{env, process::exit};

use argh::FromArgs;

#[derive(FromArgs, Debug)]
/// Arguments passed to the vega runtime
pub struct RuntimeSettings {
    /// the size of the nursery in 4KB blocks. default: 1024
    #[argh(option, long = "nursery-size", default = "1024")]
    pub nursery_size_in_blocks: usize,
    /// the initial size of the major heap in 4KB blocks. default: 1024
    #[argh(option, long = "initial-major-size", default = "1024")]
    pub initial_major_heap_size_in_blocks: usize,
    /// the number of blocks to allocate from the operating system at once.
    /// Larger sizes will reduce the number of mmap calls performed.
    /// default: 256
    #[argh(option, long = "block-batch-size", default = "256")]
    pub block_allocation_batch_size: usize,
}

pub const fn default_runtime_settings() -> RuntimeSettings {
    RuntimeSettings {
        nursery_size_in_blocks: 1024,
        initial_major_heap_size_in_blocks: 1024,
        block_allocation_batch_size: 256,
    }
}

static mut SETTINGS: RuntimeSettings = default_runtime_settings();

// Access the settings passed to the runtime at startup.
//
// This is technically only safe if it doesn't race a call to 'parse_runtime_settings'.
// Since that function is called at startup, this will never happen though.
#[allow(static_mut_refs)]
pub fn settings() -> &'static RuntimeSettings {
    unsafe { &SETTINGS }
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

    let settings = match RuntimeSettings::from_args(&command_name, &argument_slice) {
        Ok(settings) => settings,
        Err(early_exit) => match early_exit.status {
            Ok(()) => {
                println!("{}", early_exit.output);
                exit(0)
            }
            Err(()) => {
                // Horrible hack to get argh to display the help text if an error occurs 
                let help_text = RuntimeSettings::from_args(&command_name, &["--help"]).unwrap_err().output;
                eprintln!("{executable_name} +RTS: {}\n{help_text}", early_exit.output);
                exit(1)
            }
        },
    };

    unsafe {
        SETTINGS = settings;

        &SETTINGS
    }
}
