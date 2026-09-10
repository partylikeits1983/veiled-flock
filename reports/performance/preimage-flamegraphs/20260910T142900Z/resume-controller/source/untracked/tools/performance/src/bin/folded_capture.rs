//! Byte-for-byte postprocessor that retains the folded stacks used by Inferno.

use flock_performance::{Result, tee};
use std::env;
use std::fs::OpenOptions;
use std::io;

fn run() -> Result<()> {
    let path =
        env::var_os("FLOCK_PROFILE_FOLDED_PATH").ok_or("missing FLOCK_PROFILE_FOLDED_PATH")?;
    let mut output = OpenOptions::new().write(true).create_new(true).open(path)?;
    tee(io::stdin().lock(), &mut output, io::stdout().lock())?;
    output.sync_all()?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("folded_capture: {error}");
        std::process::exit(1);
    }
}
