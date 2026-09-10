mod common;

use common::{Temporary, init_git, remove_sealed};
use flock_performance::{Result, snapshot};
use std::fs;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn processor_archive_covers_new_modules_build_inputs_and_assets() -> Result<()> {
    let temp = Temporary::new("processor-source-closure")?;
    let edit = temp.join("editing");
    fs::create_dir_all(edit.join("crates/processor/src"))?;
    fs::write(
        edit.join("Cargo.toml"),
        "[workspace]\nmembers=[\"crates/processor\"]\nresolver=\"2\"\n",
    )?;
    fs::write(
        edit.join("Cargo.lock"),
        "version = 4\n[[package]]\nname = \"fixture-processor\"\nversion = \"0.0.0\"\n",
    )?;
    fs::write(
        edit.join("rust-toolchain.toml"),
        "[toolchain]\nchannel=\"1.98.0\"\n",
    )?;
    fs::write(
        edit.join("crates/processor/Cargo.toml"),
        "[package]\nname=\"fixture-processor\"\nversion=\"0.0.0\"\nedition=\"2024\"\n",
    )?;
    fs::write(
        edit.join("crates/processor/src/main.rs"),
        "mod extracted; fn main() { println!(\"{}:{}:{}\", extracted::answer(), include_str!(\"../assets/policy.txt\"), env!(\"BUILD_TAG\")); }\n",
    )?;
    init_git(&edit)?;
    // All these new inputs are absent from HEAD and any fixed source-file list.
    fs::write(
        edit.join("crates/processor/src/extracted.rs"),
        "pub fn answer() -> u32 { 42 }\n",
    )?;
    fs::create_dir(edit.join("crates/processor/assets"))?;
    fs::write(edit.join("crates/processor/assets/policy.txt"), "asset")?;
    fs::write(
        edit.join("crates/processor/build_support.rs"),
        "pub const TAG: &str = \"frozen-build\";\n",
    )?;
    fs::write(
        edit.join("crates/processor/build.rs"),
        "mod build_support; fn main() { println!(\"cargo:rustc-env=BUILD_TAG={}\", build_support::TAG); }\n",
    )?;
    let report = temp.join("processor-evidence");
    let frozen = snapshot::prepare(&edit, &report)?;
    struct Sealed(PathBuf);
    impl Drop for Sealed {
        fn drop(&mut self) {
            remove_sealed(&self.0);
        }
    }
    let _frozen_guard = Sealed(frozen.root.clone());
    for relative in [
        "crates/processor/src/extracted.rs",
        "crates/processor/assets/policy.txt",
        "crates/processor/build_support.rs",
        "crates/processor/build.rs",
    ] {
        assert!(
            frozen
                .inventory
                .iter()
                .any(|input| input.path == std::path::Path::new(relative))
        );
    }
    snapshot::verify(&frozen)?;
    let target = temp.join("target");
    let output = Command::new("cargo")
        .current_dir(&frozen.root)
        .env("RUSTUP_TOOLCHAIN", "1.98.0")
        .env("CARGO_TARGET_DIR", &target)
        .args(["build", "--locked", "--offline", "--manifest-path"])
        .arg(frozen.root.join("Cargo.toml"))
        .output()?;
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    snapshot::verify(&frozen)?;
    let executable = target.join("debug/fixture-processor");
    let processor =
        snapshot::ProcessorIdentity::register(&frozen, &report.join("source"), &executable)?;
    processor.verify()?;
    assert!(processor.verify_running().is_err());
    let result = Command::new(&executable).output()?;
    assert!(result.status.success());
    assert_eq!(result.stdout, b"42:asset:frozen-build\n");
    fs::write(
        edit.join("crates/processor/src/extracted.rs"),
        "pub fn answer() -> u32 { 99 }\n",
    )?;
    processor.verify()?;
    let restored = temp.join("restored");
    fs::create_dir(&restored)?;
    let status = Command::new("tar")
        .args(["-xpf"])
        .arg(&processor.source_archive.path)
        .arg("-C")
        .arg(&restored)
        .status()?;
    assert!(status.success());
    let restored_snapshot = snapshot::Snapshot {
        root: restored.clone(),
        ..frozen.clone()
    };
    snapshot::verify_source(&restored_snapshot)?;
    assert_eq!(
        fs::read_to_string(restored.join("crates/processor/src/extracted.rs"))?,
        "pub fn answer() -> u32 { 42 }\n"
    );
    Ok(())
}
