//! Regenerate and validate the embedded Ligerito security configs.
//! Run with `cargo run --release --example gen_ligerito_configs`.

use std::path::Path;

use flock_prover::pcs::ligerito::{LigeritoProfile, LigeritoSecurityConfig};

fn main() {
    let profiles = [
        LigeritoProfile::Fast,
        LigeritoProfile::Slim,
        LigeritoProfile::Secure,
        LigeritoProfile::Standard,
    ];
    // Configs live in the flock-core crate (which embeds them via include_str!).
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../flock-core/configs/ligerito");
    let mut failures = 0usize;

    for m in 22..=35usize {
        for &profile in &profiles {
            if profile == LigeritoProfile::Standard && !(23..=27).contains(&m) {
                continue;
            }
            let path = dir.join(format!("m{m}_{}.toml", profile.as_str()));
            match LigeritoSecurityConfig::derive_profile(m, profile) {
                Ok(cfg) => {
                    let toml = cfg.to_toml_string().expect("serialize");
                    // Round-trip to be sure the written form re-validates.
                    LigeritoSecurityConfig::from_toml_str(&toml)
                        .unwrap_or_else(|e| panic!("m={m}: written toml fails reload: {e}"));
                    std::fs::write(&path, &toml).expect("write toml");
                    let queries: usize = cfg.levels.iter().map(|l| l.queries).sum();
                    let ood: usize = cfg.levels.iter().map(|l| l.ood_samples).sum();
                    let max_fold_grind = cfg
                        .levels
                        .iter()
                        .map(|l| l.fold_grinding_bits)
                        .max()
                        .unwrap_or(0);
                    println!(
                        "write m={m} {:<6} -> {} (levels={}, Σqueries={queries}, Σood={ood}, max fold grind=2^{max_fold_grind})",
                        profile.as_str(),
                        path.file_name().unwrap().to_string_lossy(),
                        cfg.levels.len(),
                    );
                }
                Err(e) => {
                    eprintln!("FAIL  m={m} {}: derive failed: {e}", profile.as_str());
                    failures += 1;
                }
            }
        }
    }
    if failures > 0 {
        std::process::exit(1);
    }
}
