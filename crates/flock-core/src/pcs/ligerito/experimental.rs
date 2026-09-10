//! Experimental rate-1/8 UDR schedules. Rust numerical bounds only;
//! these schedules are not part of the registered Lean parameter tables.

use super::LigeritoSecurityConfig;

/// Reproduce the small-proof schedule at committed dimensions 23..=27.
/// Keep L0 at 121 queries and pay aggregate slack at narrower levels.
/// The 256-slot case adds one final-level query to the original experiment
/// so the composed FLOCK + VEIL + PCS bound also clears 100 bits.
pub fn experimental_zk100_config(m: usize) -> Result<LigeritoSecurityConfig, String> {
    let queries: &[usize] = match m {
        23 => &[121, 114, 111],
        24 => &[121, 113, 110],
        25 => &[121, 113, 109, 109],
        26 => &[121, 113, 109, 108],
        27 => &[121, 113, 109, 107],
        _ => return Err("experimental ZK PCS supports committed m=23..=27 only".into()),
    };
    let mut config = LigeritoSecurityConfig::derive_paper_compatible(m, 3, 100)?;
    if config.levels.len() != queries.len() {
        return Err("experimental ZK PCS recursion shape changed".into());
    }
    for (level, &queries) in config.levels.iter_mut().zip(queries) {
        level.queries = queries;
        level.expected_eps_query_bits = super::round1(level.paper_predicted_bits().1);
    }
    let bits = config.aggregate_soundness_bound_zk_l0()?.bits();
    if !bits.is_finite() || bits < 100.0 {
        return Err(format!(
            "experimental ZK PCS aggregate below 100 bits: {bits}"
        ));
    }
    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::ligerito::{LigeritoProfile, SoundnessRegime};

    #[test]
    fn experimental_schedules_validate_and_roundtrip() {
        for m in 23..=27 {
            let config = experimental_zk100_config(m).unwrap();
            assert!(config.aggregate_soundness_bound_zk_l0().unwrap().bits() >= 100.0);
            assert_eq!(config.levels[0].log_inv_rate, 3);
            assert!(
                config
                    .levels
                    .iter()
                    .all(|l| l.regime == SoundnessRegime::Udr
                        && l.ood_samples == 0
                        && l.fold_grinding_bits == 0)
            );
            let (prover, verifier) = config.to_prover_verifier_configs().unwrap();
            assert_eq!(prover.queries, verifier.queries);
            let encoded = config.to_toml_string().unwrap();
            let decoded = LigeritoSecurityConfig::from_toml_str(&encoded).unwrap();
            assert_eq!(
                decoded.to_prover_verifier_configs().unwrap(),
                (prover, verifier)
            );
            assert_eq!(
                LigeritoSecurityConfig::derive_profile(m, LigeritoProfile::ExperimentalZk100)
                    .unwrap()
                    .to_toml_string()
                    .unwrap(),
                encoded
            );
            // Per-round 100-bit query counts alone do not clear the aggregate.
            let untuned = LigeritoSecurityConfig::derive_paper_compatible(m, 3, 100).unwrap();
            assert!(untuned.aggregate_soundness_bound_zk_l0().unwrap().bits() < 100.0);
        }
        for m in [0, 22, 28, usize::MAX] {
            assert!(experimental_zk100_config(m).is_err());
        }
    }
}
