use super::LigeritoSecurityConfig;

/// Build the Standard ZK schedule for a supported witness dimension.
pub fn standard_config(m: usize) -> Result<LigeritoSecurityConfig, String> {
    let source = super::embedded_security_config(m, super::LigeritoProfile::Standard)
        .ok_or_else(|| format!("unsupported Standard PCS dimension: {m}"))?;
    let config = LigeritoSecurityConfig::from_toml_str(source)?;
    let bits = config
        .aggregate_soundness_bound_query_padded(config.levels[0].queries)?
        .bits();
    if !bits.is_finite() || bits < 100.0 {
        return Err(format!("ZK PCS aggregate below 100 bits: {bits}"));
    }
    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::ligerito::{LigeritoProfile, SoundnessRegime};

    #[test]
    fn canonical_schedules_validate_and_roundtrip() {
        for m in 22..=26 {
            let config = standard_config(m).unwrap();
            assert!(
                config
                    .aggregate_soundness_bound_query_padded(config.levels[0].queries)
                    .unwrap()
                    .bits()
                    >= 100.0
            );
            assert_eq!(
                config.levels[0].log_inv_rate,
                LigeritoProfile::Standard.log_inv_rate_for_m(m)
            );
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
            assert_eq!(
                super::super::embedded_security_config(m, LigeritoProfile::Standard).unwrap(),
                encoded
            );
            let decoded = LigeritoSecurityConfig::from_toml_str(&encoded).unwrap();
            assert_eq!(
                decoded.to_prover_verifier_configs().unwrap(),
                (prover, verifier)
            );
            assert_eq!(
                LigeritoSecurityConfig::derive_profile(m, LigeritoProfile::Standard)
                    .unwrap()
                    .to_toml_string()
                    .unwrap(),
                encoded
            );
        }
        for m in [0, 21, 27, usize::MAX] {
            assert!(standard_config(m).is_err());
        }
    }
}
