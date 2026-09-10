//! Typed boundary observations; they do not imply continuous power or clock state.

use crate::{Result, command};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PowerPolicy {
    #[default]
    RequireAc,
    ObserveOnly,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PowerSource {
    Ac,
    Battery,
    Unknown,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PowerObservation {
    pub source: PowerSource,
    pub observed_unix_seconds: f64,
    pub raw: String,
    pub error: Option<String>,
}

impl PowerObservation {
    pub fn parse(raw: &str) -> Self {
        let mut source = None;
        let mut ambiguous = false;
        for line in raw.lines() {
            let observed = match line.trim() {
                "Now drawing from 'AC Power'" => Some(PowerSource::Ac),
                "Now drawing from 'Battery Power'" => Some(PowerSource::Battery),
                _ => None,
            };
            if let Some(observed) = observed {
                if source.is_some_and(|previous| previous != observed) {
                    ambiguous = true;
                }
                source = Some(observed);
            }
        }
        Self {
            source: if ambiguous {
                PowerSource::Unknown
            } else {
                source.unwrap_or(PowerSource::Unknown)
            },
            observed_unix_seconds: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs_f64(),
            raw: raw.to_owned(),
            error: None,
        }
    }

    pub fn observe() -> Self {
        match command("pmset").args(["-g", "batt"]).output() {
            Ok(output) if output.status.success() => match String::from_utf8(output.stdout) {
                Ok(raw) => Self::parse(&raw),
                Err(error) => {
                    let mut observation = Self::parse("");
                    observation.error = Some(error.to_string());
                    observation
                }
            },
            Ok(output) => {
                let mut observation = Self::parse(&String::from_utf8_lossy(&output.stdout));
                observation.source = PowerSource::Unknown;
                observation.error = Some(format!(
                    "pmset failed: {}; {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr)
                ));
                observation
            }
            Err(error) => {
                let mut observation = Self::parse("");
                observation.error = Some(error.to_string());
                observation
            }
        }
    }
}

impl PowerPolicy {
    pub fn accepts(self, observation: &PowerObservation) -> bool {
        self == Self::ObserveOnly
            || (observation.source == PowerSource::Ac && observation.error.is_none())
    }

    pub fn validate(self, observation: &PowerObservation) -> Result<()> {
        if !self.accepts(observation) {
            return Err(format!(
                "require-AC measurement policy rejects {:?} power",
                observation.source
            )
            .into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn power_policy_never_converts_unknown_to_ac() {
        for raw in [
            "",
            "AC Power",
            "Now drawing from 'Battery Power'",
            "Now drawing from 'AC Power'\nNow drawing from 'Battery Power'",
        ] {
            let observation = PowerObservation::parse(raw);
            assert!(!PowerPolicy::RequireAc.accepts(&observation));
            assert!(PowerPolicy::ObserveOnly.accepts(&observation));
        }
        let observation = PowerObservation::parse(
            "Now drawing from 'AC Power'\n -InternalBattery-0  52%; charging",
        );
        assert!(PowerPolicy::RequireAc.accepts(&observation));
        assert_eq!(PowerPolicy::default(), PowerPolicy::RequireAc);
    }
}
