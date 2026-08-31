use std::fmt;

use flock_core::pcs;
use veil_f128::ConstraintError;

/// Every failure of the example contexts. Deferred constraint failures
/// surface only at `prove` or `verify`; the `assert_*` calls never fail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VeilError {
    TranscriptExhausted,
    TranscriptNotConsumed,
    ChallengeReplayExhausted,
    MaskCountMismatch { expected: usize, actual: usize },
    OracleShape { expected: usize, actual: usize },
    PointShape { expected: usize, actual: usize },
    WitnessLength { expected: usize, actual: usize },
    OracleExhausted,
    OracleNotConsumed,
    PcsParamsMismatch,
    ClaimWithoutOracle,
    ProofShape(&'static str),
    GrindingLimitExceeded,
    InvalidGrindNonce,
    ChallengeSamplingLimitExceeded,
    DegenerateChallenge,
    Constraint(ConstraintError),
    Pcs(pcs::VerifyError),
    Ligerito(String),
}

impl fmt::Display for VeilError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TranscriptExhausted => write!(f, "the masked transcript is exhausted"),
            Self::TranscriptNotConsumed => write!(f, "the masked transcript has unread values"),
            Self::ChallengeReplayExhausted => {
                write!(
                    f,
                    "the verify replay did not consume all challenges produced by the prove pass"
                )
            }
            Self::MaskCountMismatch { expected, actual } => {
                write!(f, "mask count mismatch: expected {expected}, got {actual}")
            }
            Self::OracleShape { expected, actual } => write!(
                f,
                "oracle shape mismatch: the PCS holds 2^{expected} bits, the protocol asked for 2^{actual}"
            ),
            Self::PointShape { expected, actual } => write!(
                f,
                "claim point shape mismatch: expected {expected} coordinates, got {actual}"
            ),
            Self::WitnessLength { expected, actual } => {
                write!(
                    f,
                    "packed witness length mismatch: expected {expected} words, got {actual}"
                )
            }
            Self::OracleExhausted => write!(f, "the proof carries fewer commitments than read"),
            Self::OracleNotConsumed => write!(f, "the proof carries unread commitments"),
            Self::PcsParamsMismatch => write!(f, "the commitment parameters do not match the PCS"),
            Self::ClaimWithoutOracle => write!(f, "an evaluation claim needs a configured PCS"),
            Self::ProofShape(what) => write!(f, "malformed proof: {what}"),
            Self::GrindingLimitExceeded => write!(f, "a bounded grind found no nonce"),
            Self::InvalidGrindNonce => write!(f, "a grind nonce is out of bounds or wrong"),
            Self::ChallengeSamplingLimitExceeded => {
                write!(f, "rejection sampling of a field challenge hit its cap")
            }
            Self::DegenerateChallenge => write!(f, "a sumcheck round has a degenerate challenge"),
            Self::Constraint(error) => write!(f, "VEIL constraint error: {error:?}"),
            Self::Pcs(error) => write!(f, "PCS verification error: {error:?}"),
            Self::Ligerito(message) => write!(f, "Ligerito configuration error: {message}"),
        }
    }
}

impl std::error::Error for VeilError {}

impl From<ConstraintError> for VeilError {
    fn from(value: ConstraintError) -> Self {
        Self::Constraint(value)
    }
}

impl From<pcs::VerifyError> for VeilError {
    fn from(value: pcs::VerifyError) -> Self {
        Self::Pcs(value)
    }
}
