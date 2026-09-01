//! Shared oracle-query budgets and fail-closed cap errors.

use std::{
    fmt,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

/// Deterministic upper bound on random-oracle answers made by one proof.
pub const MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF: u64 = 1_000_000;

/// SHA-256 answers one 32-byte block per random-oracle query.
pub const ORACLE_BLOCK_BYTES: usize = 32;

/// Fail-closed cap for scalar/vector rejection samplers and position samplers.
pub const REJECTION_SAMPLING_TRIALS: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OracleLimitError {
    QueryBudgetExceeded,
    GrindingLimitExceeded,
    RejectionSamplingLimitExceeded,
    PositionSamplingLimitExceeded,
}

impl fmt::Display for OracleLimitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::QueryBudgetExceeded => f.write_str("random-oracle query budget exceeded"),
            Self::GrindingLimitExceeded => f.write_str("proof-of-work grinding cap exceeded"),
            Self::RejectionSamplingLimitExceeded => f.write_str("rejection-sampling cap exceeded"),
            Self::PositionSamplingLimitExceeded => f.write_str("position-sampling cap exceeded"),
        }
    }
}

impl std::error::Error for OracleLimitError {}

#[derive(Debug)]
struct OracleQueryBudgetInner {
    limit: u64,
    used: AtomicU64,
}

/// Thread-safe per-proof random-oracle query budget.
#[derive(Clone, Debug)]
pub struct OracleQueryBudget {
    inner: Arc<OracleQueryBudgetInner>,
}

impl OracleQueryBudget {
    pub fn new(limit: u64) -> Self {
        Self {
            inner: Arc::new(OracleQueryBudgetInner {
                limit,
                used: AtomicU64::new(0),
            }),
        }
    }

    pub fn per_proof() -> Self {
        Self::new(MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF)
    }

    pub fn limit(&self) -> u64 {
        self.inner.limit
    }

    pub fn used(&self) -> u64 {
        self.inner.used.load(Ordering::Relaxed)
    }

    /// Reserve `amount` oracle answers before performing them.
    ///
    /// On failure the used count is unchanged, so callers can assert exact
    /// caps in tests and no query beyond the budget is made.
    pub fn try_charge(&self, amount: u64) -> Result<(), OracleLimitError> {
        let mut current = self.inner.used.load(Ordering::Relaxed);
        loop {
            let Some(next) = current.checked_add(amount) else {
                return Err(OracleLimitError::QueryBudgetExceeded);
            };
            if next > self.inner.limit {
                return Err(OracleLimitError::QueryBudgetExceeded);
            }
            match self.inner.used.compare_exchange_weak(
                current,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(()),
                Err(observed) => current = observed,
            }
        }
    }
}

/// Number of 32-byte oracle answers needed to fill `bytes` output bytes.
pub fn oracle_blocks_for_bytes(bytes: usize) -> Result<u64, OracleLimitError> {
    bytes
        .div_ceil(ORACLE_BLOCK_BYTES)
        .try_into()
        .map_err(|_| OracleLimitError::QueryBudgetExceeded)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_budget_failure_does_not_increment_used_count() {
        let budget = OracleQueryBudget::new(3);
        assert_eq!(budget.try_charge(2), Ok(()));
        assert_eq!(budget.used(), 2);
        assert_eq!(
            budget.try_charge(2),
            Err(OracleLimitError::QueryBudgetExceeded)
        );
        assert_eq!(budget.used(), 2);
        assert_eq!(budget.try_charge(1), Ok(()));
        assert_eq!(budget.used(), 3);
    }
}
