//! Exact scalar semantics for the generated ZK coverage artifacts.
//!
//! Protocol maps are represented as straight-line programs over [`SymScalar`].
//! The same program can be evaluated concretely, interpreted as a conservative
//! per-variable degree bound, or expanded exactly on toy instances.

pub mod cleared;
pub mod degree;
pub mod kernels;
pub mod linform;
pub mod poly;
pub mod scalar;
pub mod vars;

pub use cleared::{Cleared, DenAtom};
pub use degree::DegBound;
pub use linform::{Channel, CoordId, LinForm};
pub use poly::SparseMvPoly;
pub use scalar::SymScalar;
pub use vars::{Var, VarSet};
