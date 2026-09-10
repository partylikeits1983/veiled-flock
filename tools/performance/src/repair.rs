//! Compatibility surface for the former in-place correction command.
//!
//! Corrections now belong to immutable publication generations. Original
//! recordings and previously published report trees are read-only inputs.

use crate::Result;
use std::path::Path;

pub use crate::xctrace::validate_xml;

pub fn repair_report(_root: &Path) -> Result<()> {
    Err("in-place repair is disabled; use profile_preimages --report <evidence> --output <publication>".into())
}
