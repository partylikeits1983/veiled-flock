# Source Pins

Last checked: 2026-08-19.

These sources informed the implementation. The upstream VEIL proofs do not
apply directly to this `GF(2^128)` port.

| Source | Pinned version | Role |
|---|---|---|
| [FLOCK](https://github.com/succinctlabs/flock/commit/af7fa628fde250b862747521d79f721a501d1131) | `af7fa628fde250b862747521d79f721a501d1131` | Baseline |
| [VEIL paper, ePrint 2026/683](https://eprint.iacr.org/2026/683) | current public preprint at review date | Protocol |
| [VEIL Lean formalization](https://github.com/succinctlabs/veil-formal-verification/commit/064fb9e16fc46448010266fb77e00076985a3a23) | `064fb9e16fc46448010266fb77e00076985a3a23` | Reference proofs |
| [`slop-veil` crate](https://docs.rs/crate/slop-veil/6.2.2) | `6.2.2` | Reference implementation |

See [`SECURITY.md`](SECURITY.md) for the formal theorem scope, implementation
boundary, and remaining assumptions.
