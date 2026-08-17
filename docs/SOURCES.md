# Source pins

These are research inputs, not vendored dependencies.

| Source | Local path | Revision |
|---|---|---|
| Current FLOCK | `../flock` | `af7fa628fde250b862747521d79f721a501d1131` |
| VEIL Lean formalization | `../veil-formal-verification` | `064fb9e16fc46448010266fb77e00076985a3a23` |
| Previous zk-FLOCK experiment | `../../flock`, ref `fork/zk-flock` | `39c2ffe156a1197d04717769810c4f6fca0db4b0` |
| VEIL Rust reference | local crates.io cache, `slop-veil` | `6.2.2` |

Before a benchmark or security report, verify that the local checkouts still match
these revisions. Do not silently benchmark against a dirty or advanced checkout.

The VEIL trusted-base definitions and theorem statements require human comparison
with the paper. Machine-checked proofs do not establish that the formal statements
match either the paper or a future Rust port.
