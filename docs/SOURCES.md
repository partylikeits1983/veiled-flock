# Source pins and upstream references

Last checked: 2026-08-19.

These are research and comparison inputs. `veil-f128` is a native
`GF(2^128)` implementation in this repository; it does not depend on the
upstream `slop-veil` crate, and upstream theorems do not automatically apply to
this field/code-family port.

| Source | Pinned version | Role |
|---|---|---|
| [FLOCK](https://github.com/succinctlabs/flock/commit/af7fa628fde250b862747521d79f721a501d1131) | `af7fa628fde250b862747521d79f721a501d1131` | Baseline FLOCK implementation used when this fork was refreshed |
| [VEIL paper, ePrint 2026/683](https://eprint.iacr.org/2026/683) | current public preprint at review date | Protocol design being adapted |
| [VEIL Lean formalization](https://github.com/succinctlabs/veil-formal-verification/commit/064fb9e16fc46448010266fb77e00076985a3a23) | `064fb9e16fc46448010266fb77e00076985a3a23` | Upstream definitions and theorem structure used for comparison |
| [`slop-veil` crate documentation](https://docs.rs/crate/slop-veil/6.2.2) | `6.2.2` | Rust reference implementation used for design comparison only |
| [Historical A1/custom-mask branch point](https://github.com/partylikeits1983/veiled-flock/commit/39c2ffe156a1197d04717769810c4f6fca0db4b0) | `39c2ffe156a1197d04717769810c4f6fca0db4b0` | Previous zk-FLOCK experiment; not the active CLI path |
| [Historical benchmark implementation](https://github.com/partylikeits1983/veiled-flock/commit/a3da544ea88042ab14e69cdf0dc5663efa0cc1c3) | `a3da544ea88042ab14e69cdf0dc5663efa0cc1c3` | Source revision recorded by `artifacts/zk_benchmark_256.json` |

For a benchmark or security report, record the exact repository revision,
dirty-tree state, Rust toolchain, features, hardware, thread count, batch,
trials, and proof serialization boundary. Do not compare the historical A1
artifact with the active succinct benchmark as if only one variable changed.

The upstream VEIL material describes a protocol and formal statements. Human
review is still required to show that those statements match the paper and
that this repository's additive-domain implementation refines them. The active
composition has additional FLOCK-specific obligations listed in
[`SECURITY.md`](SECURITY.md).
