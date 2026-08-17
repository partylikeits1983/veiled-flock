# Initial transcript audit

This is a seed inventory, not the final count. P1 replaces every approximate row
with counts generated from the typed verifier program.

| Phase | Current value | Proposed VEIL class | Required action |
|---|---|---|---|
| Statement | R1CS/circuit identity and public digests | Public | Canonically encode and absorb first |
| Witness commitment | Merkle root over interleaved RS code | Shielded | Replace with stacked ZK PCS commitment |
| Zerocheck round 1 | 64 `F128` AB values + 64 C values | Exposed | Mask through multi-round compiler |
| Zerocheck later rounds | Degree-2 message pairs | Exposed | Mask and constrain |
| Zerocheck terminal values | A, B, and C evaluations | Exposed | Mask; audit C serialization once, not twice |
| Lincheck rounds | Degree-2 message pairs | Exposed | Mask and constrain |
| Lincheck terminal vector | `z_partial`, currently 64 `F128` values | Exposed | Mask and constrain |
| Ring switch | 128 `s_hat_v` values per evaluation claim | Exposed initially | Mask; consider shielded optimization later |
| Ligerito roots/paths | Merkle commitments and authentication data | Shielded | Simulate with stacked PCS view |
| Ligerito queried code data | Opened rows/columns at each recursive level | Shielded | Random padding must cover aggregate/per-level query budget |
| Ligerito sumcheck/OOD | Field messages | Exposed | Mask and constrain |
| Ligerito final `yr` | Clear terminal residual vector | Exposed initially | Mask and check inside shifted circuit |
| Fiat-Shamir challenges | Hash-derived | Derived | Interactive coins first; FS transcript later |

Important corrections relative to older notes:

- The current PCS is encoded and committed over `F128`, not directly over `F2` or
  packed `F2^32`.
- Current lincheck sends a 64-element `z_partial`, not a full length-`k` vector.
- The current Fast `m22` schedule uses query counts 218/106/53; profiles must be
  read from the checked-in configuration rather than copied from older papers.
- Current Rust Ligerito uses additive-NTT Reed–Solomon code; an RAA/MDS branch is
  not part of the initial integration scope.

