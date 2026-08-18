# zk-FLOCK with VEIL: status and remaining plan

## Implemented

- Fixed-digest BLAKE3-64 statement with randomized zk rows.
- One hiding FLOCK witness commitment/opening.
- Complete additive masking of zerocheck and lincheck messages.
- Two-phase VEIL mask commitment before FLOCK challenges.
- Shifted verifier circuit covering all PIOP equations and both PCS claims.
- Characteristic-two additive RS base/product codes and reduction.
- Public-only programmable-ROM simulator accepted by the production verifier.
- CLI, benchmark, statement/mutation tests, and canonical bundles.

The release command is:

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

The batch-256 benchmark currently measures 580 KB for succinct zk-FLOCK versus
272 KB for regular FLOCK. The prior direct whole-R1CS reference would scale to
hundreds of megabytes at that batch and is no longer user-facing.

## Next hardening milestones

The full staged proof program is in
[`FORMAL_VERIFICATION.md`](FORMAL_VERIFICATION.md). The immediate engineering
order is:

1. Add a generated mask/transcript manifest and Rust-to-Lean trace fixtures.
2. Prove the AB/C output-claim randomizer rank at every supported shape.
3. Formalize the additive RS hiding and square-code reduction used by VEIL.
4. Reconcile hiding Ligerito with the constrained-interleaved-code theorem,
   including the terminal residual.
5. Connect the public-only simulator to a classical-ROM theorem.
6. Add bounded deserialization, fuzzing, and independent review.

## Release gate

Formatting, strict Clippy, all workspace tests, real prove/verify, public-only
simulation, CLI demo, mutation tests, and benchmark reproduction must pass from
a clean checkout. Publishing remains a separate user-approved action.
