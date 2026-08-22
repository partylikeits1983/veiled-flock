# Succinct VEIL-FLOCK transcript (version 0)

1. Absorb the fixed-digest statement.
2. Commit hidingly to the randomized FLOCK witness and bind the proof nonce,
   circuit shape, and witness root.
3. Precommit to the VEIL mask vector `h` plus its six private multiplication
   pads; absorb that root under `veil-flock-mask-root-v0`.
4. Run FLOCK zerocheck. Every prover F128 message is observed and serialized as
   `value + h_i`. Scalar and slice Fiat--Shamir framing is preserved exactly.
   Sampled equality coordinates used by the compressed recurrence are
   rejection-sampled from `GF(2^128) \ {1}`.
5. Run FLOCK lincheck with the same treatment for every round pair and the
   final `z_partial` vector.
6. Send the AB and C opening values and absorb them under
   `veil-flock-output-claims-v0`. These values are tied to randomized witness
   rows and are checked in both the shifted circuit and PCS.
7. Sample the public digest batching challenge and run one hiding
   ring-switch/Ligerito opening for AB, C, and the digest claim.
8. From the pre-opening transcript fork, absorb
   `veil-flock-inner-fork-v0` and finish the VEIL proof of the shifted verifier
   circuit. This fork avoids relying on an unused historical invariant that
   Ligerito's prover and verifier leave identical states after their terminal
   opening; all linkage data is already bound before the fork.

At the batch-256 shape the mask vector has 242 F128 values:

```text
2*64 zerocheck round-1 values
+ 2*(22-6) zerocheck multilinear values
+ 2 zerocheck terminal values (a,b)
+ 2*(14-6) lincheck round values
+ 64 lincheck z_partial values
= 242
```

`final_c_eval` is not an observed FLOCK message and is omitted from the masked
zerocheck wire type. The proof stores the public C PCS claim once as `c_value`,
while the shifted circuit reconstructs it from the masked round-1 C vector.

No mask, preimage, witness bit, or unmasked PIOP round message is serialized.

PCS and VEIL commitments use a native framed `RoContext` separate from the
programmable Fiat--Shamir oracle and are not represented here. See section 15
of the [specification](../SPEC.md).
