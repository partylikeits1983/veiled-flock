# VEIL FLOCK optimization plan

The acceptance targets are at most 10% median proving-time overhead and 12%
proof-size overhead over non-ZK FLOCK for a declared range of large traces.
The current hiding PCS exceeds both targets. Its low mask block doubles the
committed message dimension, and its full blinder doubles the initial leaf
width. The first implementation stage optimizes deterministic computation,
bounds grinding during execution, and makes the remaining overhead measurable.

## Benchmark contract

Compare the same ordered BLAKE3-preimage relation, circuit dimensions, Secure
profile, hardware, and thread count. Preserve the public ZK API's registered
PCS and composed soundness floors. Report parameter differences rather than
treating the profile name as an identical composed security bound.

The benchmark warms both protocols, alternates sample order, verifies every
proof, and excludes setup and serialization from proving and verification
timings. It reports both the original serialized proof-object size and the
canonical proof transport, including the commitment and six-byte framing.
The digest vector, including its length prefix, is reported separately. The
size gate uses the largest sampled proof transport, not just its median.
PCS, VEIL, transcript, and initial-row byte counts expose structural costs;
initial rows are a subset of PCS bytes, not an additional component.

```sh
cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 15 --sizes 256,512,1024,2048,4096 --check-targets
```

The gate must fail until both targets pass at every selected shape. It does
not certify an untested trace range, timing tails, or a cryptographic theorem.
Only the existing registered shapes are accepted. Larger traces require new
circuit, PCS, soundness, sampling, grinding, oracle-budget, and formal-model
certificates before increasing the public batch limit.

## Implemented foundation

- Reuse immutable additive-transform tables keyed by the exact domain size
  and offset. The process-wide cache retains at most 131072 field elements
  (2 MiB) and 16 entries; it contains no witness data or randomness.
- Reduce each dot product once after XOR-accumulating unreduced field
  products. Batch affine sums before canonicalization, including ring
  linkage, and share that operation with the examples.
- Encode independent large VEIL columns in parallel while preserving their
  order and the sequential randomness draw order.
- Validate public vector/code dimensions with checked arithmetic before
  allocation and division, and reject malformed opening widths.
- Enforce outer and Ligerito grinding caps while searching, sharing the
  Ligerito adapter between production and examples. The simulator queries
  its shared oracle honestly for the same bounded first-success search.

These changes preserve accepted proof fields, transcript framing, randomness
order, and security parameters. An exhausted grind now stops at its cap;
the successful transcript is unchanged. This stage makes no stronger ZK claim.

A fixed-coin regression compares the entire serialized proof bundle against
upstream commit `73f5361`, with both one and four worker threads. The fixture
includes commitment, public statement, VEIL, PCS, and transcript fields; fixed
coins remain confined to the private test API.

### Foundation measurements

The [raw comparison](benchmarks/veil-foundation-2026-10-08.csv) was measured
on 2026-10-08 on an AMD Ryzen 7 7840HS, Rust 1.98.0, release mode with
`target-cpu=native`, eight workers, and 15 samples per shape. Upstream
`73f5361` was measured with this PR's identical benchmark harness, followed
by the foundation candidate; no other build or test ran during either sweep.
These are machine-specific observations from one before/after comparison,
not portable or statistically certified speedup guarantees.

| Hashes | Upstream ZK prove | Foundation ZK prove | Observed reduction |
| --- | --- | --- | --- |
| 256 | 18.396 ms | 13.179 ms | 28.4% |
| 512 | 20.886 ms | 15.757 ms | 24.6% |
| 1024 | 27.300 ms | 21.520 ms | 21.2% |
| 2048 | 52.234 ms | 47.726 ms | 8.6% |
| 4096 | 87.052 ms | 83.926 ms | 3.6% |

Proof format and size are unchanged; fresh coins account for small sampled
size differences. At 4096 hashes the foundation run's non-ZK median prove
time was 23.702 ms, giving 254.1% ZK proving overhead. Maximum sampled proof
transports were 452004 and 888244 bytes, giving 96.5% size overhead. Every
selected shape failed the 10%/12% gate, and the command exited with status 1.
The first-stage optimization is therefore not completion of the target.

## Compact PCS feasibility milestone

At 4096 hashes the pinned initial opening has 290 distinct rows, each carrying
128 field elements: 593920 bytes before salts, authentication paths, and
serialization. The non-ZK proof object is 451937 bytes. Thus the existing
initial rows alone exceed a 12% overhead budget at this shape. Faster kernels
cannot remove that wire-size constraint.

The next design must reduce initial openings and trace-sized blinding work.
Padding can be sized by a proved joint leakage rank only if it covers every
initial opened coordinate and exposed functional. Avoid a padding layout that
needlessly triggers another power-of-two transform. Removing the full blinder
also removes the current witness-independent uniform-fold boundary: the
replacement must hide recursive commitments, opened rows, sumcheck messages,
and the clear terminal residual. Initial-query hiding alone is insufficient.

Derive a joint witness-free simulator, actual operand/product distances,
additive soundness ledger, and concrete time/byte budget before replacing
the production PCS. Preserve binary-field ring linkage, commitment salts,
challenge distributions, and the fixed batched claim manifest. Proceed only
when the complete construction supports both acceptance targets.

## End to end ZK obligations

The existing Lean theorem proves statistical ZK for its uniform-coin formal
privacy view. Connecting it to production still requires:

1. Proving the Rust BLAKE3 relation implies the formal public projection.
2. Relating all serialized Rust proof fields and transcript operations to the
   formal view, including post-fold Ligerito processing.
3. Adding the computational hybrid for OS-seeded BLAKE3 XOF coin expansion.
4. Bounding remaining rejection loops and cumulative oracle use during
   execution, and extending these bounds for any new registered shapes.
5. Rechecking adaptive simulation with one shared oracle and fresh coins for
   every proof after any PCS change.

Keep [the security scope](SECURITY.md) explicit until those obligations are
discharged. Simulator regression tests and the Lean axiom audit are useful
checks; they do not replace the implementation correspondence argument.
