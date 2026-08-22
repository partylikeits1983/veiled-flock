# Benchmarks

Run the zk-FLOCK comparison from the repository root:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock
```

Generated results belong in `benchmarks/results/`, which is ignored by Git.

The benchmark constructs setup and public digests outside the timed loops.
`proof_bytes` serializes the commitment and proof but not the public digest
list. Prove/verify times and proof sizes are medians after one warm-up.

CI runs a five-sample batch-256 smoke benchmark:

```sh
bash scripts/veil-bench-check.sh
```

The default limits (3.5x prove, 3.5x verify, and 2.5x proof size relative to
plain FLOCK) are broad regression alarms, not performance targets or security
claims. Override them with `VEIL_BENCH_MAX_PROVE_OVERHEAD`,
`VEIL_BENCH_MAX_VERIFY_OVERHEAD`, and `VEIL_BENCH_MAX_SIZE_OVERHEAD` when
running an experiment.

The VEIL paper's ~3% prover-overhead result is for its own large-trace
proof-of-concept stack. This benchmark measures the complete fixed-digest
composition in this repository, including randomized witness generation, a
hiding Ligerito commitment/opening, transcript masking, and the native
`GF(2^128)` VEIL subproof. These numbers are not an implementation-to-
implementation reproduction of the paper's experiment.
