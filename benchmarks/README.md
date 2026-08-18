# Benchmarks

Run the zk-FLOCK comparison from the repository root:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock
```

Generated results belong in `benchmarks/results/`, which is ignored by Git.
