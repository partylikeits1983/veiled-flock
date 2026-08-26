# keccak-bench

An end-to-end keccak-f proving benchmark on the native chain prover and the
succinct-VEIL backend. The generic harness comes from `bench-harness`
(`benches/harness`).

The `keccak_e2e` bin is the primary suite. It runs the full sweep, it proves and
verifies all three rows per point, and it writes `--json`. The
`keccak_criterion` target adds statistical timing for the stages that have short
iterations. It completes the bin and does not replace it, because an e2e row is
a record of four timed sections, a proof size, the params, and a slowdown, but
criterion models one metric per closure.

## Layout

```
benches/keccak-bench/
├── benches/keccak_criterion.rs   criterion stage timing
└── src/
    ├── lib.rs      chain builders, linkage check, native-rate calibration
    ├── keccak.rs   the keccak_e2e bin: the SPEC, the sweep, the row functions
    └── tests.rs    unit tests, attached to the bin as a #[path] module
```

`cargo test -p keccak-bench` runs the tests through the bin target. They cover
the domain lib, the sweep shape, and a pin on the real flag spec. The tests of
the harness live in `bench-harness`.

## e2e mode

```sh
cargo run --profile bench -p keccak-bench --bin keccak_e2e
```

| Flag | Env fallback | Meaning |
|---|---|---|
| `--smoke` | `BENCH_SMOKE=1` | One sweep point at n = 64, one timing run. |
| `--runs <1..=16>` | from smoke | Timing runs per row, best of N. |
| `--max-log <6..=19>` | `BENCH_KECCAK_MAX_LOG` | The sweep bound: n = 2^6, 2^8, up to 2^max-log, in steps of 2. Raise it above 12 only after you measure. The parser validates it even in smoke mode. |
| `--json <path>` | — | Write the rows as JSON. |

A flag always wins over its environment variable. The bin lands at
`target/release/keccak_e2e`. For the profile mapping and the baseline caveat,
refer to `benches/README.md`.

## criterion mode

```sh
cargo bench -p keccak-bench -- --save-baseline main
```

Scope: witness generation, native chain verify, succinct verify for the two
relations, and succinct-chain prove, all at n = 64. The native chain prove and
the succinct public-chain prove stay in the bin. A comparison against a baseline
is a task for the time after the merge.

The prove group uses `Flat` and `sample_size(10)`, which fixes the count of the
iterations per sample. An "unable to complete N samples" warning is a defect of
the configuration, not a pass.

The succinct verify group includes the public-linkage equality check, so it
matches the e2e `verify` column. This is a deliberate divergence from the blake3
convention, which times the circuit verify only, because the keccak check is a
pure equality and not a hash recompute. The prove group reuses one setup, so it
gives the steady state of a warm setup, and the e2e column pays the per-run
setup cost.

## Results

Full sweep on Apple Silicon macOS, 2026-08-26, best of 3. The table gives the
two ends of the sweep, and `--json` gives all 12 rows. The native rate baseline
is the bit-level `keccak_f` chain, so the slowdown factors are small.

| backend | relation | n_real | prove | verify | bytes | slowdown |
|---|---|---|---|---|---|---|
| native-ligerito | chain-in-circuit | 64 | 7 ms | 3.5 ms | 273 KB | 4.4x |
| veil-succinct | public-chain | 64 | 15 ms | 5.3 ms | 580 KB | 9.7x |
| veil-succinct | chain-in-circuit | 64 | 15 ms | 4.7 ms | 581 KB | 9.6x |
| native-ligerito | chain-in-circuit | 4096 | 53 ms | 3.9 ms | 365 KB | 0.54x |
| veil-succinct | public-chain | 4096 | 376 ms | 54 ms | 678 KB | 3.8x |
| veil-succinct | chain-in-circuit | 4096 | 340 ms | 5.3 ms | 679 KB | 3.5x |

The two `chain-in-circuit` rows prove the same relation, so a comparison of the
two gives the cost of the zk mask layer. A slowdown below 1.0 means that the
prover is faster than the calibrated native rate. Nobody has analysed that
result yet, so do not quote it as a speedup.

Params: native `PcsParams { m: 22|24, log_inv_rate: 1, log_batch_size: 6,
profile: Fast, zk: false }`, and succinct the same with `zk: true`.

## How to add a row function

1. Extend the sweep or add a shape in `src/keccak.rs`. Take `smoke` and the
   overrides as parameters, and add a unit test for the shape.
2. Add the row function in the rows section. Take `(n, native_rate, runs)`, time
   it with `time_best`, and build the row with `BenchRow::new`.
3. Assert that verify returns `Ok`. A broken proof is a failure of the bench.
4. Wire the row into the sweep loop of `main` with `bench.push(...)`.
5. Make a fresh `FsChallenger` and a fresh `ZkRng` in each timed closure,
   because verify consumes the Fiat-Shamir transcript.
