# blake3-bench

An end-to-end BLAKE3 proving benchmark on the two veil-f128 backends. The
generic harness comes from `bench-harness` (`benches/harness`).

The `blake3_e2e` bin is the primary suite. It runs the full sweeps, it proves
and verifies every row, and it writes `--json`. The `blake3_criterion` target
adds statistical timing for the stages that have short iterations. It completes
the bin and does not replace it, because an e2e row is a record of four timed
sections, a proof size, the params, and a slowdown, but criterion models one
metric per closure.

## Layout

```
benches/blake3-bench/
├── benches/blake3_criterion.rs   criterion stage timing
└── src/
    ├── lib.rs      chain builder, public linkage check, native-rate calibration
    ├── blake3.rs   the blake3_e2e bin: the SPEC, the sweeps, the row functions
    └── tests.rs    unit tests, attached to the bin as a #[path] module
```

`cargo test -p blake3-bench` runs the tests through the bin target. They cover
the domain lib, the sweep shapes, and a pin on the real flag spec. The tests of
the harness live in `bench-harness`.

## e2e mode

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e
```

| Flag | Env fallback | Meaning |
|---|---|---|
| `--smoke` | `BENCH_SMOKE=1` | One small row per sweep, one timing run. |
| `--runs <1..=16>` | from smoke | Timing runs per row, best of N. |
| `--framed-max-log <1..=14>` | `BENCH_FRAMED_MAX_LOG` | The framed sweep bound. Read the memory model below before you raise it above 6. |
| `--json <path>` | — | Write the rows as JSON. |

A flag always wins over its environment variable. The bin lands at
`target/release/blake3_e2e`. For the profile mapping and the baseline caveat,
refer to `benches/README.md`.

### Framed memory model

Let `m = 14 + n_blocks_log`, and let `N = 2^m` be the count of the witness bits.
`VeiledBlake3Setup::prove` expands z, a, and b to one `F128` per witness bit,
which is `3 * 16 * N` bytes. `prove_block_r1cs` commits vectors of length
`N + 6` and `2N + 2` at inverse rate 4. At `n_blocks = 64` that is about 50 MB
plus about 0.5 GB of codewords, which is near the 1 GB budget. At
`n_blocks = 1024` it is about 805 MB plus codewords of several GB.

## criterion mode

```sh
cargo bench -p blake3-bench -- --save-baseline main
```

Scope: witness generation, framed verify at n = 2, succinct verify at n = 256,
and succinct prove at the 256-slot floor. The framed prove stays in the bin,
because its iterations are too long for the 10-sample floor of criterion. A
comparison against a baseline is a task for the time after the merge.

The prove group uses `Flat` and `sample_size(10)`, which fixes the count of the
iterations per sample. An "unable to complete N samples" warning is a defect of
the configuration, not a pass.

Two divergences from the e2e columns. The verify groups time the circuit verify
only and leave out the linkage recompute. The prove group reuses one setup, so
it gives the steady state of a warm setup, but the first prove on a fresh setup
pays about 0.4 s and the e2e column reports that. Do not compare the numbers.

## Results

Full sweep on Apple Silicon macOS, 2026-08-26, best of 3. Every row is
`public-chain`. The table gives the two ends of each sweep, and `--json` gives
all 10 rows.

| backend | n_real | prove | verify | bytes | slowdown |
|---|---|---|---|---|---|
| veil-framed | 2 | 0.154 s | 75 ms | 5.9 MB | 5.8e5x |
| veil-framed | 64 | 12.3 s | 3.60 s | 185 MB | 1.4e6x |
| veil-succinct | 256 | 0.014 s | 4.6 ms | 580 KB | 403x |
| veil-succinct | 2048 | 0.039 s | 6.3 ms | 624 KB | 143x |

Params: framed `BlockR1csParameters { query_count: 128, inverse_rate: 4 }`, and
succinct `PcsParams { m: 22..25, log_inv_rate: 1, log_batch_size: 6, profile:
Fast, zk: true }`.

## How to add a row function

1. Put the sweep shape in the sweeps section of `src/blake3.rs`. Take `smoke`
   and the overrides as parameters, and add a unit test for the shape.
2. Add the row function in the rows section. Take `(n, native_rate, runs)`, time
   it with `time_best`, and build the row with `BenchRow::new`.
3. Assert that verify returns `Ok`. A broken proof is a failure of the bench.
4. Wire the sweep into `main` with `bench.push(...)`.
5. Make a fresh `FsChallenger` and a fresh `ZkRng` in each timed closure,
   because verify consumes the Fiat-Shamir transcript.
