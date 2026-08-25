# blake3-bench

End-to-end BLAKE3 proving benchmark over both veil-f128 backends, plus
the shared harness that `keccak-bench` reuses. The crate has two modes:

- **e2e bin** (`blake3_e2e`) — the full sweeps: prove AND verify every
  row, print the row table, dump `--json`. This is the primary suite.
- **criterion target** (`blake3_criterion`) — statistical stage timing
  of the cheap stages only (witness, both verifies, one succinct prove
  shape). It complements the bin; it does not replace it: the e2e rows
  are multi-metric records (four timed sections, proof size, params,
  cross-row slowdown) with expensive iterations, while criterion models
  single-metric closures — so criterion takes only the stages where its
  statistics beat best-of-N.

## Layout

```
benches/blake3-bench/
├── Cargo.toml
├── README.md
├── benches/
│   └── blake3_criterion.rs   criterion stage-timing target
└── src/
    ├── lib.rs                shared harness (timer, rows, table, JSON,
    │                         env parsing) — keccak-bench reuses it via
    │                         a path dependency
    ├── blake3.rs             the blake3_e2e bin: flags, sweeps, row
    │                         functions
    └── tests.rs              all unit tests (harness + bin), attached
                              to the bin as a #[path] module
```

`cargo test -p blake3-bench` runs every unit test through the bin
target: `src/tests.rs` covers the harness (through the crate's public
API) and the bin's flag parsing and sweep shapes.

## e2e mode

Run under the tuned `bench` profile — never bare `--release`, which
silently changes codegen (the workspace tunes `[profile.bench]` only):

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e
```

Flags (each flag wins over its env-var fallback):

| Flag | Env fallback | Meaning |
|---|---|---|
| `--smoke` | `BENCH_SMOKE=1` | One small row per sweep, 1 timing run. |
| `--runs <1..=16>` | derived from smoke | Timing runs per row (best-of-N). |
| `--framed-max-log <1..=14>` | `BENCH_FRAMED_MAX_LOG` | Framed sweep bound. Read the memory model in `src/blake3.rs` before raising it above 6. |
| `--json <path>` | — | Write the rows as JSON for cross-commit tracking. |

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e -- --smoke
cargo run --profile bench -p blake3-bench --bin blake3_e2e -- --json results.json
```

The binary lands at `target/release/blake3_e2e` (`--profile bench` maps
to the `release` output directory). Note `--profile bench` builds the
dependency crates under the bench profile too, while `cargo bench`
builds dependencies under `release`; rows measured before this layout
change are close but not codegen-identical — re-baseline once.

## criterion mode

```sh
cargo bench -p blake3-bench -- --save-baseline main
```

Scope: witness generation, framed verify (n = 2), succinct verify
(n = 256), succinct prove (one shape at the 256-slot floor). The framed
prove stays out — its multi-second iterations gain nothing from
criterion's 10-sample floor; the e2e bin owns it. Regression comparison
(`-- --baseline main`) is a post-merge workflow.

Measured on 2026-08-25: witness ~21 µs, framed verify ~77 ms, succinct
verify ~4.9 ms, succinct prove ~13 ms. CAUTION on the prove number: the
criterion group reuses one setup, so it measures the warm-setup
steady-state prove. The first prove on a fresh setup pays a lazy
one-time cost of ~0.4 s, and THAT is what the e2e `prove` column
reports (which is why the e2e succinct prove times are nearly flat
across n = 256..2048). The two numbers are different statistics — do
not compare them.

## Results (partial run, 2026-08-25)

One budgeted partial run: `--runs 1` (single timing run per row, not
best-of-3), default sweeps, Apple Silicon macOS. NOT a full sweep — the
framed sweep beyond n = 64 is hours.

| backend | relation | n_real | prove | verify | proof bytes | slowdown |
|---|---|---|---|---|---|---|
| veil-framed | public-chain | 2 | 604 ms | 77 ms | 5.9 MB | 1.9e6x |
| veil-framed | public-chain | 8 | 1.20 s | 322 ms | 23 MB | 9.6e5x |
| veil-framed | public-chain | 32 | 5.15 s | 1.60 s | 92 MB | 1.0e6x |
| veil-framed | public-chain | 64 | 11.6 s | 4.73 s | 185 MB | 1.2e6x |
| veil-succinct | public-chain | 256 | 487 ms | 7.6 ms | 579 KB | 1.2e4x |
| veil-succinct | public-chain | 512 | 484 ms | 5.8 ms | 591 KB | 6.1e3x |
| veil-succinct | public-chain | 1024 | 443 ms | 6.0 ms | 611 KB | 2.8e3x |
| veil-succinct | public-chain | 2048 | 468 ms | 6.7 ms | 624 KB | 1.5e3x |

Params: framed `BlockR1csParameters { query_count: 128, inverse_rate: 4 }`;
succinct `PcsParams { m: 22..25, log_inv_rate: 1, log_batch_size: 6,
profile: Fast, zk: true }`. Rows without equal params are not
comparable. See `benches/README.md` for the column and relation
definitions.

## Adding a row function

1. Put the sweep shape in the sweeps section of `src/blake3.rs` (env-free —
   take `smoke` and overrides as parameters; unit-test the shape).
2. Add a row function in the rows section of `src/blake3.rs`: take
   `(n, native_rate, runs)`, time with `time_best`, build the row with
   `BenchRow::new` (backend, relation, and params are mandatory), and
   assert verify — a broken proof is a bench failure, not a data point.
3. Wire the sweep loop into `run` with a per-row progress table.
4. Fresh `FsChallenger`/`ZkRng` inside every timed closure — verify
   consumes the Fiat–Shamir transcript.
