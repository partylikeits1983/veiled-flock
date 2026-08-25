# keccak-bench

End-to-end keccak-f proving benchmark over the native chain prover and
the succinct-VEIL backend. The crate has two modes:

- **e2e bin** (`keccak_e2e`) — the full sweep: prove AND verify all
  three rows per point, print the row table, dump `--json`. This is the
  primary suite.
- **criterion target** (`keccak_criterion`) — statistical stage timing
  of the cheap stages only (witness, the three verifies, one
  succinct-chain prove shape). It complements the bin; it does not
  replace it: the e2e rows are multi-metric records (four timed
  sections, proof size, params, cross-row slowdown), while criterion
  models single-metric closures — so criterion takes only the stages
  where its statistics beat best-of-N.

## Layout

```
benches/keccak-bench/
├── Cargo.toml
├── README.md
├── benches/
│   └── keccak_criterion.rs   criterion stage-timing target
└── src/
    ├── lib.rs                keccak witness builders + native-rate
    │                         calibration; the generic harness comes
    │                         from the `bench-harness` crate
    │                         (`benches/harness`)
    ├── keccak.rs             the keccak_e2e bin: the SPEC (titles +
    │                         sweep-bound flag), sweep, row functions
    └── tests.rs              all unit tests (domain + sweep shape +
                              the real-spec pin), attached to the bin
                              as a #[path] module
```

`cargo test -p keccak-bench` runs every unit test through the bin
target: `src/tests.rs` covers the domain lib (through the crate's
public API), the sweep shape, and the real-spec pin; the harness's own
tests live in `bench-harness`.

## e2e mode

Run under the tuned `bench` profile — never bare `--release`, which
silently changes codegen (the workspace tunes `[profile.bench]` only):

```sh
cargo run --profile bench -p keccak-bench --bin keccak_e2e
```

Flags (each flag wins over its env-var fallback):

| Flag | Env fallback | Meaning |
|---|---|---|
| `--smoke` | `BENCH_SMOKE=1` | One small sweep point (n = 64), 1 timing run. |
| `--runs <1..=16>` | derived from smoke | Timing runs per row (best-of-N). |
| `--max-log <6..=19>` | `BENCH_KECCAK_MAX_LOG` | Sweep bound: n = 2^6, 2^8, … 2^max-log (steps by 2; m = 16 + log). Raise above 12 only after measuring — configs stop at m = 35 but the upper range is unrunnable on a workstation. Validated at parse time even in smoke mode — stricter than the pre-split bench, which read the env var only on the non-smoke path. |
| `--json <path>` | — | Write the rows as JSON for cross-commit tracking. |

```sh
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --smoke
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --json results.json
```

The binary lands at `target/release/keccak_e2e`. Profile mapping and
the re-baseline caveat live in `benches/README.md`.

## criterion mode

```sh
cargo bench -p keccak-bench -- --save-baseline main
```

Scope: witness generation, native chain verify, succinct verify (both
relations), succinct-chain prove — all at n = 64. The native chain
prove and the succinct public-chain prove stay out; the e2e bin owns
them. Regression comparison (`-- --baseline main`) is a post-merge
workflow.

Measured on 2026-08-25: witness ~1.5 ms (the bit-level `keccak_f` makes
even witness generation ms-scale), native verify ~3.4 ms, succinct
verify ~5.2 ms (includes the public-linkage equality check, matching the
e2e `verify` column — a DELIBERATE divergence from blake3's criterion
convention, which times the circuit verify only; keccak's linkage check
is a pure equality, not a hash recompute), succinct-chain verify
~4.5 ms, succinct-chain prove ~14 ms. The prove group reuses one hoisted setup (warm-setup
steady-state); the e2e `prove` column pays any per-run setup effects —
the two numbers are different statistics.

## Results (partial run, 2026-08-25)

One budgeted partial run: `--runs 1 --max-log 8` (single timing run per
row, n = 64 and 256 only), Apple Silicon macOS. NOT the full sweep
(default reaches n = 4096). The native rate baseline is the bit-level
`keccak_f` chain (~0.04 Mperm/s), so slowdown factors are small.

| backend | relation | n_real | prove | verify | proof bytes | slowdown |
|---|---|---|---|---|---|---|
| native-ligerito | chain-in-circuit | 64 | 13.9 ms | 3.5 ms | 273 KB | 9.3x |
| veil-succinct | public-chain | 64 | 19.4 ms | 5.4 ms | 580 KB | 12.9x |
| veil-succinct | chain-in-circuit | 64 | 18.4 ms | 4.5 ms | 581 KB | 12.3x |
| native-ligerito | chain-in-circuit | 256 | 14.6 ms | 3.8 ms | 296 KB | 2.4x |
| veil-succinct | public-chain | 256 | 37.2 ms | 7.6 ms | 613 KB | 6.2x |
| veil-succinct | chain-in-circuit | 256 | 32.7 ms | 4.8 ms | 614 KB | 5.4x |

Params: native `PcsParams { m: 22|24, log_inv_rate: 1, log_batch_size: 6,
profile: Fast, zk: false }`; succinct the same with `zk: true`. Rows
without equal params are not comparable. The two `chain-in-circuit`
backends prove the SAME relation — compare those rows for the cost of
the zk masking layer. See `benches/README.md` for the column and
relation definitions.

## Adding a row function

1. Extend the sweep or add a shape in `src/keccak.rs` (env-free — take
   `smoke` and overrides as parameters; unit-test the shape in
   `src/tests.rs`).
2. Add a row function in the rows section of `src/keccak.rs`: take
   `(n, native_rate, runs)`, time with `time_best`, build the row with
   `BenchRow::new` (backend, relation, and params are mandatory), and
   assert verify — a broken proof is a bench failure, not a data point.
3. Wire it into `main`'s sweep loop with `bench.push(...)` — the driver
   prints the per-row progress table.
4. Fresh `FsChallenger`/`ZkRng` inside every timed closure — verify
   consumes the Fiat–Shamir transcript.
