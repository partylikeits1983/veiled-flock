# no-std and WebAssembly

VEIL-FLOCK's reusable cryptographic libraries can build without Rust's
standard library. This makes the protocol and verification code usable in
environments that provide `core` and `alloc` but not operating-system services,
including `wasm32-unknown-unknown` and constrained embedding targets.

This support is deliberately scoped. It is not a claim that every native
workflow, especially production proof generation, is available without a host
environment.

## Feature model

`flock-core`, `veil-f128`, and `flock-prover` default to `std` and `parallel`.
The `parallel` feature requires `std` and enables Rayon. Disable default
features to use the serial no-std build:

```toml
[dependencies]
flock-core = { path = "../flock-core", default-features = false }
veil-f128 = { path = "../veil-f128", default-features = false }
flock-prover = { path = "../flock-prover", default-features = false }
```

Check the supported library configurations from the workspace root:

```sh
cargo check --locked -p flock-core --no-default-features
cargo check --locked -p veil-f128 --no-default-features
cargo check --locked -p flock-prover --no-default-features
```

The no-std surface includes the FLOCK protocol, PCS, VEIL backend, proof
verification, and the BLAKE3-preimage relation. The following facilities
intentionally require `std`:

- Command-line binaries and Cargo examples.
- Proof-bundle file I/O.
- TOML parsing and serialization for Ligerito configurations.
- The programmable-oracle simulator and host-specific thread-pool setup.

Ligerito's production profile can still be selected without TOML at runtime:
the no-std build derives the registered profile values used by the protocol.

## Proving and randomness

Secure zero-knowledge proofs need unpredictable mask randomness. The ordinary
`Blake3PreimageZkSetup::prove` API draws that randomness from the operating
system and is therefore available only with `std`.

The no-std benchmark path enables the explicitly named
`insecure-deterministic-masks` feature and calls `prove_with_rng` with a
deterministic seed. This is suitable for reproducible tests and performance
measurement only; it must not be used to create production zero-knowledge
proofs. No-std verification remains available without that feature.

## Compatibility behavior

When `std` or `parallel` is disabled, the internal `flock-compat` crate
provides only the APIs used by this workspace. It is not a general replacement
for `std` or Rayon.

| Native API shape | no-std behavior |
| --- | --- |
| `HashMap` and `HashSet` | `BTreeMap` and `BTreeSet` |
| Rayon-style iterators and `join` | Execute serially |
| Thread-pool configuration | No-op; reported thread count is one |
| Environment variables | Unavailable |
| `Instant` timing | Always reports zero elapsed time |
| Synchronization | Minimal atomics-backed primitives; not a substitute for a host threading runtime |

The serial path preserves the implementation's iterator-oriented structure, so
the protocol does not need a separate WASM implementation. It does not
preserve native parallel throughput.

## WebAssembly benchmark export

`flock-wasm-bench` builds a `cdylib` for
`wasm32-unknown-unknown` and exports a benchmark for the VEIL BLAKE3-preimage
prove/verify path:

```sh
rustup target add wasm32-unknown-unknown
cargo build --locked -p flock-wasm-bench \
  --target wasm32-unknown-unknown --release
```

The generated module imports `env.performance_now`, which the embedding host
must provide as a millisecond clock. It exports:

- `veiled_flock_wasm_bench_max_blocks`
- `veiled_flock_wasm_bench_result_size`
- `veiled_flock_wasm_bench_blake3_preimage`

The last function receives a block count, sample count, and pointer to a
`VeiledFlockWasmBenchResult`. It returns a status code and writes the best
prove and verify times into that result. This crate is a low-level benchmark
ABI, not a browser binding or a general-purpose proof serialization interface.

## Native builds

Keep the default features for native applications that need parallel proving,
OS-provided randomness, files, or CLI tooling. The no-std configuration is a
portability option for library consumers, while the default configuration
remains the supported operational path for native proof generation.
