# Architecture

## Protocol composition

```text
secret preimages
      |
FLOCK witness + R1CS
      |
      +-- witness MLE --> stacked F128 ZK PCS --> shielded oracle view
      |
      +-- zerocheck / lincheck / ring switch / Ligerito messages --> v
                                                                    |
uniform h ----------------------------------------------------------+
                                                                    v
                                                               v' = v + h
                                                                    |
                   VEIL ZK R1CS eval proves C(v' - h) = 0 ---------+
                                                                    |
                     public statement + shielded view + v' + inner proof
```

The verifier never receives `v` and does not rerun the original decision directly
on unmasked messages.

## Field choice

The integration treats FLOCK's packed field `F128` as VEIL's protocol field. This
avoids expanding one exposed message into 128 separate base-field symbols and
matches the field in which zerocheck, lincheck, and ring-switch messages already
live.

VEIL's abstract protocols are field-generic, but its available Rust implementation
uses a two-adic prime field. `veil-f128` therefore implements the required
additive-NTT code and protocol kernels directly. It is a port of the construction,
not a type alias around the existing implementation.

## Repository boundaries

### `veil-f128`

Owns code-theoretic primitives, ZK dot product, ZK Hadamard, ZK R1CS evaluation,
query-budget types, and their simulators. It must not depend on BLAKE3 statement
semantics.

### `zk-flock-veil`

Owns the FLOCK adapter: public statement encoding, typed transcript events,
generic verifier contexts, stacked PCS integration, and compiled prove/verify
APIs. It is the only crate that depends directly on FLOCK internals.

### `zk-flock-sim`

Owns end-to-end simulation and distinguishing/negative-control experiments. Its
normal dependency graph must not include witness-generation or real-prover entry
points. Test-only attack fixtures live behind an explicit feature.

### `zk-flock-cli`

Owns reproducibility commands. It contains no protocol logic.

## Transcript ownership

Every event is exactly one of:

- **Public:** statement, profile, circuit digest, and deterministic metadata.
- **Shielded:** commitment/oracle data covered by the partially ZK PCS simulator.
- **Exposed:** witness-dependent `F128` values masked by the intermediate compiler.
- **Derived:** verifier challenges deterministically derived from prior events or
  sampled as public verifier coins.

No catch-all byte writes are allowed. Serialization must require a typed event and
classification.

For the first experiment, ring-switch partial evaluations and Ligerito's terminal
residual are exposed. This may increase the inner decision circuit, but it gives a
clear simulation story without changing recursion semantics. A later optimized
design may absorb them into the shielded PCS only after proving the corresponding
simulator and binding properties.

## Public API target

The eventual top-level API should distinguish security models in its types:

```text
prove_interactive(params, statement, witness, verifier_coins, prover_coins)
verify_interactive(params, statement, proof, verifier_coins)
simulate_interactive(params, statement, verifier_coins, simulator_coins)

prove_fs(params, statement, witness, prover_coins)
verify_fs(params, statement, proof)
simulate_fs_rom(params, statement, simulator_coins, programmable_oracle)
```

The transparent/debug inner system must use a different proof/profile type so it
cannot be confused with a zero-knowledge proof.

