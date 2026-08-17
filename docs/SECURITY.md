# Experimental security model

## Intended statement privacy

For the first profile, the ordered digest vector, batch size, circuit identity,
and parameter profile are public. The 256 64-byte preimages and every other R1CS
witness value are secret.

The protocol does not attempt to hide batch size, circuit shape, proof length,
parameter schedule, timing, memory access, or prover-side hardware behavior.

## Three deliberately separate modes

### Interactive ZK target

The primary research target is perfect zero-knowledge in VEIL's public-coin IOP
model, for non-adaptive code queries within a hard registered query budget. The
simulator receives the public statement and verifier randomness but no witness.

### Fiat-Shamir experiment

The noninteractive artifact is computational and uses a programmable-random-oracle
simulation. This is not covered merely by completing the interactive VEIL port.
The report must identify its hash, domain separation, programming interface, and
any rewinding or abort behavior.

### Transparent debug mode

A transparent inner checker may be used while plumbing the compiler. It provides
neither transcript privacy nor a ZK claim and must serialize under a distinct
profile identifier.

## Required invariants

1. Statement binding precedes every witness commitment and challenge.
2. The circuit digest commits to the exact relation and matrix layout.
3. Every witness-dependent transcript value is shielded or exposed-and-masked.
4. Query counts never exceed the randomness dimension certified for the code.
5. Random padding is independent across commitments/rounds where the proof needs
   independence.
6. The simulator's module graph cannot call witness generation or the real prover.
7. Registered profiles are immutable; unknown dimensions fail closed.
8. Proof decoding rejects trailing bytes, wrong event order, and wrong lengths.
9. Real and simulated transcripts have identical public shape.
10. The FS and interactive claims are never represented by the same profile ID.

## What tests can and cannot establish

Distribution tests, witness-pair distinguishers, and negative controls are
essential regression tests. They do not prove zero-knowledge over `F128`.
Security relies on exact projection/rank or code theorems, the VEIL simulator
composition, the PCS binding assumptions, and a separate FS argument where used.

## Experimental release label

Until the code properties, compiler adaptation, and trusted-base correspondence
have been reviewed, every binary and proof format must display:

```text
EXPERIMENTAL: not audited, not production-safe, no protection for real secrets
```

