# Architecture Diagrams

ASCII sequence and class diagrams for the three workspace crates. Rendered as plain
text: no Mermaid, no images, max 100 columns, readable in a terminal and on GitHub.

**Mirror rule.** This directory is canonical and tracked. `.claude/architecture/` holds
a byte-for-byte copy produced by `cp docs/architecture/*.md .claude/architecture/`, for
agent-side loads. That copy is **machine-local**: `.claude/` is not tracked in this
repository, so the mirror is absent on a fresh clone and must be regenerated with the
command above — never hand-edited. `scripts/check-diagrams.sh` skips the mirror check
when the directory is absent and fails when it exists and differs.

| Diagram | Contents |
|---|---|
| [flock-core](flock-core-sequence.md) | Prover, verifier, PCS internals; Fiat-Shamir points |
| [veil-f128](veil-f128-sequence.md) | Masked transcript, additive RS code, simulator |
| [flock-prover](flock-prover-sequence.md) | CLI, prove, verify, simulator and certificate |
| [class diagram](class-diagram.md) | Crate deps, per-crate types, cross-crate edges |

Anchors in these files are `path/to/file.rs:LINE`, repo-root-relative, and point at
definitions unless the entry says otherwise. They rot when code moves;
`scripts/check-diagrams.sh` bounds the damage by failing when an anchored path is
missing, is not repo-root-relative, or names a line past end-of-file.

Run the checker after any edit:

```sh
scripts/check-diagrams.sh
```
