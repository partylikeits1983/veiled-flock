# Lean proofs

This directory contains generic masking and probability lemmas from the
earlier zk-FLOCK work. It does not formalize the active succinct VEIL protocol
or its Rust implementation.

```sh
cd lean
lake exe cache get
lake build
cd ..
scripts/lean-axioms.sh
```
