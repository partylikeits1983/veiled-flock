# Benchmarks

Generated results go in `benchmarks/results/` and are ignored by Git.

Every result record must include source revisions, dirty-state flags, profile ID,
host/CPU, thread count, compiler version, iteration count, and median plus raw
samples for proving time, verification time, proof bytes, and peak memory.

Required comparisons:

1. current FLOCK baseline;
2. transparent compiler plumbing;
3. interactive zk-FLOCK with VEIL; and
4. Fiat-Shamir zk-FLOCK, when implemented.
