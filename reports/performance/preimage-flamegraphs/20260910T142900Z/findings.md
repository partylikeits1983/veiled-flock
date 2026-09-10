# Findings from the preimage profiles

[Full report](report.md) · [All 28 interactive SVGs](index.html) · [Exact hotspot counts](hotspots.csv)

The clearest follow-up target is the column-gather loop in `CscCircuit::fold_alpha_batched`. It dominates verification at both endpoints and remains dominant in the repeats. Large proving workloads distribute more of their sampled work across field kernels, transforms, and scheduling.

These are findings about the recorded workloads. Every primary capture ran on battery, with charge declining from 27% to 11%; the small repeats ended at 8% with an early battery warning. The large repeats ran about 100 minutes later on AC power while charging. The first episode lacks an immediate closing baseline. The report documents these deviations from the planned AC-only protocol. Neither flamegraph widths nor the repeat comparisons establish a controlled speedup.

## The dominant verification kernel

The table shows **self sample-row share** for the same `fold_alpha_batched` column-gather closure. The denominator is each capture's usable backtrace rows across all threads, not wall-clock latency.

| Workload | 64 hashes: primary / repeat | 4,096 hashes: primary / repeat |
| --- | ---: | ---: |
| FLOCK verify | 75.89% / 76.15% | 59.85% / 59.92% |
| Full-ZK verify | 61.99% / 63.23% | 55.60% / 56.07% |

The corresponding primary proving shares decline from **49.41% to 9.52%** for FLOCK and from **34.63% to 8.48%** for Full-ZK as the input grows from 64 to 4,096 hashes. The operation still matters at the larger size, but accounts for a smaller fraction of a broader proving workload.

The original method begins at [lincheck.rs:326](source/locations/crates/flock-core/src/lincheck.rs#L326). Its closure walks each CSC column's A and B row-index ranges, gathers the corresponding `eq_inner` entries, and computes `alpha * sa + sb`. This is a symbol-name and source inspection mapping, not instruction-address line attribution. The automatic source lookup marks this trait-qualified symbol “external or unresolved” because its demangled name begins with `<`; the copied module supplies the missing repository mapping.

**First experiment:** microbenchmark this column gather at the recorded circuit dimensions. Measure its serial and parallel paths, column lengths, and memory locality. Change one column partitioning or gather-layout choice at a time; preserve row multiplicities, field arithmetic, and exact outputs. Compare kernel results with the original implementation, run protocol tests, then collect interleaved unprofiled timings and endpoint profiles under consistent power conditions. The observed share does not predict the speedup of a proposed change.

A concrete candidate is to tile adjacent columns and scan their already sorted row lists in windows that reuse `eq_inner` cache lines. Preserve every stored A/B entry, separate accumulators, and zero-column outputs; report preprocessing time and memory separately. The serial/parallel switch is at **4,096 columns**, not hashes ([lincheck.rs:944](source/locations/crates/flock-core/src/lincheck.rs#L944)). Benchmark below, at, and above that column count under both one-worker and eight-worker pools with representative BLAKE3 sparsity.

## Large proving workloads

Several distinct kernels become visible at 4,096 hashes:

| Kernel | FLOCK prove self share | Full-ZK prove self share | Original source |
| --- | ---: | ---: | --- |
| `butterfly_row_pair` | 5.08% | 8.06% | [portable NTT kernel:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| AArch64 `fold_pairs` | 6.27% | — | [field slice kernel:8](source/locations/crates/flock-core/src/field/f128_slice/aarch64.rs#L8) |
| `accumulate_convert_with_s_hat_v` | 4.84% | — | [zerocheck kernel:51](source/locations/crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs#L51) |

A dash means the value is not selected for this comparison; it does not mean zero samples. “Portable” is a source-module name and does not establish that generated code lacks hardware field instructions.

**Second experiment:** benchmark the observed transform and field kernels at the actual large-case dimensions, then vary subgroup size or task granularity. The implementation already performs fusion, so inspect the existing algorithm before adding another pass or proposing more fusion. Require scalar-equivalent outputs and compare unprofiled proving latency after the kernel checks.

Scheduling is also visible: the disjoint leaf-category heuristic assigns it a mean **13.45%** across the 28 equally weighted primary cases. FLOCK proving at 4,096 hashes has `swtch_pri` self share **12.95%** in the primary and **11.97%** in its resumed repeat. These sampled Running-stack frames describe observed scheduling activity, not time blocked off CPU.

**Third experiment:** inspect task sizes beneath the relevant Rayon callers and alter one partition or parallel threshold at a time. Measure task counts together with latency. Preserve the one-worker shared verifier policy; Full-ZK's outer verification work also runs outside that pool. A reduction in scheduling sample share alone does not prove a latency improvement.

## Timing and size context

In the original unprofiled baseline, increasing the hash count 64-fold increases FLOCK proving latency **5.16×** and verification latency **1.25×**. Full-ZK changes are **4.45×** and **1.37×**. Full-ZK proving costs **2.88–4.31×** FLOCK across the seven rows; Full-ZK verification costs **0.81–0.96×** FLOCK. These are measured baseline ratios, not a prediction from sample shares.

The small Full-ZK cases pad to 256 slots, consistent with their similar 64/128/256 timings and proof sizes. Median size overhead declines from **191.7%** at 64 hashes to **96.0%** at 4,096; sizes come from serialization, independently of profiling. Full-ZK sizes vary with randomness, and the report retains their measured ranges.

The largest original-before/final-after timing change is **8.1%**; the largest change within the resumed baseline pair is **6.7%**. The normal/symbol comparison reaches **10.7%** and combines build effects with measurement variability. Even within the first episode, Full-ZK verification at 64 hashes has a **14.0%** higher profiled call rate in its repeat. Stable hotspot identity is therefore stronger evidence here than a small timing difference.

All 44 accepted recordings retain original XML, trace archives, harness metadata, and recorder/export statuses. Corrected SVGs preserve every accepted sample count while repairing semicolons inside Rust frame names. The eight smokes are quality checks; the analysis above uses primary captures and full-duration endpoint repeats. The interrupted large FLOCK-prove repeat remains archived and excluded.
