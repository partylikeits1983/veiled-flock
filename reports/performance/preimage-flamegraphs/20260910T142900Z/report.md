# BLAKE3 preimage flamegraph report

Completed 28 primary captures and eight endpoint repeats. [Open the flamegraph gallery](index.html). Fresh unprofiled timing medians and proof sizes are below; the [historical reference](reference.csv) is a separate series.

**Power-condition limitation.** Capture conditions departed from the planned AC-only protocol. All 56 boundary observations for the 28 primary captures report battery operation, with charge declining from 27% to 11%. The four small endpoint repeats ran at 11%–8%, ending with an early battery warning. The four resumed large endpoint repeats ran approximately 100 minutes later on AC power while charging, at 46%–51%. The recordings describe the observed workloads; these changed conditions and the missing immediate closing baseline limit controlled timing comparisons. Recorded load averages include the profiling workload, and the available thermal observations do not establish constant CPU clocks. See the [first primary](cases/flock-prove-0064/primary-001/attempt.json), [last small repeat](cases/full-zk-verify-0064/repeat-001/attempt.json), and [resume observations](resume.json).

[Read the findings and source-guided follow-up experiments](findings.md). This power caveat, the findings link, and a clarification that the sample denominator applies to hotspot percentages were added during final evidence review. The [unaltered generated report](report-generated.md) and [editorial provenance](editorial-review.json) preserve the distinction between generated metrics and reviewed commentary.

**Report processing correction.** The displayed stacks and SVGs were regenerated from the archived raw XML after capture to correct semicolons embedded in Rust array type names. An embedded semicolon within one frame is displayed as `；` (fullwidth semicolon); ASCII `;` remains the separator between frames. The original XML, original collapsed stacks, and original SVGs are preserved. [Report processing provenance](report-processing.json) records the inputs, preserved originals, and revised reporting tools separately from the measured source snapshot.

**Two measurement episodes.** All 28 primary captures, the four 64-hash repeats, and the original normal/symbol baselines belong to the first episode. After a pause, the four 4,096-hash repeats were captured in a second episode, bracketed by a new [resume baseline](baseline-resume-before.csv) and the [final baseline](baseline-after.csv). The primary episode has no immediate closing baseline. Original-before versus final-after differences are cross-session changes, not drift measured across an uninterrupted primary series. [Resume provenance](resume.json) records the resumed controller separately and verifies that the registered workload, helper, Cargo, and profiler binaries retain their original identities.

## Environment and measurement

CPU: Apple M1 Pro. Memory: 17179869184 bytes. Branch: `chore/preimage-flamegraphs`. Base revision: `73f5361629a2683b5e18bc084c7b64a0ab77fe05`. Frozen source identity: `54cc47530ad38ffbb467b0a42f1b2fb66bc8eb5f1f4b08ef800c31a0ac76b72c`. Toolchain: `1.98.0`. Profiler: flamegraph-flamegraph 0.6.13. [Run manifest](manifest.json) records OS/Xcode versions, build settings, tool paths and checksums, power settings, and load observations.

The reference used an Apple M2 Pro with 16 GiB and revision `9a369670ba5ad3d9a450b859572760b179085666`; machine/revision differences prevent interpreting a timing difference as a code regression. The current series uses release optimization and `target-cpu=native`, with separately prebuilt normal and debug-symbol binaries. Each baseline uses one warm-up and five samples, verifies every proof, and reports medians. Setup, message/digest generation, and serialization are outside its timers; public API checks remain inside. [Exact benchmark source](source/locations/crates/flock-prover/examples/preimage_scaling.rs).

The validation/build logs record a local Rust toolchain warning: `rust-objcopy` aborted because `libLLVM.dylib` could not be loaded. On macOS, Rust invokes this utility for requested debug-info stripping and reports a started utility's unsuccessful exit as a warning; this can leave debug information unstripped. The profiling build explicitly uses `strip=none`, and accepted captures separately require symbolized workload stacks. See the [pinned Rust compiler implementation](https://github.com/rust-lang/rust/blob/88d9e12ae178fab0fb5cc050a94da85685d449ea/compiler/rustc_codegen_ssa/src/back/link.rs#L1168-L1248) and the recorded logs: [make-test.stderr](logs/make-test.stderr).

Captures sample the whole process across all threads. Proving checks warm-up and final outputs, retaining only the latest proof; verification rotates through eight prepared and validated proofs. The shared verifier pool keeps its one-worker policy. Full-ZK verification also performs outer circuit work on the calling thread and dispatches parallel Rayon work outside that pool, so its profile must retain both caller and worker stacks. Preparation, warm-up, challenger construction, proof destruction, final validation, and cleanup remain visible. The harness records phase durations and the absence of all 12 prohibited environment variables before creating pools. No temporal slice was applied.

Flamegraph width and hotspot percentages use **usable backtrace row occurrences**, matching inferno 0.12.6's xctrace collapse algorithm: one row contributes one count, irrespective of the XML `weight` column. This is sampled CPU activity across threads, not wall-clock latency, and it is not a nanosecond-weighted time sum. Scheduler frames such as `swtch_pri` and `thread_yield` in sampled Running stacks represent observed scheduling activity; their share is not blocked wall-clock time. Inclusive counts deduplicate repeated occurrences of the same symbol within each stack; inclusive symbols overlap and must not be summed. Self counts use the leaf frame and do form a partition. [Collapsed stacks and original XML](cases/) preserve the denominator evidence.

## Fresh timing and size results

Values are from the normal baseline before profiling. Full-ZK/FLOCK ratios compare paired medians. Size overhead is `(full_zk_bytes / flock_bytes - 1) × 100`.

| Hashes | FLOCK prove ms | FLOCK verify ms | FLOCK bytes | Full-ZK prove ms | Full-ZK verify ms | Full-ZK bytes | Prove ratio | Verify ratio | Size overhead |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.385 | 14.221 | 274609 | 18.901 | 12.389 | 801097 | 4.31× | 0.87× | 191.7% |
| 128 | 4.919 | 14.542 | 283537 | 18.221 | 12.228 | 800777 | 3.70× | 0.84× | 182.4% |
| 256 | 6.070 | 14.465 | 377697 | 18.868 | 12.374 | 801545 | 3.11× | 0.86× | 112.2% |
| 512 | 7.897 | 14.885 | 385081 | 22.737 | 13.196 | 811793 | 2.88× | 0.89× | 110.8% |
| 1024 | 9.184 | 16.000 | 398657 | 31.730 | 13.021 | 847521 | 3.45× | 0.81× | 112.6% |
| 2048 | 13.801 | 16.000 | 433425 | 47.878 | 14.565 | 863953 | 3.47× | 0.91× | 99.3% |
| 4096 | 22.646 | 17.716 | 451937 | 84.103 | 17.006 | 885841 | 3.71× | 0.96× | 96.0% |

Full-ZK batches of 64 and 128 pad to 256 slots. Non-ZK uses smaller circuits and ad hoc PCS schedules below the registry floor. Serialized proof sizes exclude returned witness commitments, public digests, and bundle framing. CPU profiles do not establish proof size overhead.

### Cross-session timing changes and debug-symbol comparison

Deltas below are relative to the original normal baseline before primary profiling. The final normal baseline follows the resumed episode; it does not immediately close the primary episode. These before/after values describe cross-session changes and cannot bound within-episode drift for the primary matrix. The symbol baseline belongs to the first episode.

These are five-sample medians, without confidence intervals. A large delta warrants checking load/thermal observations and repeating baselines before attributing smaller differences to code.

| Hashes | Protocol | Normal after prove / verify ms | After change prove / verify | Symbols prove / verify ms | Symbol delta prove / verify | Bytes before min–max | Bytes after min–max | Bytes symbols min–max |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | FLOCK-non-ZK-Secure | 4.473 / 14.109 | +2.0% / -0.8% | 4.427 / 14.118 | +1.0% / -0.7% | 274609–274609 | 274609–274609 | 274609–274609 |
| 64 | VEIL-FLOCK-full-ZK | 18.756 / 12.027 | -0.8% / -2.9% | 18.238 / 12.372 | -3.5% / -0.1% | 800617–802249 | 799209–802665 | 800105–802697 |
| 128 | FLOCK-non-ZK-Secure | 4.792 / 14.363 | -2.6% / -1.2% | 4.847 / 14.540 | -1.5% / -0.0% | 283537–283537 | 283537–283537 | 283537–283537 |
| 128 | VEIL-FLOCK-full-ZK | 17.815 / 12.055 | -2.2% / -1.4% | 18.811 / 12.797 | +3.2% / +4.7% | 800585–802345 | 800489–801769 | 800201–802121 |
| 256 | FLOCK-non-ZK-Secure | 6.432 / 14.438 | +6.0% / -0.2% | 6.036 / 14.470 | -0.6% / +0.0% | 377697–377697 | 377697–377697 | 377697–377697 |
| 256 | VEIL-FLOCK-full-ZK | 17.947 / 11.946 | -4.9% / -3.5% | 18.173 / 12.433 | -3.7% / +0.5% | 800521–802281 | 800873–802473 | 800777–802377 |
| 512 | FLOCK-non-ZK-Secure | 7.549 / 14.788 | -4.4% / -0.7% | 7.560 / 14.782 | -4.3% / -0.7% | 385081–385081 | 385081–385081 | 385081–385081 |
| 512 | VEIL-FLOCK-full-ZK | 21.051 / 12.788 | -7.4% / -3.1% | 22.416 / 12.847 | -1.4% / -2.6% | 810673–812913 | 811409–812561 | 810641–812913 |
| 1024 | FLOCK-non-ZK-Secure | 9.228 / 15.501 | +0.5% / -3.1% | 10.165 / 15.720 | +10.7% / -1.7% | 398657–398657 | 398657–398657 | 398657–398657 |
| 1024 | VEIL-FLOCK-full-ZK | 30.190 / 12.912 | -4.9% / -0.8% | 31.685 / 12.942 | -0.1% / -0.6% | 846273–848449 | 845089–848929 | 844929–848321 |
| 2048 | FLOCK-non-ZK-Secure | 13.545 / 15.774 | -1.9% / -1.4% | 15.190 / 16.036 | +10.1% / +0.2% | 433425–433425 | 433425–433425 | 433425–433425 |
| 2048 | VEIL-FLOCK-full-ZK | 46.190 / 13.828 | -3.5% / -5.1% | 48.559 / 14.378 | +1.4% / -1.3% | 863505–865329 | 862449–863761 | 861905–863889 |
| 4096 | FLOCK-non-ZK-Secure | 22.439 / 17.518 | -0.9% / -1.1% | 24.567 / 17.762 | +8.5% / +0.3% | 451937–451937 | 451937–451937 | 451937–451937 |
| 4096 | VEIL-FLOCK-full-ZK | 77.249 / 16.034 | -8.1% / -5.7% | 87.466 / 16.771 | +4.0% / -1.4% | 885009–887537 | 883281–886481 | 883633–886193 |

Largest absolute cross-session before/after timing change: **8.1%**. Largest absolute symbol-build delta: **10.7%**. These comparisons combine build effects and measurement variability; they do not isolate a causal debug-symbol effect. Exact data: [before](baseline-before.csv), [after](baseline-after.csv), [symbols](baseline-symbols.csv).

### Resumed-episode baseline controls

These normal-binary baselines bracket only the four resumed 4,096-hash repeats. They use the same prebuilt executable as the first episode. All seven sizes were sampled in each control run; they are additional timing observations, not replacement primary captures. Exact timing and proof-size ranges: [resume before](baseline-resume-before.csv), [final after](baseline-after.csv).

| Hashes | Protocol | Resume before prove / verify ms | Final after prove / verify ms | Resumed-interval change prove / verify |
| ---: | --- | ---: | ---: | ---: |
| 64 | FLOCK-non-ZK-Secure | 4.337 / 14.205 | 4.473 / 14.109 | +3.1% / -0.7% |
| 64 | VEIL-FLOCK-full-ZK | 18.226 / 12.036 | 18.756 / 12.027 | +2.9% / -0.1% |
| 128 | FLOCK-non-ZK-Secure | 4.786 / 14.391 | 4.792 / 14.363 | +0.1% / -0.2% |
| 128 | VEIL-FLOCK-full-ZK | 18.151 / 12.518 | 17.815 / 12.055 | -1.9% / -3.7% |
| 256 | FLOCK-non-ZK-Secure | 6.165 / 14.501 | 6.432 / 14.438 | +4.3% / -0.4% |
| 256 | VEIL-FLOCK-full-ZK | 18.870 / 12.459 | 17.947 / 11.946 | -4.9% / -4.1% |
| 512 | FLOCK-non-ZK-Secure | 7.747 / 14.790 | 7.549 / 14.788 | -2.6% / -0.0% |
| 512 | VEIL-FLOCK-full-ZK | 22.139 / 13.609 | 21.051 / 12.788 | -4.9% / -6.0% |
| 1024 | FLOCK-non-ZK-Secure | 9.890 / 15.661 | 9.228 / 15.501 | -6.7% / -1.0% |
| 1024 | VEIL-FLOCK-full-ZK | 29.976 / 12.723 | 30.190 / 12.912 | +0.7% / +1.5% |
| 2048 | FLOCK-non-ZK-Secure | 13.780 / 15.849 | 13.545 / 15.774 | -1.7% / -0.5% |
| 2048 | VEIL-FLOCK-full-ZK | 48.421 / 14.386 | 46.190 / 13.828 | -4.6% / -3.9% |
| 4096 | FLOCK-non-ZK-Secure | 21.429 / 17.716 | 22.439 / 17.518 | +4.7% / -1.1% |
| 4096 | VEIL-FLOCK-full-ZK | 76.066 / 16.132 | 77.249 / 16.034 | +1.6% / -0.6% |

Largest absolute timing change across the resumed interval: **6.7%**. Largest absolute change from the original-before baseline to the resume-before baseline: **9.6%**. The latter is a cross-session comparison. These controls cannot recover the missing immediate closing baseline for the first episode.

### Scaling observations

- FLOCK-non-ZK-Secure: a 64× increase in hashes changes prove latency by 5.16×, verify latency by 1.25×, and median proof bytes by 1.65× in the before baseline.
- VEIL-FLOCK-full-ZK: a 64× increase in hashes changes prove latency by 4.45×, verify latency by 1.37×, and median proof bytes by 1.11× in the before baseline.

## Flamegraph matrix

Open an SVG to use its search and zoom controls.

| Hashes | FLOCK prove | FLOCK verify | Full-ZK prove | Full-ZK verify |
| ---: | --- | --- | --- | --- |
| 64 | [SVG](svg/flock-prove-0064.svg) | [SVG](svg/flock-verify-0064.svg) | [SVG](svg/full-zk-prove-0064.svg) | [SVG](svg/full-zk-verify-0064.svg) |
| 128 | [SVG](svg/flock-prove-0128.svg) | [SVG](svg/flock-verify-0128.svg) | [SVG](svg/full-zk-prove-0128.svg) | [SVG](svg/full-zk-verify-0128.svg) |
| 256 | [SVG](svg/flock-prove-0256.svg) | [SVG](svg/flock-verify-0256.svg) | [SVG](svg/full-zk-prove-0256.svg) | [SVG](svg/full-zk-verify-0256.svg) |
| 512 | [SVG](svg/flock-prove-0512.svg) | [SVG](svg/flock-verify-0512.svg) | [SVG](svg/full-zk-prove-0512.svg) | [SVG](svg/full-zk-verify-0512.svg) |
| 1024 | [SVG](svg/flock-prove-1024.svg) | [SVG](svg/flock-verify-1024.svg) | [SVG](svg/full-zk-prove-1024.svg) | [SVG](svg/full-zk-verify-1024.svg) |
| 2048 | [SVG](svg/flock-prove-2048.svg) | [SVG](svg/flock-verify-2048.svg) | [SVG](svg/full-zk-prove-2048.svg) | [SVG](svg/full-zk-verify-2048.svg) |
| 4096 | [SVG](svg/flock-prove-4096.svg) | [SVG](svg/flock-verify-4096.svg) | [SVG](svg/full-zk-prove-4096.svg) | [SVG](svg/full-zk-verify-4096.svg) |

Representative small and large proving cases:

![FLOCK prove, 64 hashes](svg/flock-prove-0064.svg)

![FLOCK prove, 4096 hashes](svg/flock-prove-4096.svg)

![Full-ZK prove, 64 hashes](svg/full-zk-prove-0064.svg)

![Full-ZK prove, 4096 hashes](svg/full-zk-prove-4096.svg)

## Capture quality and phase durations

Loop call rates are profiled throughput and must not replace the unprofiled baseline timings. Phase durations are wall-clock observations; they do not measure phase CPU shares. Missing/unknown/truncated counts refer to XML rows or recognized frame markers, as labeled. Zero marked truncation does not establish complete stacks.

| Case | Usable / all XML rows | Loop seconds / calls | Preparation / validation / cleanup seconds | Rows with unknown frame / unknown leaf | Marked truncated rows | Global / verifier workers |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| [flock-prove-0064](cases/flock-prove-0064/primary-001/attempt.json) | 151546 / 151553 | 30.000 / 6153 | 0.691 / 0.015 / 0.005 | 1656 / 0 | 0 | 8 / 1 |
| [flock-prove-0128](cases/flock-prove-0128/primary-001/attempt.json) | 140941 / 140953 | 30.005 / 5080 | 0.710 / 0.015 / 0.073 | 2652 / 0 | 0 | 8 / 1 |
| [flock-prove-0256](cases/flock-prove-0256/primary-001/attempt.json) | 137857 / 137865 | 30.002 / 4118 | 0.728 / 0.017 / 0.081 | 4518 / 0 | 0 | 8 / 1 |
| [flock-prove-0512](cases/flock-prove-0512/primary-001/attempt.json) | 128444 / 128456 | 30.002 / 3052 | 0.689 / 0.015 / 0.098 | 6576 / 0 | 0 | 8 / 1 |
| [flock-prove-1024](cases/flock-prove-1024/primary-001/attempt.json) | 159631 / 159640 | 30.001 / 3092 | 0.657 / 0.016 / 0.005 | 12081 / 0 | 0 | 8 / 1 |
| [flock-prove-2048](cases/flock-prove-2048/primary-001/attempt.json) | 158979 / 158985 | 30.007 / 2033 | 0.660 / 0.016 / 0.004 | 15584 / 1 | 0 | 8 / 1 |
| [flock-prove-4096](cases/flock-prove-4096/primary-001/attempt.json) | 160071 / 160081 | 30.001 / 1250 | 0.674 / 0.025 / 0.006 | 19315 / 1 | 0 | 8 / 1 |
| [flock-verify-0064](cases/flock-verify-0064/primary-001/attempt.json) | 30678 / 30688 | 30.002 / 2066 | 0.853 / 0.014 / 0.020 | 447 / 0 | 0 | 8 / 1 |
| [flock-verify-0128](cases/flock-verify-0128/primary-001/attempt.json) | 30747 / 30757 | 30.010 / 2028 | 0.834 / 0.014 / 0.019 | 671 / 0 | 0 | 8 / 1 |
| [flock-verify-0256](cases/flock-verify-0256/primary-001/attempt.json) | 30867 / 30877 | 30.001 / 1996 | 1.003 / 0.015 / 0.055 | 455 / 1 | 0 | 8 / 1 |
| [flock-verify-0512](cases/flock-verify-0512/primary-001/attempt.json) | 30886 / 30896 | 30.007 / 1958 | 0.885 / 0.015 / 0.004 | 563 / 0 | 0 | 8 / 1 |
| [flock-verify-1024](cases/flock-verify-1024/primary-001/attempt.json) | 31201 / 31208 | 30.005 / 1910 | 0.834 / 0.016 / 0.004 | 730 / 0 | 0 | 8 / 1 |
| [flock-verify-2048](cases/flock-verify-2048/primary-001/attempt.json) | 31346 / 31354 | 30.009 / 1867 | 0.903 / 0.016 / 0.004 | 493 / 0 | 0 | 8 / 1 |
| [flock-verify-4096](cases/flock-verify-4096/primary-001/attempt.json) | 31824 / 31833 | 30.016 / 1702 | 0.977 / 0.018 / 0.004 | 618 / 1 | 0 | 8 / 1 |
| [full-zk-prove-0064](cases/full-zk-prove-0064/primary-001/attempt.json) | 105131 / 105143 | 30.007 / 1475 | 0.710 / 0.014 / 0.056 | 4083 / 1 | 0 | 8 / 1 |
| [full-zk-prove-0128](cases/full-zk-prove-0128/primary-001/attempt.json) | 107648 / 107658 | 30.013 / 1516 | 0.708 / 0.015 / 0.018 | 4037 / 1 | 0 | 8 / 1 |
| [full-zk-prove-0256](cases/full-zk-prove-0256/primary-001/attempt.json) | 98693 / 98704 | 30.014 / 1333 | 0.757 / 0.015 / 0.091 | 3649 / 1 | 0 | 8 / 1 |
| [full-zk-prove-0512](cases/full-zk-prove-0512/primary-001/attempt.json) | 104195 / 104202 | 30.024 / 1139 | 0.730 / 0.021 / 0.004 | 5361 / 1 | 0 | 8 / 1 |
| [full-zk-prove-1024](cases/full-zk-prove-1024/primary-001/attempt.json) | 108792 / 108799 | 30.024 / 951 | 0.676 / 0.013 / 0.003 | 8623 / 0 | 0 | 8 / 1 |
| [full-zk-prove-2048](cases/full-zk-prove-2048/primary-001/attempt.json) | 108604 / 108611 | 30.025 / 631 | 0.705 / 0.014 / 0.004 | 10796 / 0 | 0 | 8 / 1 |
| [full-zk-prove-4096](cases/full-zk-prove-4096/primary-001/attempt.json) | 108516 / 108526 | 30.050 / 386 | 0.742 / 0.016 / 0.005 | 13059 / 1 | 0 | 8 / 1 |
| [full-zk-verify-0064](cases/full-zk-verify-0064/primary-001/attempt.json) | 87649 / 87658 | 30.006 / 2159 | 0.998 / 0.013 / 0.079 | 501 / 1 | 0 | 8 / 1 |
| [full-zk-verify-0128](cases/full-zk-verify-0128/primary-001/attempt.json) | 86718 / 86728 | 30.014 / 2137 | 0.940 / 0.014 / 0.094 | 442 / 1 | 0 | 8 / 1 |
| [full-zk-verify-0256](cases/full-zk-verify-0256/primary-001/attempt.json) | 84415 / 84425 | 30.005 / 2052 | 0.963 / 0.013 / 0.056 | 440 / 0 | 0 | 8 / 1 |
| [full-zk-verify-0512](cases/full-zk-verify-0512/primary-001/attempt.json) | 89222 / 89228 | 30.002 / 2261 | 0.927 / 0.012 / 0.004 | 648 / 0 | 0 | 8 / 1 |
| [full-zk-verify-1024](cases/full-zk-verify-1024/primary-001/attempt.json) | 89174 / 89180 | 30.014 / 2244 | 0.991 / 0.014 / 0.003 | 599 / 1 | 0 | 8 / 1 |
| [full-zk-verify-2048](cases/full-zk-verify-2048/primary-001/attempt.json) | 85690 / 85697 | 30.005 / 2097 | 1.124 / 0.015 / 0.003 | 640 / 0 | 0 | 8 / 1 |
| [full-zk-verify-4096](cases/full-zk-verify-4096/primary-001/attempt.json) | 80814 / 80822 | 30.010 / 1861 | 1.405 / 0.017 / 0.003 | 850 / 0 | 0 | 8 / 1 |

## Hotspots

Each case lists its top five inclusive and top five self symbols. Full counts and explicit denominators are in [hotspots.csv](hotspots.csv). Source links are **symbol-name lookups** in copied frozen modules; they are not address-derived line attribution. A module link at line 1 means no function declaration was resolved. External-library symbols remain labeled without a repository source link. Self categories use a single leaf-symbol rule and form disjoint buckets, but inlining and missing symbols can shift attribution. Category names are clues for investigation, not exact API phase boundaries.

### flock-prove-0064

[SVG](svg/flock-prove-0064.svg) · [attempt evidence](cases/flock-prove-0064/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 141897 | 93.63% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 141897 | 93.63% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 141897 | 93.63% | external or unresolved |
| inclusive | `_pthread_start` | 141897 | 93.63% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 141897 | 93.63% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 74881 | 49.41% | external or unresolved |
| self | `swtch_pri` | 32265 | 21.29% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 6242 | 4.12% | external or unresolved |
| self | `__psynch_cvwait` | 2971 | 1.96% | external or unresolved |
| self | `_platform_memmove` | 2532 | 1.67% | external or unresolved |

Self categories: sumchecks and constraint checks 51.01%; scheduling and synchronization 27.83%; other or unresolved 11.23%; field arithmetic and transforms 4.75%; allocation and copying 3.24%; PCS and Merkle work 1.01%; transcript, hashing, and randomness 0.92%.

### flock-prove-0128

[SVG](svg/flock-prove-0128.svg) · [attempt evidence](cases/flock-prove-0128/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 131801 | 93.52% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 131801 | 93.52% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 131801 | 93.52% | external or unresolved |
| inclusive | `_pthread_start` | 131801 | 93.52% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 131801 | 93.52% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 62986 | 44.69% | external or unresolved |
| self | `swtch_pri` | 33879 | 24.04% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 5215 | 3.70% | external or unresolved |
| self | `__psynch_cvwait` | 2536 | 1.80% | external or unresolved |
| self | `_platform_memmove` | 2270 | 1.61% | external or unresolved |

Self categories: sumchecks and constraint checks 47.03%; scheduling and synchronization 30.18%; other or unresolved 11.39%; field arithmetic and transforms 5.93%; allocation and copying 3.07%; transcript, hashing, and randomness 1.26%; PCS and Merkle work 1.15%.

### flock-prove-0256

[SVG](svg/flock-prove-0256.svg) · [attempt evidence](cases/flock-prove-0256/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 127483 | 92.47% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 127483 | 92.47% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 127483 | 92.47% | external or unresolved |
| inclusive | `_pthread_start` | 127483 | 92.47% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 127483 | 92.47% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 51020 | 37.01% | external or unresolved |
| self | `swtch_pri` | 35239 | 25.56% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4118 | 2.99% | external or unresolved |
| self | `__psynch_cvwait` | 2710 | 1.97% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 2349 | 1.70% | external or unresolved |

Self categories: sumchecks and constraint checks 40.83%; scheduling and synchronization 31.94%; other or unresolved 12.86%; field arithmetic and transforms 7.68%; allocation and copying 3.04%; transcript, hashing, and randomness 2.00%; PCS and Merkle work 1.65%.

### flock-prove-0512

[SVG](svg/flock-prove-0512.svg) · [attempt evidence](cases/flock-prove-0512/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 117802 | 91.71% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 117802 | 91.71% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 117802 | 91.71% | external or unresolved |
| inclusive | `_pthread_start` | 117802 | 91.71% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 117802 | 91.71% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 38617 | 30.07% | external or unresolved |
| self | `swtch_pri` | 32365 | 25.20% | external or unresolved |
| self | `flock_core::field::f128_slice::aarch64::fold_pairs` | 3121 | 2.43% | [crates/flock-core/src/field/f128_slice/aarch64.rs:8](source/locations/crates/flock-core/src/field/f128_slice/aarch64.rs#L8) |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 3067 | 2.39% | external or unresolved |
| self | `<flock_core::ntt::additive_ntt_f128::AdditiveNttF128>::forward_transform_interleaved_scalar_from_layer` | 2599 | 2.02% | external or unresolved |

Self categories: sumchecks and constraint checks 35.65%; scheduling and synchronization 31.25%; other or unresolved 14.28%; field arithmetic and transforms 10.74%; transcript, hashing, and randomness 3.10%; allocation and copying 2.79%; PCS and Merkle work 2.20%.

### flock-prove-1024

[SVG](svg/flock-prove-1024.svg) · [attempt evidence](cases/flock-prove-1024/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 150638 | 94.37% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 150638 | 94.37% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 150638 | 94.37% | external or unresolved |
| inclusive | `_pthread_start` | 150638 | 94.37% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 150638 | 94.37% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 36928 | 23.13% | external or unresolved |
| self | `swtch_pri` | 29110 | 18.24% | external or unresolved |
| self | `flock_core::field::f128_slice::aarch64::fold_pairs` | 5786 | 3.62% | [crates/flock-core/src/field/f128_slice/aarch64.rs:8](source/locations/crates/flock-core/src/field/f128_slice/aarch64.rs#L8) |
| self | `flock_core::zerocheck::univariate_skip_optimized::kernels::aarch64::accumulate_convert_with_s_hat_v` | 4793 | 3.00% | [crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs:51](source/locations/crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs#L51) |
| self | `core::ptr::read::<core::ptr::Packed<core::core_arch::arm_shared::neon::uint8x16_t>>` | 4541 | 2.84% | external or unresolved |

Self categories: sumchecks and constraint checks 31.67%; scheduling and synchronization 24.43%; other or unresolved 18.43%; field arithmetic and transforms 15.57%; transcript, hashing, and randomness 4.09%; PCS and Merkle work 3.08%; allocation and copying 2.73%.

### flock-prove-2048

[SVG](svg/flock-prove-2048.svg) · [attempt evidence](cases/flock-prove-2048/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 150190 | 94.47% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 150190 | 94.47% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 150190 | 94.47% | external or unresolved |
| inclusive | `_pthread_start` | 150190 | 94.47% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 150190 | 94.47% | external or unresolved |
| self | `swtch_pri` | 26330 | 16.56% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 24428 | 15.37% | external or unresolved |
| self | `flock_core::field::f128_slice::aarch64::fold_pairs` | 8291 | 5.22% | [crates/flock-core/src/field/f128_slice/aarch64.rs:8](source/locations/crates/flock-core/src/field/f128_slice/aarch64.rs#L8) |
| self | `flock_core::zerocheck::univariate_skip_optimized::kernels::aarch64::accumulate_convert_with_s_hat_v` | 6356 | 4.00% | [crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs:51](source/locations/crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs#L51) |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 5800 | 3.65% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |

Self categories: sumchecks and constraint checks 25.82%; scheduling and synchronization 22.19%; other or unresolved 21.04%; field arithmetic and transforms 20.74%; transcript, hashing, and randomness 5.26%; allocation and copying 2.89%; PCS and Merkle work 2.05%.

### flock-prove-4096

[SVG](svg/flock-prove-4096.svg) · [attempt evidence](cases/flock-prove-4096/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `thread_start` | 152314 | 95.15% | external or unresolved |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 152313 | 95.15% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 152313 | 95.15% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 152313 | 95.15% | external or unresolved |
| inclusive | `_pthread_start` | 152313 | 95.15% | external or unresolved |
| self | `swtch_pri` | 20736 | 12.95% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 15232 | 9.52% | external or unresolved |
| self | `flock_core::field::f128_slice::aarch64::fold_pairs` | 10032 | 6.27% | [crates/flock-core/src/field/f128_slice/aarch64.rs:8](source/locations/crates/flock-core/src/field/f128_slice/aarch64.rs#L8) |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 8133 | 5.08% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| self | `flock_core::zerocheck::univariate_skip_optimized::kernels::aarch64::accumulate_convert_with_s_hat_v` | 7754 | 4.84% | [crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs:51](source/locations/crates/flock-core/src/zerocheck/univariate_skip_optimized/kernels/aarch64.rs#L51) |

Self categories: field arithmetic and transforms 25.37%; other or unresolved 23.17%; sumchecks and constraint checks 22.36%; scheduling and synchronization 17.29%; transcript, hashing, and randomness 6.61%; allocation and copying 2.83%; PCS and Merkle work 2.36%.

### flock-verify-0064

[SVG](svg/flock-verify-0064.svg) · [attempt evidence](cases/flock-verify-0064/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 29813 | 97.18% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 29813 | 97.18% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 29813 | 97.18% | external or unresolved |
| inclusive | `_pthread_start` | 29813 | 97.18% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 29813 | 97.18% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 23283 | 75.89% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 2066 | 6.73% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 938 | 3.06% | external or unresolved |
| self | `flock_core::pcs::tensor_algebra::square_transpose::{closure#0}` | 354 | 1.15% | [crates/flock-core/src/pcs/tensor_algebra.rs:122](source/locations/crates/flock-core/src/pcs/tensor_algebra.rs#L122) |
| self | `<alloc::vec::Vec<u32>>::as_slice` | 310 | 1.01% | external or unresolved |

Self categories: sumchecks and constraint checks 76.28%; other or unresolved 12.89%; field arithmetic and transforms 4.14%; allocation and copying 2.24%; PCS and Merkle work 2.10%; transcript, hashing, and randomness 1.59%; scheduling and synchronization 0.77%.

### flock-verify-0128

[SVG](svg/flock-verify-0128.svg) · [attempt evidence](cases/flock-verify-0128/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 29818 | 96.98% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 29818 | 96.98% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 29818 | 96.98% | external or unresolved |
| inclusive | `_pthread_start` | 29818 | 96.98% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 29818 | 96.98% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 22767 | 74.05% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 2023 | 6.58% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1097 | 3.57% | external or unresolved |
| self | `flock_core::pcs::tensor_algebra::square_transpose::{closure#0}` | 535 | 1.74% | [crates/flock-core/src/pcs/tensor_algebra.rs:122](source/locations/crates/flock-core/src/pcs/tensor_algebra.rs#L122) |
| self | `<alloc::vec::Vec<u32>>::as_slice` | 311 | 1.01% | external or unresolved |

Self categories: sumchecks and constraint checks 74.44%; other or unresolved 13.37%; field arithmetic and transforms 4.91%; PCS and Merkle work 2.84%; allocation and copying 2.24%; transcript, hashing, and randomness 1.50%; scheduling and synchronization 0.70%.

### flock-verify-0256

[SVG](svg/flock-verify-0256.svg) · [attempt evidence](cases/flock-verify-0256/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `thread_start` | 29575 | 95.81% | external or unresolved |
| inclusive | `_pthread_start` | 29574 | 95.81% | external or unresolved |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 29573 | 95.81% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 29573 | 95.81% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 29573 | 95.81% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 22855 | 74.04% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 1985 | 6.43% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 891 | 2.89% | external or unresolved |
| self | `<alloc::vec::Vec<u32>>::as_slice` | 341 | 1.10% | external or unresolved |
| self | `flock_core::pcs::tensor_algebra::square_transpose::{closure#0}` | 334 | 1.08% | [crates/flock-core/src/pcs/tensor_algebra.rs:122](source/locations/crates/flock-core/src/pcs/tensor_algebra.rs#L122) |

Self categories: sumchecks and constraint checks 74.49%; other or unresolved 13.68%; field arithmetic and transforms 4.02%; allocation and copying 2.81%; PCS and Merkle work 2.13%; transcript, hashing, and randomness 2.04%; scheduling and synchronization 0.82%.

### flock-verify-0512

[SVG](svg/flock-verify-0512.svg) · [attempt evidence](cases/flock-verify-0512/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 29287 | 94.82% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 29287 | 94.82% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 29287 | 94.82% | external or unresolved |
| inclusive | `_pthread_start` | 29287 | 94.82% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 29287 | 94.82% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 22364 | 72.41% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 1936 | 6.27% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1062 | 3.44% | external or unresolved |
| self | `flock_core::pcs::tensor_algebra::square_transpose::{closure#0}` | 424 | 1.37% | [crates/flock-core/src/pcs/tensor_algebra.rs:122](source/locations/crates/flock-core/src/pcs/tensor_algebra.rs#L122) |
| self | `<alloc::vec::Vec<u32>>::as_slice` | 295 | 0.96% | external or unresolved |

Self categories: sumchecks and constraint checks 72.93%; other or unresolved 14.47%; field arithmetic and transforms 4.64%; allocation and copying 2.76%; PCS and Merkle work 2.48%; transcript, hashing, and randomness 2.04%; scheduling and synchronization 0.68%.

### flock-verify-1024

[SVG](svg/flock-verify-1024.svg) · [attempt evidence](cases/flock-verify-1024/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `thread_start` | 28994 | 92.93% | external or unresolved |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 28993 | 92.92% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 28993 | 92.92% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 28993 | 92.92% | external or unresolved |
| inclusive | `_pthread_start` | 28993 | 92.92% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 21506 | 68.93% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 1795 | 5.75% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1371 | 4.39% | external or unresolved |
| self | `flock_core::pcs::tensor_algebra::square_transpose::{closure#0}` | 532 | 1.71% | [crates/flock-core/src/pcs/tensor_algebra.rs:122](source/locations/crates/flock-core/src/pcs/tensor_algebra.rs#L122) |
| self | `flock_prover::digest_bind::fold_region` | 494 | 1.58% | [crates/flock-prover/src/digest_bind.rs:233](source/locations/crates/flock-prover/src/digest_bind.rs#L233) |

Self categories: sumchecks and constraint checks 69.42%; other or unresolved 15.86%; field arithmetic and transforms 5.75%; allocation and copying 2.93%; PCS and Merkle work 2.84%; transcript, hashing, and randomness 2.49%; scheduling and synchronization 0.72%.

### flock-verify-2048

[SVG](svg/flock-verify-2048.svg) · [attempt evidence](cases/flock-verify-2048/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 27729 | 88.46% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 27729 | 88.46% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 27729 | 88.46% | external or unresolved |
| inclusive | `_pthread_start` | 27729 | 88.46% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 27729 | 88.46% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 21019 | 67.05% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 1769 | 5.64% | external or unresolved |
| self | `flock_prover::digest_bind::fold_region` | 970 | 3.09% | [crates/flock-prover/src/digest_bind.rs:233](source/locations/crates/flock-prover/src/digest_bind.rs#L233) |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 873 | 2.79% | external or unresolved |
| self | `<flock_prover::digest_bind::DigestStatement>::public_digest::{closure#0}` | 593 | 1.89% | external or unresolved |

Self categories: sumchecks and constraint checks 67.61%; other or unresolved 18.27%; field arithmetic and transforms 4.26%; allocation and copying 3.60%; transcript, hashing, and randomness 3.40%; PCS and Merkle work 2.09%; scheduling and synchronization 0.78%.

### flock-verify-4096

[SVG](svg/flock-verify-4096.svg) · [attempt evidence](cases/flock-verify-4096/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 26061 | 81.89% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 26061 | 81.89% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 26061 | 81.89% | external or unresolved |
| inclusive | `_pthread_start` | 26061 | 81.89% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 26061 | 81.89% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 19046 | 59.85% | external or unresolved |
| self | `flock_prover::digest_bind::fold_region` | 1685 | 5.29% | [crates/flock-prover/src/digest_bind.rs:233](source/locations/crates/flock-prover/src/digest_bind.rs#L233) |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 1664 | 5.23% | external or unresolved |
| self | `<flock_prover::digest_bind::DigestStatement>::public_digest::{closure#0}` | 1107 | 3.48% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 950 | 2.99% | external or unresolved |

Self categories: sumchecks and constraint checks 60.61%; other or unresolved 22.93%; field arithmetic and transforms 4.84%; allocation and copying 4.47%; transcript, hashing, and randomness 4.12%; PCS and Merkle work 2.26%; scheduling and synchronization 0.77%.

### full-zk-prove-0064

[SVG](svg/full-zk-prove-0064.svg) · [attempt evidence](cases/full-zk-prove-0064/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 90310 | 85.90% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 90310 | 85.90% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 90310 | 85.90% | external or unresolved |
| inclusive | `_pthread_start` | 90310 | 85.90% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 90310 | 85.90% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 36404 | 34.63% | external or unresolved |
| self | `swtch_pri` | 19311 | 18.37% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 2953 | 2.81% | external or unresolved |
| self | `_platform_memmove` | 2849 | 2.71% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 2093 | 1.99% | external or unresolved |

Self categories: sumchecks and constraint checks 36.51%; scheduling and synchronization 23.70%; other or unresolved 16.20%; field arithmetic and transforms 10.81%; allocation and copying 6.68%; transcript, hashing, and randomness 4.18%; PCS and Merkle work 1.90%; VEIL protocol work 0.02%.

### full-zk-prove-0128

[SVG](svg/full-zk-prove-0128.svg) · [attempt evidence](cases/full-zk-prove-0128/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 92415 | 85.85% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 92415 | 85.85% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 92415 | 85.85% | external or unresolved |
| inclusive | `_pthread_start` | 92415 | 85.85% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 92415 | 85.85% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 37586 | 34.92% | external or unresolved |
| self | `swtch_pri` | 20235 | 18.80% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 2954 | 2.74% | external or unresolved |
| self | `_platform_memmove` | 2808 | 2.61% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 2142 | 1.99% | external or unresolved |

Self categories: sumchecks and constraint checks 36.85%; scheduling and synchronization 23.95%; other or unresolved 16.03%; field arithmetic and transforms 10.66%; allocation and copying 6.55%; transcript, hashing, and randomness 4.14%; PCS and Merkle work 1.79%; VEIL protocol work 0.02%.

### full-zk-prove-0256

[SVG](svg/full-zk-prove-0256.svg) · [attempt evidence](cases/full-zk-prove-0256/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 84783 | 85.91% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 84783 | 85.91% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 84783 | 85.91% | external or unresolved |
| inclusive | `_pthread_start` | 84783 | 85.91% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 84783 | 85.91% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 33355 | 33.80% | external or unresolved |
| self | `swtch_pri` | 20787 | 21.06% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 2655 | 2.69% | external or unresolved |
| self | `_platform_memmove` | 2604 | 2.64% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1997 | 2.02% | external or unresolved |

Self categories: sumchecks and constraint checks 35.54%; scheduling and synchronization 26.29%; other or unresolved 15.42%; field arithmetic and transforms 10.43%; allocation and copying 6.52%; transcript, hashing, and randomness 4.04%; PCS and Merkle work 1.72%; VEIL protocol work 0.03%.

### full-zk-prove-0512

[SVG](svg/full-zk-prove-0512.svg) · [attempt evidence](cases/full-zk-prove-0512/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 89564 | 85.96% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 89564 | 85.96% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 89564 | 85.96% | external or unresolved |
| inclusive | `_pthread_start` | 89564 | 85.96% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 89564 | 85.96% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 28823 | 27.66% | external or unresolved |
| self | `swtch_pri` | 19668 | 18.88% | external or unresolved |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 3089 | 2.96% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 3010 | 2.89% | external or unresolved |
| self | `_platform_memmove` | 2717 | 2.61% | external or unresolved |

Self categories: sumchecks and constraint checks 30.39%; scheduling and synchronization 24.33%; other or unresolved 17.80%; field arithmetic and transforms 13.82%; allocation and copying 5.85%; transcript, hashing, and randomness 5.31%; PCS and Merkle work 2.49%; VEIL protocol work 0.01%.

### full-zk-prove-1024

[SVG](svg/full-zk-prove-1024.svg) · [attempt evidence](cases/full-zk-prove-1024/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `_pthread_start` | 92441 | 84.97% | external or unresolved |
| inclusive | `thread_start` | 92441 | 84.97% | external or unresolved |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 92440 | 84.97% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 92440 | 84.97% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 92440 | 84.97% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 22754 | 20.92% | external or unresolved |
| self | `swtch_pri` | 13632 | 12.53% | external or unresolved |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 5478 | 5.04% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 3839 | 3.53% | external or unresolved |
| self | `_platform_memmove` | 3711 | 3.41% | external or unresolved |

Self categories: sumchecks and constraint checks 24.71%; other or unresolved 22.35%; field arithmetic and transforms 18.93%; scheduling and synchronization 17.51%; transcript, hashing, and randomness 7.70%; allocation and copying 6.34%; PCS and Merkle work 2.44%; VEIL protocol work 0.01%.

### full-zk-prove-2048

[SVG](svg/full-zk-prove-2048.svg) · [attempt evidence](cases/full-zk-prove-2048/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 91759 | 84.49% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 91759 | 84.49% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 91759 | 84.49% | external or unresolved |
| inclusive | `_pthread_start` | 91759 | 84.49% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 91759 | 84.49% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 15238 | 14.03% | external or unresolved |
| self | `swtch_pri` | 10963 | 10.09% | external or unresolved |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 7265 | 6.69% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 4855 | 4.47% | external or unresolved |
| self | `core::intrinsics::rotate_right::<u32>` | 4675 | 4.30% | external or unresolved |

Self categories: other or unresolved 25.70%; field arithmetic and transforms 22.76%; sumchecks and constraint checks 18.82%; scheduling and synchronization 14.57%; transcript, hashing, and randomness 9.42%; allocation and copying 5.84%; PCS and Merkle work 2.88%; VEIL protocol work 0.00%.

### full-zk-prove-4096

[SVG](svg/full-zk-prove-4096.svg) · [attempt evidence](cases/full-zk-prove-4096/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 91057 | 83.91% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 91057 | 83.91% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 91057 | 83.91% | external or unresolved |
| inclusive | `_pthread_start` | 91057 | 83.91% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 91057 | 83.91% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 9198 | 8.48% | external or unresolved |
| self | `flock_core::ntt::additive_ntt_f128::kernels::portable::butterfly_row_pair` | 8750 | 8.06% | [crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs:4](source/locations/crates/flock-core/src/ntt/additive_ntt_f128/kernels/portable.rs#L4) |
| self | `swtch_pri` | 7247 | 6.68% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 6237 | 5.75% | external or unresolved |
| self | `core::intrinsics::rotate_right::<u32>` | 5550 | 5.11% | external or unresolved |

Self categories: field arithmetic and transforms 28.36%; other or unresolved 27.35%; sumchecks and constraint checks 14.34%; transcript, hashing, and randomness 11.25%; scheduling and synchronization 9.62%; allocation and copying 5.64%; PCS and Merkle work 3.44%; VEIL protocol work 0.00%.

### full-zk-verify-0064

[SVG](svg/full-zk-verify-0064.svg) · [attempt evidence](cases/full-zk-verify-0064/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 71109 | 81.13% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 71109 | 81.13% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 71109 | 81.13% | external or unresolved |
| inclusive | `_pthread_start` | 71109 | 81.13% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 71109 | 81.13% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 54330 | 61.99% | external or unresolved |
| self | `swtch_pri` | 4975 | 5.68% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4361 | 4.98% | external or unresolved |
| self | `_platform_memmove` | 2501 | 2.85% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1907 | 2.18% | external or unresolved |

Self categories: sumchecks and constraint checks 62.22%; other or unresolved 12.23%; allocation and copying 8.44%; field arithmetic and transforms 7.66%; scheduling and synchronization 7.29%; transcript, hashing, and randomness 1.31%; PCS and Merkle work 0.82%; VEIL protocol work 0.03%.

### full-zk-verify-0128

[SVG](svg/full-zk-verify-0128.svg) · [attempt evidence](cases/full-zk-verify-0128/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `thread_start` | 70527 | 81.33% | external or unresolved |
| inclusive | `_pthread_start` | 70526 | 81.33% | external or unresolved |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 70525 | 81.33% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 70525 | 81.33% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 70525 | 81.33% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 54048 | 62.33% | external or unresolved |
| self | `swtch_pri` | 4769 | 5.50% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4312 | 4.97% | external or unresolved |
| self | `_platform_memmove` | 2487 | 2.87% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1851 | 2.13% | external or unresolved |

Self categories: sumchecks and constraint checks 62.53%; other or unresolved 12.00%; allocation and copying 8.66%; field arithmetic and transforms 7.43%; scheduling and synchronization 7.23%; transcript, hashing, and randomness 1.32%; PCS and Merkle work 0.78%; VEIL protocol work 0.04%.

### full-zk-verify-0256

[SVG](svg/full-zk-verify-0256.svg) · [attempt evidence](cases/full-zk-verify-0256/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 68999 | 81.74% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 68999 | 81.74% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 68999 | 81.74% | external or unresolved |
| inclusive | `_pthread_start` | 68999 | 81.74% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 68999 | 81.74% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 52118 | 61.74% | external or unresolved |
| self | `swtch_pri` | 5434 | 6.44% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4127 | 4.89% | external or unresolved |
| self | `_platform_memmove` | 2269 | 2.69% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1900 | 2.25% | external or unresolved |

Self categories: sumchecks and constraint checks 61.96%; other or unresolved 11.96%; allocation and copying 8.31%; scheduling and synchronization 8.26%; field arithmetic and transforms 7.38%; transcript, hashing, and randomness 1.30%; PCS and Merkle work 0.79%; VEIL protocol work 0.04%.

### full-zk-verify-0512

[SVG](svg/full-zk-verify-0512.svg) · [attempt evidence](cases/full-zk-verify-0512/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 71956 | 80.65% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 71956 | 80.65% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 71956 | 80.65% | external or unresolved |
| inclusive | `_pthread_start` | 71956 | 80.65% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 71956 | 80.65% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 54890 | 61.52% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4673 | 5.24% | external or unresolved |
| self | `swtch_pri` | 3718 | 4.17% | external or unresolved |
| self | `_platform_memmove` | 2609 | 2.92% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 2416 | 2.71% | external or unresolved |

Self categories: sumchecks and constraint checks 61.73%; other or unresolved 13.22%; allocation and copying 8.55%; field arithmetic and transforms 8.08%; scheduling and synchronization 5.88%; transcript, hashing, and randomness 1.52%; PCS and Merkle work 0.99%; VEIL protocol work 0.04%.

### full-zk-verify-1024

[SVG](svg/full-zk-verify-1024.svg) · [attempt evidence](cases/full-zk-verify-1024/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 70804 | 79.40% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 70804 | 79.40% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 70804 | 79.40% | external or unresolved |
| inclusive | `_pthread_start` | 70804 | 79.40% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 70804 | 79.40% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 54323 | 60.92% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4554 | 5.11% | external or unresolved |
| self | `swtch_pri` | 3854 | 4.32% | external or unresolved |
| self | `_platform_memmove` | 2797 | 3.14% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1857 | 2.08% | external or unresolved |

Self categories: sumchecks and constraint checks 61.12%; other or unresolved 13.32%; allocation and copying 9.19%; field arithmetic and transforms 7.67%; scheduling and synchronization 6.00%; transcript, hashing, and randomness 1.71%; PCS and Merkle work 0.95%; VEIL protocol work 0.03%.

### full-zk-verify-2048

[SVG](svg/full-zk-verify-2048.svg) · [attempt evidence](cases/full-zk-verify-2048/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 66746 | 77.89% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 66746 | 77.89% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 66746 | 77.89% | external or unresolved |
| inclusive | `_pthread_start` | 66746 | 77.89% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 66746 | 77.89% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 50439 | 58.86% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 4267 | 4.98% | external or unresolved |
| self | `swtch_pri` | 3601 | 4.20% | external or unresolved |
| self | `_platform_memmove` | 2717 | 3.17% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 1951 | 2.28% | external or unresolved |

Self categories: sumchecks and constraint checks 59.14%; other or unresolved 14.85%; allocation and copying 9.09%; field arithmetic and transforms 7.99%; scheduling and synchronization 5.92%; transcript, hashing, and randomness 2.01%; PCS and Merkle work 0.98%; VEIL protocol work 0.03%.

### full-zk-verify-4096

[SVG](svg/full-zk-verify-4096.svg) · [attempt evidence](cases/full-zk-verify-4096/primary-001/attempt.json)

| Attribution | Symbol | Rows | Share | Source lookup |
| --- | --- | ---: | ---: | --- |
| inclusive | `<alloc::boxed::Box<dyn core::ops::function::FnOnce<(), Output = ()> + core::marker::Send> as core::ops::function::FnOnce<()>>::call_once` | 61249 | 75.79% | external or unresolved |
| inclusive | `<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}` | 61249 | 75.79% | external or unresolved |
| inclusive | `<rayon_core::registry::WorkerThread>::wait_until::<rayon_core::latch::OnceLatch>` | 61249 | 75.79% | external or unresolved |
| inclusive | `_pthread_start` | 61249 | 75.79% | external or unresolved |
| inclusive | `std::thread::lifecycle::spawn_unchecked::<<rayon_core::registry::DefaultSpawn as rayon_core::registry::ThreadSpawn>::spawn::{closure#0}, ()>::{closure#1}::{closure#0}` | 61249 | 75.79% | external or unresolved |
| self | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 44929 | 55.60% | external or unresolved |
| self | `<core::slice::iter::Iter<u32> as core::iter::traits::iterator::Iterator>::next` | 3762 | 4.66% | external or unresolved |
| self | `swtch_pri` | 3301 | 4.08% | external or unresolved |
| self | `_platform_memmove` | 2738 | 3.39% | external or unresolved |
| self | `core::core_arch::aarch64::neon::generated::vmull_p64` | 2189 | 2.71% | external or unresolved |

Self categories: sumchecks and constraint checks 55.94%; other or unresolved 17.22%; allocation and copying 9.12%; field arithmetic and transforms 8.41%; scheduling and synchronization 5.67%; transcript, hashing, and randomness 2.54%; PCS and Merkle work 1.08%; VEIL protocol work 0.02%.

## Endpoint repeat variability

The repeated endpoints use fresh attempts at full duration. Profiled call-rate delta is repeat relative to primary. Top self-share comparisons use the primary's leading self symbol; changing share does not itself establish a speed change.

The 64-hash repeats share the first measurement episode with their primaries. The 4,096-hash repeats belong to the resumed second episode, so their primary/repeat differences combine repeat variability with cross-session conditions. Use the resumed-episode baseline controls above when interpreting them.

| Case | Repeat episode | Usable rows primary / repeat | Profiled call-rate delta | Primary top self symbol | Self share primary / repeat |
| --- | --- | ---: | ---: | --- | ---: |
| [flock-prove-0064](cases/flock-prove-0064/repeat-001/attempt.json) | same episode as primary | 151546 / 158948 | +6.7% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 49.41% / 49.70% |
| [flock-prove-4096](cases/flock-prove-4096/repeat-002/attempt.json) | second; cross-session comparison | 160071 / 165670 | +5.6% | `swtch_pri` | 12.95% / 11.97% |
| [flock-verify-0064](cases/flock-verify-0064/repeat-001/attempt.json) | same episode as primary | 30678 / 30794 | +0.6% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 75.89% / 76.15% |
| [flock-verify-4096](cases/flock-verify-4096/repeat-002/attempt.json) | second; cross-session comparison | 31824 / 31851 | +0.4% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 59.85% / 59.92% |
| [full-zk-prove-0064](cases/full-zk-prove-0064/repeat-001/attempt.json) | same episode as primary | 105131 / 107542 | +8.7% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 34.63% / 35.69% |
| [full-zk-prove-4096](cases/full-zk-prove-4096/repeat-002/attempt.json) | second; cross-session comparison | 108516 / 109224 | +0.8% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 8.48% / 8.60% |
| [full-zk-verify-0064](cases/full-zk-verify-0064/repeat-001/attempt.json) | same episode as primary | 87649 / 94036 | +14.0% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 61.99% / 63.23% |
| [full-zk-verify-4096](cases/full-zk-verify-4096/repeat-002/attempt.json) | second; cross-session comparison | 80814 / 80976 | +0.8% | `<flock_core::lincheck::CscCircuit as flock_core::lincheck::LincheckCircuit>::fold_alpha_batched::{closure#0}` | 55.60% / 56.07% |

## Ranked follow-up experiments

These are hypotheses ranked by mean per-case self share across the 28 primary captures, giving every workload equal weight. They are not predicted speedups or a combined application CPU budget. Confirm the relevant symbols and repeat stability in the individual case before changing code.

1. **sumchecks and constraint checks** — mean self share 49.00%; largest observed case [flock-verify-0064](svg/flock-verify-0064.svg), 76.28%. Measure the leading packed reduction or fold at representative sizes. Zerocheck already fuses its fold with the first multilinear message (zerocheck.rs:467), and lincheck already fuses two binds with the next evaluation (lincheck.rs:1104). Test chunk sizing or reusable temporary storage while preserving bit-exact round messages and every public API witness and soundness check.

2. **scheduling and synchronization** — mean self share 13.45%; largest observed case [flock-prove-0256](svg/flock-prove-0256.svg), 31.94%. Inspect task granularity in the observed Rayon call paths. FsChallenger::grind_pow (challenger.rs:311) uses ordered parallel search above 8,192 expected hashes; lincheck's parallel threshold is 4,096 elements (lincheck.rs:944). Change one relevant threshold or chunk size at a time while preserving the shared verifier pool and canonical proof output. Compare latency with sampled scheduling activity; the latter is not blocked wall time.

3. **field arithmetic and transforms** — mean self share 10.49%; largest observed case [full-zk-prove-4096](svg/full-zk-prove-4096.svg), 28.36%. Benchmark the leading carryless-arithmetic or transform kernel at the recorded dimensions. The interleaved NTT already fuses layers and uses a 2 MiB subgroup target (ntt/additive_ntt_f128.rs:280); test subgroup size or task granularity before proposing more fusion. Require scalar-equivalent outputs and full protocol tests, then measure endpoint latency.

4. **allocation and copying** — mean self share 5.23%; largest observed case [full-zk-verify-1024](svg/full-zk-verify-1024.svg), 9.19%. Measure allocation counts and bytes on the leading call paths. If framed Merkle verification is implicated, test two reusable node buffers in verify_merkle_multi_proof_framed (merkle.rs:535), whose current level loop allocates a new vector. Preserve rejection checks, sibling ordering, and exact proof consumption; compare unprofiled medians and endpoint captures.

5. **transcript, hashing, and randomness** — mean self share 3.51%; largest observed case [full-zk-prove-4096](svg/full-zk-prove-4096.svg), 11.25%. Use caller stacks to separate Merkle hashing, transcript hashing, proof-of-work, and entropy acquisition. If proof-of-work dominates, test fixed-block hashing or nonce-batch sizing around sha256_has_leading_zero_bits (challenger.rs:400). Its encoded input is already a 41-byte stack array (ro.rs:189). Preserve difficulty, transcript bytes, the smallest successful nonce, and fresh full-ZK randomness.

## Evidence and limitations

[Manifest](manifest.json), [source archive and patch](source/), [validation/build logs](logs/), [all attempts](cases/), and per-attempt recorder/export status, harness JSON, folded stacks, original XML, and archived `.trace` directories preserve the evidence. Low-sample attempts remain archived; only accepted primary SVGs enter the matrix. The source archive includes uncommitted implementation files and the plan, so the base Git revision alone does not describe the measured code. No commit or push is part of this run.

Unknown addresses and explicitly marked truncation are counted above, but sampling cannot establish complete stacks or expose every short-lived function. Full-ZK randomness and warm-cache corpus reuse differ from independent one-shot verification. Compare small timing differences against the available baseline controls, symbol-build variability, and endpoint repeats; the sample totals are adequacy checks, not confidence intervals. One-time phases remain included in every SVG. Frame-based source lookup and self-category grouping are heuristic and must be verified before making optimization claims.

The first episode lacks an immediate closing baseline. The resumed interval's before/after controls describe only its four large endpoint repeats; they do not establish continuous thermal/load stability across the pause or retrospectively bracket the primary matrix.
