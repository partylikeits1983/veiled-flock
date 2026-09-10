# BLAKE3 preimage performance: results and flamegraphs

<a id="overview"></a>

This report brings together the complete reviewed results, findings, and **44
accepted SVG flamegraphs** from run `20260910T142900Z`. It compares the FLOCK
(non-ZK) and Full-ZK proof variants on the same BLAKE3 preimage workload, from
64 to 4,096 hashes.

**Proving time** measures creating a proof. **Verification time** measures checking
it. **Proof size** is the serialized proof's byte count under the recorded
serialization boundary. The flamegraphs show where sampled work occurred across
the process's threads. The timings come from separate, unprofiled benchmark runs.

<a id="measurement-conditions"></a>

**Read the results with these conditions in mind.** All 28 primary profiles ran
on battery, with charge falling from 27% to 11%; small endpoint repeats ended at
8% with an early battery warning. Large endpoint repeats ran about 100 minutes
later on AC while charging at 46%–51%. The first episode has no immediate closing
baseline. These results describe the recorded workloads and help choose follow-up
experiments; they do not establish a controlled optimization speedup. The
historical reference also used a different computer and source revision.

These opening sections are an editorial reading guide. The [complete reviewed
report](#complete-reviewed-report) and [complete findings](#complete-findings)
follow, preserving all their original narrative, numbers, and tables.

**Repository artifact scope.** This checkout includes the complete Markdown
reports, SVGs, PNG previews, benchmark CSVs, attempt records, logs, and source
archives. Raw Instruments recordings, exported XML, folded stacks, and compiled
executables remain in the local measurement archive. The historical inventories
and validation records describe that full archive, including files omitted from
Git. Reading the report requires no additional files; rerunning the assembler or
reprocessing a historical recording requires restoring the full archive first.

## Contents

- [What the results show](#guide-results)
- [Fresh performance at a glance](#performance-at-a-glance)
- [Historical reference supplied for this work](#historical-reference)
- [Explore the flamegraphs](#guide-flamegraphs)
- [Follow-up experiments](#guide-experiments)
- [Complete reviewed report](#complete-reviewed-report)
- [Complete findings](#complete-findings)
- [Endpoint repeat flamegraphs](#repeat-flamegraphs)
- [Smoke flamegraphs](#smoke-flamegraphs)
- [Evidence and run history](#evidence-and-run-history)

<a id="guide-results"></a>

## What the results show

- **Full-ZK costs more to prove and produces larger proofs in this baseline.**
  Its proving medians are 2.88–4.31 times FLOCK's; its verification medians are
  0.81–0.96 times FLOCK's. Median proof-size overhead ranges from 191.7% at 64
  hashes to 96.0% at 4,096 hashes.
- **Verification repeatedly concentrates in the same kernel.** The column-gather
  closure in `CscCircuit::fold_alpha_batched` accounts for 55.60%–75.89% of self
  sample rows across the four primary verification endpoints. The repeats retain
  the same leading hotspot. This makes it a useful experiment target, without
  predicting how much an implementation change would improve latency.
- **Large proving cases spread work across more kernels.** Field arithmetic,
  transforms, and scheduling become more visible at 4,096 hashes. Their exact
  shares and source references appear in the complete findings.

These observations summarize the [reviewed findings](20260910T142900Z/findings.md).
Sample shares and timing ratios use different denominators and should be read
separately.

<a id="performance-at-a-glance"></a>

## Fresh performance at a glance

**Machine:** Apple M1 Pro, 16 GiB memory. **Base revision:**
`73f5361629a2683b5e18bc084c7b64a0ab77fe05`. The frozen source also includes
uncommitted files recorded in the [run manifest](20260910T142900Z/manifest.json)
and source archive; the base revision alone does not identify the measured code.

The following are the normal-binary **before-baseline medians**, with one warm-up
and five samples per case. Setup, message/digest generation, and serialization
are outside the timing boundaries. Every generated proof is verified. Exact
values and size ranges are in [baseline-before.csv](20260910T142900Z/baseline-before.csv).

| Hashes | FLOCK prove (ms) | FLOCK verify (ms) | Full-ZK prove (ms) | Full-ZK verify (ms) |
| ---: | ---: | ---: | ---: | ---: |
| 64 | 4.385 | 14.221 | 18.901 | 12.389 |
| 128 | 4.919 | 14.542 | 18.221 | 12.228 |
| 256 | 6.070 | 14.465 | 18.868 | 12.374 |
| 512 | 7.897 | 14.885 | 22.737 | 13.196 |
| 1,024 | 9.184 | 16.000 | 31.730 | 13.021 |
| 2,048 | 13.801 | 16.000 | 47.878 | 14.565 |
| 4,096 | 22.646 | 17.716 | 84.103 | 17.006 |

| Hashes | FLOCK proof (B) | Full-ZK proof (B) | Size overhead |
| ---: | ---: | ---: | ---: |
| 64 | 274,609 | 801,097 | 191.7% |
| 128 | 283,537 | 800,777 | 182.4% |
| 256 | 377,697 | 801,545 | 112.2% |
| 512 | 385,081 | 811,793 | 110.8% |
| 1,024 | 398,657 | 847,521 | 112.6% |
| 2,048 | 433,425 | 863,953 | 99.3% |
| 4,096 | 451,937 | 885,841 | 96.0% |

Sizes are medians. Overhead is `(Full-ZK bytes / FLOCK bytes − 1) × 100`.
Full-ZK proof sizes vary with randomness; the complete report retains their
measured min–max ranges. Serialized sizes exclude returned witness commitments,
public digests, and bundle framing. Full-ZK batches of 64 and 128 pad to 256 slots.

| Hashes | Full-ZK / FLOCK prove time | Full-ZK / FLOCK verify time |
| ---: | ---: | ---: |
| 64 | 4.31× | 0.87× |
| 128 | 3.70× | 0.84× |
| 256 | 3.11× | 0.86× |
| 512 | 2.88× | 0.89× |
| 1,024 | 3.45× | 0.81× |
| 2,048 | 3.47× | 0.91× |
| 4,096 | 3.71× | 0.96× |

For each ratio, 1× means equal measured medians. These values compare variants
within this baseline; they do not measure a change made during this reporting task.
Increasing the hash count 64-fold changes proving medians by 5.16× for FLOCK and
4.45× for Full-ZK, and verification medians by 1.25× and 1.37× respectively.

The full report also preserves the symbol-build comparison, all four baseline
CSVs, and their size ranges. The largest original-before/final-after timing
change is 8.1%; the largest resumed-interval change is 6.7%; the symbol-build
comparison reaches 10.7%. These comparisons include measurement variability.
Only the resumed-before/final-after pair brackets the four resumed large repeats.

<a id="historical-reference"></a>

## Historical reference supplied for this work

This is the original seven-row table from [reference.csv](20260910T142900Z/reference.csv),
measured on an **Apple M2 Pro with 16 GiB**, revision
`9a369670ba5ad3d9a450b859572760b179085666`. Its machine and source differ from the
fresh M1 Pro series. The tables are separate observations; their differences do
not identify a code regression or speedup.

| Hashes | FLOCK prove (ms) | FLOCK verify (ms) | FLOCK proof (B) | Full-ZK prove (ms) | Full-ZK verify (ms) | Full-ZK proof (B) | Size overhead |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.944 | 13.123 | 274,609 | 19.350 | 11.454 | 801,705 | 191.9% |
| 128 | 5.140 | 13.544 | 283,537 | 18.987 | 11.338 | 801,865 | 182.8% |
| 256 | 6.447 | 13.467 | 377,697 | 19.485 | 11.534 | 802,185 | 112.4% |
| 512 | 7.961 | 14.042 | 385,081 | 24.723 | 12.499 | 811,281 | 110.7% |
| 1,024 | 10.381 | 14.460 | 398,657 | 32.597 | 11.974 | 847,489 | 112.6% |
| 2,048 | 15.925 | 15.033 | 433,425 | 49.119 | 13.442 | 863,857 | 99.3% |
| 4,096 | 23.917 | 16.476 | 451,937 | 81.780 | 15.662 | 885,585 | 96.0% |

<a id="guide-flamegraphs"></a>

## Explore the flamegraphs

Choose a case below to jump to its embedded SVG and detailed hotspot table.
Each full-size image has an **Open/download SVG** link. The report includes all
28 primary graphs, followed by eight endpoint repeats and eight smoke graphs.
The [existing HTML gallery](20260910T142900Z/index.html) provides another view of
the 28 primaries.

<!-- PRIMARY_MATRIX -->

**Reading a graph:** the frames show sampled call stacks. Width is the share of
usable sampled backtrace rows across all threads, with one count per usable row.
It is neither elapsed wall-clock time nor a weighted nanosecond sum. A frame's
vertical position describes call depth. **Self** counts attribute a row to its
leaf frame; **inclusive** counts also include callers, so inclusive percentages
overlap and cannot be added together. Sampled scheduler frames do not quantify
time blocked off CPU.

Embedded SVG images are static views. To use search and zoom, open or download
the SVG in a browser that permits its scripts. PNG links provide an optional
fallback for viewers without SVG support. All graphs use the corrected frame
labels; archived originals remain available as provenance.

The Markdown uses relative links to the adjacent `20260910T142900Z/` directory.
Keep that directory available when sharing the report and its assets; copying
the Markdown alone does not include its figures or evidence files. The evidence
index also links the earlier `20260910T142700Z/` unsuccessful preparation.

<a id="guide-experiments"></a>

## Follow-up experiments

The findings propose three practical starting points. They are hypotheses for
future work, and no optimization was made or measured during report assembly.

1. **Measure the column gather.** Start with `CscCircuit::fold_alpha_batched` at
   the recorded circuit dimensions. Investigate column lengths, memory locality,
   and serial/parallel work. Preserve row multiplicities and exact field results.
2. **Measure the large-case field and transform kernels.** Investigate the
   observed NTT, field-folding, and zerocheck kernels before changing subgroup
   size or task granularity. Check scalar-equivalent outputs.
3. **Measure task granularity.** Inspect the Rayon paths associated with sampled
   scheduling activity. Change one threshold or partition at a time, preserve
   the shared verifier policy, and compare unprofiled latency under consistent
   power conditions.

The complete findings retain the concrete tiling proposal, threshold details,
source links, and validation requirements. The complete report also retains its
broader ranked categories, including allocation/copying and transcript/hash work.
Those category means give each primary case equal weight; they are not a combined
application CPU budget or a prediction of achievable speedup.
