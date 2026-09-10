# Preimage performance profiles

This local Rust workflow profiles the seven sizes in the README performance
table, with separate FLOCK/full-ZK prove/verify captures. It creates 28 primary
SVGs, eight endpoint repeats, fresh unprofiled CSV baselines, a report and a
local HTML gallery. The default workload is 30 seconds per capture; validation,
compilation, smoke recordings and export add time.

Execution status for `20260910T142900Z`: all 28 primary captures, eight smokes,
four 64-hash repeats, and the original normal-before/symbol baselines were
collected before a pause. The first 4,096-hash FLOCK-prove repeat was interrupted.
The four large endpoint repeats, resumed baseline controls, corrected derived
SVGs, and final report remain pending. See the
[execution amendment](../../.claude/plans/preimage-flamegraphs.md).

The current recorder integration requires macOS, Xcode's Time Profiler,
Rust 1.98.0, and `rsvg-convert` for checking rendered SVGs. Run on AC power.
Instruments must have permission to profile launched processes. The repository
`make test` prerequisites also apply, including the x86 Clippy target.

Create a `chore/` branch and finish editing before running:

```sh
cargo install flamegraph --version 0.6.13 --locked \
  --root target/profiling-tools/flamegraph-0.6.13
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --seconds 30 --output reports/performance/preimage-flamegraphs/20260910T150000Z
```

Choose a new UTC run directory each time. Existing directories are rejected.
Custom `CARGO_TARGET_DIR` paths, including spaces, are supported. The profiler
installation remains at the explicit workspace-local path above.

Bootstrap reconstructs uncommitted source into a private read-only copy under
`/private/tmp`, runs final checks there, and builds separate checking, tooling,
normal release and symbol-enabled release artifacts. Cargo's JSON output
selects the executables. The snapshot-built runner performs all measurements.
Source archives, inventories, tool hashes, commands, statuses and raw traces
are retained. The runner never changes the Git index, commits or pushes.

All workloads and recorder children remove the diagnostic/default-policy keys
in `measurement-env.json`. The harness independently checks them before
creating thread pools. A diagnostic key set to `0` or empty is still present
and is rejected. Baselines use their prebuilt executables directly and verify
every generated proof. Profiling prove loops verify the warm-up and final
proof; verification loops rotate through eight prevalidated proofs.

Profiles contain whole-process sampled work across all threads, including
preparation, proof destruction and final verification. Inferno's xctrace
collapse counts usable backtrace row occurrences; the report labels this
denominator and does not reinterpret it as wall-clock latency or xctrace's
weighted-time column. Published M2 Pro numbers remain a historical reference,
separate from measurements on the current host.

Every attempt gets fresh scratch/evidence directories. Interrupted or failed
recordings cannot become primary SVGs, even if an SVG or harness success file
exists. Interrupted runners stop their child process groups. Failed runs retain
`incomplete.json` and logs. A workload or measurement-policy change requires a
new run directory. Do not modify a frozen source tree or reuse failed evidence.

To resume the current interrupted run with unchanged measurement artifacts:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --resume reports/performance/preimage-flamegraphs/20260910T142900Z/manifest.json
```

Resume prepares, validates, and builds a separate frozen controller source B.
It records that controller in `resume.json` while preserving and rechecking
the original source A, workload/helper executables, and toolchain/profiler
hashes. The original primaries and accepted small endpoint repeats remain
accepted evidence. Only the four missing large endpoint repeats run, each in
a fresh attempt directory; the interrupted `repeat-001` remains archived.
If original measurement identities cannot be preserved, start a new run.

The resumed interval gets its own `baseline-resume-before.csv` and final
`baseline-after.csv`, both from the original normal benchmark executable.
This creates two measurement episodes. The first episode has no immediate
closing baseline, so original-before/final-after deltas are cross-session
changes. The resumed controls bracket only the four large repeats. The report
labels 64-hash repeat comparisons as same-episode and 4,096-hash comparisons
as cross-session; it does not claim uninterrupted baseline coverage.

To regenerate only the report from completed evidence:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --report reports/performance/preimage-flamegraphs/20260910T150000Z
```

Open `index.html` locally or follow the relative links in `report.md`. Bulky
raw traces and debug artifacts can be packaged separately when sharing, while
retaining the artifact checksums and source-to-capture mapping.

Before publishing, the report step corrects an upstream xctrace-collapse
formatting defect: Rust array types such as `[u8; 64]` contain the same ASCII
semicolon used to delimit folded frames. It reconstructs stacks from the raw
XML frame references, displaying semicolons inside names as `；`. Original
profiler outputs, exact frame names, and processing checksums are retained;
recorded samples and workload metadata are unchanged. This step also runs when
completing the capture workflow above.

To apply the correction once to an older completed run:

```sh
cargo run --locked --offline --release -p flock-performance \
  --bin repair_preimage_report -- reports/performance/preimage-flamegraphs/20260910T150000Z
```

Run report builds and processing after the final baseline. Rebuilding tools
during active measurements would disturb the host. The processing manifest
`report-processing.json` separately records reporting code/dependencies,
executable identities, input/output checksums, and preserved original-artifact
paths. It does not replace the original measurement snapshot or the resumed
controller's provenance. A report is complete only after the remaining
measurements, correction, rendering, and artifact checks succeed.

The workflow leaves all changes local. **Do not commit or push without the
user's explicit approval**; approval to run or resume measurements authorizes
neither action.
