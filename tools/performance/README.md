# Preimage performance profiles

This local Rust workflow profiles the seven sizes in the README performance
table, with separate FLOCK/full-ZK prove/verify captures. New runs select 28
primary captures, eight endpoint smokes and eight endpoint repeats, with fresh
unprofiled CSV baselines. Reports and SVG galleries are published as immutable
generations beside the measurement evidence. Primaries and repeats default to
30 seconds; smokes use five seconds. Validation, compilation and export add time.

Execution completed for `20260910T142900Z`: **44 accepted recordings** comprise
28 primaries, eight smokes, and eight endpoint repeats. Frozen-source checks
(including `make test`), resumed baseline controls, raw-XML frame correction,
SVG rendering, and artifact checks completed successfully. Open the
[combined Markdown report with all 44 SVGs](../../reports/performance/preimage-flamegraphs/README.md),
[report](../../reports/performance/preimage-flamegraphs/20260910T142900Z/report.md)
or [28-SVG gallery](../../reports/performance/preimage-flamegraphs/20260910T142900Z/index.html).

The combined document includes a reading guide, the complete reviewed report
and findings, and primary/repeat/smoke figures. Its adjacent source and validation
records describe the assembly separately from the unchanged historical evidence.
The Git checkout includes the report, SVGs, previews, CSVs, records, logs, and
source archives. Raw recordings/XML, folded stacks, and compiled executables
remain local; historical inventories still describe the full measurement archive.
Restore that archive before running historical assembly or reprocessing commands.
To assemble another review copy into a fresh destination with the full archive:

```sh
cargo run --locked --release -p flock-performance --example assemble_preimage_markdown -- \
  reports/performance/preimage-flamegraphs/20260910T142900Z \
  tools/performance/assets/preimage-report-overview.md \
  reports/performance/preimage-flamegraphs/README-review.md
```

This example composes the existing reviewed documents and corrected SVGs. It
preserves existing destinations and does not perform new captures or XML analysis.

The run has a documented **power-protocol deviation**. Primary captures ran on
battery, declining from 27% to 11%; the small endpoint repeats ended at 8% with
an early battery warning. The resumed large repeats ran on AC power while
charging at 46%–51%. The primary episode also lacks an immediate closing
baseline. These results therefore do not establish an uninterrupted AC-only
benchmark or controlled cross-session timing changes. See the
[execution amendment](../../reports/performance/preimage-flamegraphs/20260910T142900Z/execution-plan-completed.md) and the report's
methodology and limitations.

The current recorder integration requires macOS, Xcode's Time Profiler,
the toolchain pinned in `rust-toolchain.toml`, and `rsvg-convert` for checking
rendered SVGs. Instruments must have permission to profile launched processes.
The repository `make test` prerequisites also apply, including the x86 Clippy
target.

New runs default to `--power-policy require-ac`: battery or unknown power
before a baseline/capture blocks launch; either observation afterward retains
the recording but prevents acceptance. An explicit
`--power-policy observe-only` is available when starting a new run. The policy
is fixed across its resumed episodes. Boundary observations do not establish
uninterrupted AC power or constant clocks.

Create a `chore/` branch and finish editing before running:

```sh
cargo install flamegraph --version 0.6.13 --locked \
  --root target/profiling-tools/flamegraph-0.6.13
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --seconds 30 --output reports/performance/preimage-flamegraphs/NEW-RUN
```

Replace `NEW-RUN` with a new run name, preferably a UTC timestamp. Existing
measurement directories are rejected. Automatic publication uses the sibling
`NEW-RUN-publication` directory and prints its immutable gallery path.
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
recordings cannot become selected SVGs, even if an SVG or harness success file
exists. Interrupted runners stop their child process groups and check
descendant cleanup. Command outcomes distinguish spawn failure, exit, signal,
interruption and cleanup failure; a child exiting zero after interruption is
still unacceptable. Bootstrap/controller failures retain separate records
and logs. One writer owns a run or publication at a time. A workload or
measurement-policy change requires a new run directory. Do not modify a
frozen source tree or reuse failed evidence.

Resume an unfinished run with its original measurement manifest:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --resume reports/performance/preimage-flamegraphs/NEW-RUN/manifest.json
```

Each continuation freezes and validates a separate controller source B while
preserving the original measurement source A, workload/helper executables and
toolchain/profiler hashes. It verifies selected evidence and runs only missing
case slots with fresh attempt IDs. A second interruption can be resumed under
the same identity checks; original evidence is retained. Changed or missing
measurement identities require a fresh run, and completed measurements use
report publication rather than another measurement episode.

New runs store episode records and before/symbols/after baseline controls under
`episodes/<id>/`. An interrupted episode remains unclosed. A later baseline
belongs to its new episode and cannot close an earlier interval. Build/check
work completes before settling and controls. Cargo-flamegraph still asks Cargo
to resolve artifact freshness; the runner checks measurement-target file bytes,
hashes, membership and modification times before and after it. Changes retain
the capture as unaccepted, including recompilation that produces an identical
executable. The only timestamp exception is Cargo's aggregate dependency file
`release/examples/preimage_profile.d`, which Cargo may refresh during a cached
build; its contents and existence are still checked. Executable, object and
fingerprint timestamps remain strict. Explicit builds stay outside captures.

The historical `20260910T142900Z` run used its earlier `resume.json` layout and
completed four missing large repeats in fresh `repeat-002` directories. Its
interrupted `repeat-001` remains excluded. The `baseline-resume-before.csv`
and final `baseline-after.csv` bracket only those four large repeats. Original
before/final after deltas cross sessions; 64-hash repeat comparisons belong to
the first episode and 4,096-hash comparisons cross episodes. The completed
historical files are preserved, including their documented power deviation.

To regenerate a report from completed evidence, provide a separate publication
root. Missing, identical, ancestor or descendant output destinations are
rejected before writes. Historical evidence is read-only; regeneration never
rewrites its report, analysis, attempts or editorial records:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --report reports/performance/preimage-flamegraphs/20260910T142900Z \
  --output reports/performance/preimage-publications/review-001
```

Use `--findings <markdown-file>` to include authored findings as a hashed
generation input. Required methodological caveats come from evidence even
when no authored findings are supplied. The processing source and executable
are frozen and verified separately from the measurement workload.

Publication stages a complete report/SVG/analysis generation, validates its
files and links, then moves it to `generations/<id>/` and atomically selects it
with `current.json`. Consumers resolve that pointer once; the CLI prints the
immutable `generations/<id>/index.html` path for local browsing. The generation
inventory hashes payload files, its manifest hashes the inventory, and the
external pointer hashes the manifest. Published generations are never edited.
Interrupted staging stays unpublished; a new processing attempt retains prior
outputs. Read-only reporting creates no measurement episode.

To validate the selected generation and print its immutable gallery path:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --current reports/performance/preimage-publications/review-001
```

If processing stopped after a complete generation was renamed but before its
pointer was selected, recover that ready generation by ID. Recovery rechecks
its files, links, processing identity and input hashes before selecting it;
partial staging directories cannot be recovered this way:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --recover-publication reports/performance/preimage-publications/review-001 \
  --generation GENERATION-ID
```

These operations can use the prebuilt `profile_preimages` executable directly;
`cargo run` may compile first and must stay outside active measurements.

Open the printed `index.html` locally or follow its relative report links.
Linked raw evidence remains a companion dependency: retain its declared
location when sharing, along with source archives and artifact checksums.

Before publishing, processing corrects an upstream xctrace-collapse formatting
defect: Rust array types such as `[u8; 64]` contain the same ASCII semicolon
used to delimit folded frames. It reconstructs stacks from raw XML frame
references, displaying semicolons inside names as `；`. Exact frame names and
recorded samples are preserved. Corrected derived files belong to the new
generation. This also runs when completing a new capture workflow; it does
not replace historical originals or prior corrected outputs.

The repair command uses the same publication path and requires a separate
destination:

```sh
cargo run --locked --offline --release -p flock-performance \
  --bin repair_preimage_report -- \
  reports/performance/preimage-flamegraphs/20260910T142900Z \
  --output reports/performance/preimage-publications/review-002
```

Run report builds and processing after the final baseline. Rebuilding tools
during active measurements would disturb the host. A legacy processing marker
must record completion before those inputs can be published; its existence
alone is insufficient. New generation provenance records reporting source,
dependencies, executable identity and input/output checksums separately from
the measurement snapshot. The old run's `report-processing.json` remains
historical evidence. Completion of a new run requires accepted measurements,
correction, rendering and artifact checks.

For cleanup correctness checks, build fresh release examples and run the
explicit integration test. It exercises both protocols/operations at 64 and
4,096 hashes, actual v1 metadata, exclusive metadata publication, diagnostic
reintroduction and the 14-row baseline CSV contract:

```sh
cargo build --locked --release -p flock-prover --features veil \
  --example preimage_profile --example preimage_scaling
FLOCK_PREIMAGE_PROFILE_BIN=target/release/examples/preimage_profile \
FLOCK_PREIMAGE_SCALING_BIN=target/release/examples/preimage_scaling \
cargo test --locked --release -p flock-performance --test harness_contract \
  short_endpoint_workloads_and_baseline_keep_the_v1_contract -- --ignored --nocapture
```

For a custom Cargo target directory, point the two variables at its examples.
Optional `FLOCK_PREIMAGE_CHECK_OUTPUT` retains correctness artifacts in a new
directory; relative artifact paths are resolved from the workspace root.
Otherwise the test removes its temporary files. These short checks
do not establish performance equivalence. The ordinary unit/integration suite
and repository `make test` remain required.

When harness or recorder integration changes, prepare a fresh frozen source
and tool build for four five-second Instruments smokes at 64 hashes:

```sh
FLOCK_PREIMAGE_SMOKE_OUTPUT=target/preimage-integration-smoke \
cargo test --locked --release -p flock-performance --test instruments \
  prepare_frozen_instruments_smoke -- --ignored --nocapture
```

This explicit macOS test runs frozen package/example checks and prepares a new
manifest without capturing. Preparation prints the recorded build environment
from `manifest.snapshot.build_environment`. Restore its exact values and
presence before launching the frozen runner: Cargo may inject `CARGO_HOME` and
`RUSTUP_HOME` that are absent in a plain shell. Remove extra build settings;
do not edit the accepted manifest or bypass its environment check. After all
editing and builds finish, invoke the printed frozen runner with
`--integration-smoke-frozen <manifest-path>`. It
checks both protocols and operations, usable workload samples, and the required
verifier/Rayon workers. These are integration checks with their own evidence;
they produce no performance baseline or published benchmark report.

The workflow leaves all changes local. **Do not commit or push without the
user's explicit approval**; approval to run or resume measurements authorizes
neither action.
