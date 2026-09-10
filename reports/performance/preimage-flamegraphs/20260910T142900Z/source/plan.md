# Plan: profile the BLAKE3 preimage performance table

Date: 2026-09-10. Status: planned; captures and measurements have not run.

Produce a performance report with **28 flamegraph SVGs**, covering all seven
batch sizes in the [README performance table](../../README.md#performance):
64, 128, 256, 512, 1,024, 2,048, and 4,096 hashes. At each size, capture
non-ZK FLOCK prove, non-ZK FLOCK verify, full-ZK prove, and full-ZK verify.
Include fresh unprofiled timings and proof sizes alongside the supplied
historical results, then identify measured hotspots and optimization candidates.

## 0. Create the work branch and preserve approval requirements

Before implementation, inspect the current branch and working-tree status,
preserve existing changes, and create a dedicated branch from the current HEAD:

```sh
git switch -c chore/preimage-flamegraphs
```

Use the conventional `chore/` prefix for this profiling-tooling and reporting
work. If that branch already exists, verify whether it belongs to this task;
reuse it only when appropriate, otherwise choose a new `chore/` name without
resetting or overwriting an existing branch. Record the selected branch and
starting revision in the run manifest.

**Do not commit or push without the user's explicit approval.** Approval of
this plan or its implementation does not authorize either action. Approval
to commit does not authorize a push unless the user explicitly approves both.
Apply this restriction to automated scripts and delegated work as well.

Complete implementation, validation, captures, and the local report first.
Present the resulting diff, check results, report, and SVGs for review before
requesting approval to commit or push. Leave the completed work local and
uncommitted while awaiting that approval; a commit or push is not required
to complete this plan's local deliverables.

## 1. Establish the measurement environment

The planning inspection found:

| Item | Published table | Current workspace / host |
| --- | --- | --- |
| Revision | `9a369670ba5ad3d9a450b859572760b179085666` | `73f5361629a2683b5e18bc084c7b64a0ab77fe05` |
| CPU / memory | Apple M2 Pro / 16 GiB | Apple M1 Pro / 16 GiB |
| Rust | 1.98.0 | 1.98.0, `aarch64-apple-darwin` |
| Benchmark | `preimage_scaling` example | Same example exists |
| Profiler | Not specified | cargo-flamegraph 0.6.6; Xcode xctrace 26.0 available |

- Profile a frozen source snapshot of the current revision plus all local
  implementation changes. Preserve staged, unstaged, and untracked source
  contents before final validation, and run all accepted checks, builds, and
  captures against that private source copy. Save the exact Git revision,
  dirty status, Cargo.lock checksum, OS version, CPU/memory details, tool
  versions, commands, and relevant build environment in the run manifest.
- Preserve the supplied table as `reference.csv`, with its original machine
  and revision. Treat new numbers as a separate measurement series; differences
  across these machines and revisions do not establish a code regression.
- Apply the measurement-environment contract below to both unprofiled
  baselines, the baseline with debug symbols, correctness checks, smoke
  captures, primary captures, and repeats. Call `init_perf_thread_pool()`
  before parallel work and record the actual pool size. Preserve the separate
  verifier pool and its thread policy.
- Run captures serially on AC power with other heavy work stopped. Record
  power mode and any thermal or background-load interruptions.

### Measurement-environment contract

The root cause is inside the timed public APIs: `finalize_commit` checks
`var_os("FLOCK_COMMIT_TIMING").is_some()` and conditionally formats and writes
timing messages to stderr. See
[`commit.rs`](../../crates/flock-core/src/pcs/commit.rs). Setting the variable
to `0` or an empty string enables those branches. Redirecting stderr still
executes the formatting and IO. Recording the setting without removing it
would preserve the measurement contamination.
The kernels' unconditional timer calls remain part of the measured code.

The source audit found additional diagnostic switches. Clear the complete
list consistently, while distinguishing active preimage paths from adjacent
code paths:

| Variables to remove | Reason / source |
| --- | --- |
| `FLOCK_COMMIT_TIMING` | Commitment timing output inside proving; [`pcs/commit.rs`](../../crates/flock-core/src/pcs/commit.rs). |
| `FLOCK_ZC_TIMING` | Zerocheck timing output; [`zerocheck.rs`](../../crates/flock-core/src/zerocheck.rs). |
| `LINCHECK_TRACE`, `VERIFY_TRACE` | Prover/verifier tracing; [`lincheck.rs`](../../crates/flock-core/src/lincheck.rs), [`verifier.rs`](../../crates/flock-core/src/verifier.rs). |
| `PCS_TRACE`, `LIG_PROVE_TRACE`, `LIG_VERIFY_TRACE` | PCS and Ligerito tracing; [`pcs.rs`](../../crates/flock-core/src/pcs.rs), [`ring_switch.rs`](../../crates/flock-core/src/pcs/ring_switch.rs), [`ligerito.rs`](../../crates/flock-core/src/pcs/ligerito.rs). |
| `LIGERITO_TRACE`, `PERM_TRACE`, `MERKLE_TRACE` | Diagnostics in alternate or adjacent code paths; clear them too, without claiming all are reached by this benchmark. |
| `RAYON_NUM_THREADS` | Preserve the benchmark's default performance-core pool. |
| `FLOCK_NO_PREFAULT` | Preserve the default allocation policy. Its helper is not reached by the current preimage APIs; this is a default-setting rule, not a measured cost attribution. |

Store this explicit list in `tools/performance/measurement-env.json`, included
by the Rust runner/helpers and profiling example at compile time. Apply it
through one child-command builder using `Command::env_remove` for every key.
Use the same policy in the xctrace wrapper before launching the real recorder.
Keep unrelated environment intact and apply the separately recorded toolchain
and build settings explicitly;
do not clear the entire environment or use wildcard removal of `FLOCK_*`,
which would also remove the capture helpers' own configuration.

Use `var_os` for presence checks so empty and non-Unicode values are detected.
The profiling harness must validate absence of all listed keys before creating
thread pools or setups, then record that observation in its final metadata.
Unexpected presence fails the capture. The runner records the effective child
environment for direct baseline commands; an actual xctrace smoke capture
must confirm the launched harness observes the same policy. Do not mutate the
parent process's environment after threads start.

The primary series always uses this policy. Diagnostic experiments, if needed
to investigate a failure, receive separate run IDs and cannot supply baseline
numbers or primary SVGs. Absence of known diagnostic messages in workload logs
is an additional check; the environment observation is the acceptance rule.

Use a workspace-local installation of flamegraph **0.6.13**, pinned and
version-checked, so the Mac uses its xctrace backend. Upstream switched macOS
profiling from DTrace to xctrace in 0.6.8; the installed 0.6.6 predates that
change. See the [upstream release notes](https://github.com/flamegraph-rs/flamegraph/releases).

```sh
cargo install flamegraph --version 0.6.13 --locked \
  --root target/profiling-tools/flamegraph-0.6.13
```

Check `xcrun xctrace list templates` and run a short capture before the full
matrix. Request any actual OS profiling permission when encountered. If the
backend cannot collect usable stacks, preserve its error and resolve the
capture prerequisite before the full run. A run on another host needs its own
baseline and environment label.

## 2. Add a focused profiling harness

Add `crates/flock-prover/examples/preimage_profile.rs`, gated by the existing
`veil` feature in its Cargo example declaration. Its proposed interface is:

```text
preimage_profile --protocol flock|full-zk --operation prove|verify
                 --hashes 64|128|256|512|1024|2048|4096
                 --seconds 30 --attempt-id <id> --metadata <path>
```

Reject invalid arguments and zero durations. Reuse the deterministic message
generator and protocol domain from
[`preimage_scaling.rs`](../../crates/flock-prover/examples/preimage_scaling.rs),
through a small shared example-support module if needed. Keep the existing
benchmark command and CSV columns compatible.

Harness behavior:

1. Initialize thread pools, messages, public digests, and the selected setup
   once. Perform one warm-up prove/verify pair before the repeated workload.
2. Call the same public APIs as the table: `Blake3PreimageSetup::prove/verify`
   or `Blake3PreimageZkSetup::prove/verify`. Preserve all API witness checks,
   transcript work, configuration validation, and soundness checks.
3. For non-ZK, construct a fresh `FsChallenger` for each call with domain
   `b"flock-blake3-preimage-scaling"`. Full-ZK proving keeps its normal fresh
   OS-seeded randomness and internally initialized challenger.
4. For prove captures, repeatedly generate proofs and retain only the latest
   result; release the previous result to bound memory. Verify the final proof
   after the loop. Explicitly report that warm-up and final outputs are
   checked in the profiling harness; the separate baseline verifies **every**
   generated proof. Do not retain an unbounded batch of proofs.
5. For verify captures, prepare and validate a small fixed corpus, such as
   eight proofs, before the loop. Rotate through it without cloning or
   serializing inside the loop. Record corpus size; this is a warm-cache
   repeated-verification workload. Every verification must succeed.
6. Use `std::hint::black_box` on relevant inputs/results. Record loop duration,
   completed calls, preparation/validation/cleanup durations, and thread counts
   outside the loop. Include the attempt ID, selected workload, requested
   duration, observed measurement-environment policy, and final validation result in the
   metadata. Write the success metadata atomically only after the complete
   workload and final validation finish. Keep logging and serialization outside
   the loop.

The primary SVGs show **whole-process sampled CPU**, dominated by one repeated
operation. They include one-time preparation and final validation, plus loop
overhead such as challenger construction and proof destruction. They are not
an assertion of exact isolation to the README's timer boundaries. Keep those
frames visible and describe their contribution. Inspect the raw trace if
preparation, proof-corpus generation, or cleanup materially affects a capture;
extend the run or use a validated temporal slice before drawing API-specific
conclusions. A temporal slice must retain all process threads and establish
the mapping between harness phase boundaries and trace timestamps.

**Capture all process threads.** Verification executes on the dedicated
`flock-verify` worker, and full-ZK proving uses Rayon workers. Filtering solely
for a main-thread harness function would discard real work.

## 3. Preserve release optimization and collect fresh baselines

This section defines the build and measurement commands. Execute them in the
order specified in section 5. Final validation and builds use the private
source root prepared in section 4; preliminary builds in the editing checkout
do not qualify as measurement artifacts.

The table uses `cargo run --release`, while `[profile.bench]` additionally
enables thin LTO and one codegen unit. Use the release profile for these
examples. Add debug symbols through environment settings for profiling;
retain `.cargo/config.toml`'s `target-cpu=native` and avoid replacing `RUSTFLAGS`.
Resolve one Cargo target root, then allocate fresh per-series `checks`, `tools`,
`performance-normal`, and `performance-symbols` directories beneath it. Keep
build outputs outside the frozen source inputs. All build commands run from
the frozen root with its manifest and the recorded Rust toolchain selected
explicitly. Prebuild both workload variants before the first baseline; the
final baseline must reuse the normal executable without a symbol-to-normal
rebuild. Resolve both `preimage_scaling` executables from Cargo's JSON build
output, record their paths/checksums, and launch those binaries directly
through the shared child-command builder. The runner performs no Cargo launch
between baseline environment sanitization and workload execution.

Run the unchanged benchmark before and after the capture series under the
same runtime-environment policy. This standalone invocation, from the frozen
root, documents the equivalent benchmark; the automated runner uses the
prebuilt binary and does not invoke Cargo for baseline measurements:

```sh
env -u RAYON_NUM_THREADS -u FLOCK_NO_PREFAULT \
  -u FLOCK_COMMIT_TIMING -u FLOCK_ZC_TIMING \
  -u LINCHECK_TRACE -u VERIFY_TRACE -u PCS_TRACE \
  -u LIGERITO_TRACE -u LIG_PROVE_TRACE -u LIG_VERIFY_TRACE \
  -u PERM_TRACE -u MERKLE_TRACE -u CARGO_PROFILE_RELEASE_DEBUG \
  -u CARGO_PROFILE_RELEASE_STRIP \
  CARGO_TARGET_DIR="$normal_target_dir" \
  cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 5
```

Save both CSV outputs and stderr. Each baseline retains one warm-up, five
samples, median prove/verify timings, and median/min/max serialized proof
bytes. If the two runs differ enough to alter the report's conclusions,
investigate load/thermal drift and repeat the affected baseline.

Prebuild the profiling example with the lockfile enforced:

```sh
CARGO_TARGET_DIR="$symbol_target_dir" \
  CARGO_PROFILE_RELEASE_DEBUG=2 CARGO_PROFILE_RELEASE_STRIP=none \
  cargo build --locked --release -p flock-prover --features veil \
  --example preimage_profile
```

Also run the existing timing benchmark once with those same symbol settings
and the same runtime environment to check for a material build-setting effect.
Remove inherited `CARGO_PROFILE_RELEASE_DEBUG` and
`CARGO_PROFILE_RELEASE_STRIP` with `Command::env_remove` for both normal
baseline builds/runs. Set those variables explicitly only for the symbol
baseline and profiling builds, so launching the runner from a shell with
profiling settings cannot change the normal baseline. Keep profiled loop
timings separate from the unprofiled baseline.

## 4. Automate capture and preserve evidence

Add a Rust workspace package, `flock-performance`, at `tools/performance/`,
with three binaries and shared support code:

| Rust source | Binary | Responsibility |
| --- | --- | --- |
| `src/bin/profile_preimages.rs` | `profile_preimages` | Build the harness, drive the matrix sequentially, write metadata, and validate artifacts. |
| `src/bin/xctrace_capture.rs` | `xctrace_capture` | Delegate to xctrace and preserve raw traces and exported XML. |
| `src/bin/folded_capture.rs` | `folded_capture` | Save folded stacks while forwarding identical bytes to stdout for SVG generation. |

Register the package in the root workspace and update/review Cargo.lock before
the locked builds and recording its final checksum. Reuse workspace
`serde`/`serde_json` for structured metadata;
use `std::process::Command`, `std::fs`, and `std::io` for orchestration and
artifact IO. Keep capture automation and helpers in Rust.

### Preserve the uncommitted source and build identity

Capturing provenance after compilation can pair an old executable with newer
source. Hashing a mutable checkout before and after compilation still misses
a file changed and then restored while the compiler reads it. The accepted
compiler inputs must therefore be the preserved private copy itself.

After implementation, Cargo.lock updates, and formatting in the editing
checkout, prepare the snapshot **before final checks and builds**. Preliminary
development checks may run earlier, but do not replace final validation of
the snapshot. Do not change the user's Git index or create a commit.
The snapshot's input scope includes workspace manifests,
Cargo.lock, rust-toolchain.toml, `.cargo` configuration, all workspace crate
sources/configurations/build scripts, local path dependencies, the new Rust
tooling, `measurement-env.json`, Makefile, and files needed by invoked validation
commands. Exclude generated reports, scratch traces, and Cargo target
directories; record exclusions explicitly.

- Save the base revision and Git status. Capture final tracked contents relative
  to HEAD with `git diff --binary --full-index --no-ext-diff --no-textconv HEAD --`
  restricted to that input scope. This includes the combined staged and
  unstaged result actually present in the working tree.
- Enumerate new files with `git ls-files --others --exclude-standard -z` and
  copy build-relevant entries as raw bytes under `source/untracked/`, preserving
  relative paths. Include any ignored build input referenced by the manifests
  or source explicitly. Record each input's hash, type, executable mode or
  symlink target, and deletions in `source/inputs.json`; hash bytes, not lossy
  text conversions. Parse Git path lists as NUL-delimited data.
- Copy this plan into `source/plan.md` explicitly because `.claude/` is ignored.
  Save the base revision, patch, input inventory, new files, relevant build
  configuration, and tool versions under `source/`. Reuse workspace `sha2` for
  SHA-256 checksums. Record only relevant environment keys, not a full dump.
- Materialize HEAD plus the patch and copied new files into a fresh private
  source root outside the editing checkout and its target directories, such as a
  task-specific directory under `/private/tmp`. Compare inventories taken
  before/after snapshot preparation with the materialized copy, including path
  membership and file contents. If they differ, discard that candidate and
  prepare it again before running final checks. Give the verified copy a
  content-derived snapshot ID and preserve that exact inventory.
- Copy source bytes independently; do not hardlink them to the editing checkout
  or retain source/configuration symlinks resolving outside the inventoried
  private inputs. Preserve internal layout and executable bits. External local
  dependencies or configuration references must be frozen consistently before
  proceeding. Snapshot creation preserves the user's tree and index.
- Make inventoried source files/directories read-only in the private root.
  Precreate an excluded writable `.profile-scratch/` child for recorder working
  directories; Cargo outputs go to the separate per-series target directories.
  Record sealing permissions separately from the original executable modes.
  Final formatting uses `cargo fmt --all -- --check`, and tests write fixtures
  only to designated temporary/output directories. A source-writing check must
  fail rather than modify the snapshot.
- Run final checks and every explicit build against this root, checking its
  inventory before and after each operation. Register executable checksums only
  after successful validation/build completion and unchanged inputs. Preserve
  the source copy or a verified archive, original source-path mapping, commands,
  and logs so debug information can still resolve snapshot source locations.
- Record executable checksums for the normal baseline, symbol baseline,
  profiling harness, runner, both helpers, and selected profiler. Retain the
  profiling executable and its required debug-symbol artifacts for trace
  analysis. Use the separate workload target directories defined in section 3
  and save the role-to-executable mapping in `builds.json`.

Cargo discovers configuration from its working directory, ancestors, and Cargo
home; setting `--manifest-path` alone does not isolate those inputs. Keep the
private root outside the editing checkout and inventory applicable external
Cargo configuration as well. Freeze needed settings/references and verify
the isolated build resolves the intended flags, including `target-cpu=native`.
Select the recorded Rust 1.98.0 toolchain explicitly for final commands rather
than inheriting a directory override. If equivalent configuration cannot be
established, fail preparation instead of silently changing the build.
See [Cargo configuration discovery](https://doc.rust-lang.org/cargo/reference/config.html#hierarchical-structure).

Recheck the frozen inputs and recorded build configuration before and after
each check, build, baseline, and capture. Tie every result to its snapshot ID
and executable identity. An unexpected change to the frozen tree, Cargo.lock,
compiler settings, selected tools, runtime policy, or a role's executable
invalidates that series. Preserve it as incomplete and start a new snapshot,
validation, and measurement series. Each intentional normal/symbol variant
must match its own registered identity.

Subsequent edits in the editing checkout cannot affect a running snapshot
build and do not redefine its provenance. If those edits are intended fixes
for this task, finish them in the editing checkout and start a new snapshot
and series; never patch the frozen copy. Report-only changes can reuse unchanged
evidence. This binds measurements to preserved inputs on this host; it does
not assert byte-identical builds across different machines.

The initial runner invocation in the editing checkout is a bootstrap step:

```sh
cargo build --locked --release -p flock-performance --bin profile_preimages
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --seconds 30 \
  --output "reports/performance/preimage-flamegraphs/<UTC-run-id>"
```

Replace `<UTC-run-id>` with the run's UTC timestamp.

Bootstrap mode prepares/verifies the source copy, runs its final validation,
and builds the accepted runner/helpers/workloads from that copy. It then
launches the frozen runner using the absolute Cargo-JSON artifact path and an
internal `--frozen-run <run-config-path>` mode. That mode loads the prepared
snapshot/build identities, verifies its own executable hash, and proceeds with
smoke captures and measurements without preparing another snapshot. The live
bootstrap binary is recorded separately and cannot substitute for the accepted
runner. Bootstrap itself does not collect measurements.

Pass absolute paths for the frozen manifest, all target directories, report
root, and pinned profiler installation. Prepend that installation's `bin`
directory to child PATH and verify its version. Locate helpers beside the
accepted runner using `std::env::current_exe()` and verify their registered
hashes. Never fall back to binaries from the editing checkout or an older run.

Give every smoke, primary, repeat, and retry capture a fresh attempt ID and
exclusively created directory. Refuse to reuse an existing attempt directory.
Use separate locations for the profiler's working files and retained evidence:

```text
<frozen-root>/.profile-scratch/<case>/<attempt-id>/
  cargo-flamegraph.trace          # recorder working directory; upstream deletes it

<report-root>/cases/<case>/<attempt-id>/
  raw/recording.trace/            # preserved copy; outside recorder directory
  raw/time-profile.xml
  stacks.folded
  flamegraph.svg
  harness.json
  record-status.json
  export-status.json
  attempt.json                    # capture kind, parameters, validation outcome
  logs/
```

Keep recorder scratch beneath the private root so Cargo discovers the frozen
`.cargo/config.toml`. Both the manifest and the current working directory
must refer to this root, including cargo-flamegraph's internal Cargo builds.
The scratch location is independent of the external `CARGO_TARGET_DIR` used
for build artifacts. Check the canonical scratch and archive paths are
distinct and neither contains the other. Copy into a temporary archive
directory, finish and validate the copy, then rename it to `raw/recording.trace`
before allowing upstream export/cleanup. Preserve failed attempts and label
partial evidence; retries get a new ID. Record the capture kind separately
from the case so endpoint repeats cannot replace a validated primary SVG.

The runner must accept a capture only when its own interruption state is
clear, cargo-flamegraph exits successfully, both wrapper status files report
normal successful completion and artifact IO, and the harness metadata matches
the current attempt ID, protocol, operation, hash count, and requested duration.
Also require successful final validation, a positive completed-call count,
and an observed loop duration at least as long as requested. Missing, stale,
or mismatched metadata fails the attempt even if an SVG exists. Check the
raw trace, XML, folded stacks, SVG, source identity, and observed environment
before marking the attempt complete.

The pinned tool's Cargo interface does not expose `--locked` and still invokes
Cargo before every capture. Prebuild with `--locked`, then run those internal
builds offline against the same frozen manifest, configuration, toolchain,
and symbol target directory. The read-only lockfile and input/executable
checks must reject unexpected changes; an internal build must never fall back
to the editing checkout. Do not pass unsupported flags.

Command shape after the harness and capture helpers exist, run from the
attempt's scratch directory with paths supplied by the runner. Here
`manifest` is `<frozen-root>/Cargo.toml`, `target_dir` is the registered
`performance-symbols` directory, and the runner supplies the pinned toolchain:

```sh
env -u RAYON_NUM_THREADS -u FLOCK_NO_PREFAULT \
  -u FLOCK_COMMIT_TIMING -u FLOCK_ZC_TIMING \
  -u LINCHECK_TRACE -u VERIFY_TRACE -u PCS_TRACE \
  -u LIGERITO_TRACE -u LIG_PROVE_TRACE -u LIG_VERIFY_TRACE \
  -u PERM_TRACE -u MERKLE_TRACE \
  CARGO_NET_OFFLINE=true CARGO_PROFILE_RELEASE_DEBUG=2 \
  CARGO_PROFILE_RELEASE_STRIP=none CARGO_TARGET_DIR="$target_dir" \
  XCTRACE="$xctrace_capture" FLOCK_PROFILE_XCTRACE_BIN="$real_xctrace" \
  FLOCK_PROFILE_ATTEMPT_ID="$attempt_id" \
  FLOCK_PROFILE_ATTEMPT_DIR="$attempt_dir" \
  FLOCK_PROFILE_FOLDED_PATH="$folded_path" \
  cargo flamegraph --manifest-path "$manifest" \
    -p flock-prover --features veil --example preimage_profile \
    --deterministic --title 'Full-ZK prove / 4096 hashes' \
    --post-process "$folded_capture_command" -o "$svg_path" -- \
    --protocol full-zk --operation prove --hashes 4096 \
    --seconds 30 --attempt-id "$attempt_id" --metadata "$metadata_path"
```

Construct subprocess arguments with `Command::arg`/`args` and set child
environment variables with `Command::env`; launch binaries directly.
The `--post-process` option is a command string parsed by flamegraph:
`folded_capture_command` must encode the absolute `folded_capture` executable
path using that parser's quoting rules. Pass its output destination through
`FLOCK_PROFILE_FOLDED_PATH`, so paths containing spaces work without embedding
the destination in the command string. The helper streams stdin to the saved
file and stdout byte for byte, and fails on read, write, or flush errors.

Three backend details need explicit handling, confirmed against the
[0.6.13 implementation](https://github.com/flamegraph-rs/flamegraph/blob/v0.6.13/src/lib.rs):

- macOS uses the Time Profiler template. Custom `--freq`, custom `--cmd`, and
  Linux-only `--no-inline` are unsuitable here. Record the actual trace sampling
  metadata; do not label the capture 997 Hz merely from the CLI default.
- The tool deletes `cargo-flamegraph.trace` after export. Set `XCTRACE` to the
  Rust `xctrace_capture` binary. Resolve the real tool once with
  `xcrun -f xctrace` and pass its absolute path in
  `FLOCK_PROFILE_XCTRACE_BIN`, avoiding recursive invocation of the wrapper.
  Forward the original arguments with `std::env::args_os()` and stdout without
  adding diagnostics; inherit stderr or drain it concurrently. After successful
  recording, archive the complete trace as described above. During export,
  stream stdout both to `raw/time-profile.xml` and unchanged to flamegraph.
  Record each stage's original child exit code or terminating signal, attempt
  ID, and artifact-copy/IO outcome in its own status file under
  `FLOCK_PROFILE_ATTEMPT_DIR`. Write successful status atomically only after
  the stage and its artifact writes complete. Save folded stacks through the
  Rust `folded_capture` helper passed to `--post-process`.
- cargo-flamegraph accepts recorder SIGINT, SIGTERM, and macOS exit code 54
  and may continue exporting. Preserve the original status in metadata, but
  normalize every interrupted or unsuccessful wrapper stage to ordinary exit
  code **1**, including copy/IO failures; return **0** only after complete
  success. The runner must independently inspect both wrapper status files,
  rather than relying on cargo-flamegraph's exit code or the harness success
  marker. If the wrapper is killed before writing a status file, the missing
  file fails the attempt. An interruption after harness success, including
  during trace finalization, must still prevent publication of that capture.

## 5. Validate, then run the complete matrix

This is the authoritative execution order:

1. Finish implementation, Cargo.lock updates, and formatting in the editing
   checkout. Preliminary development checks are allowed here. Start bootstrap
   preparation; preliminary executables/check results do not qualify as final
   validated artifacts.
2. Prepare, reconstruct, verify, and seal the private source copy and record
   its input inventory/snapshot ID **before final validation or compilation**.
   Resolve its build configuration and toolchain. Allocate fresh per-series
   checks/tools/normal/symbol outputs and recorder scratch. If preparation
   observes changing inputs, retry it before running checks.
3. In the frozen root, run check-only formatting,
   `cargo test --locked -p flock-performance`, the helper tests below, and
   applicable repository checks (`make test` for implementation changes).
   Run correctness checks for all 28 harness selections, invalid arguments,
   challenger resets, proof validity, and bounded memory. Confirm the existing
   benchmark still emits all 14 protocol/size rows correctly. Recheck frozen
   input/configuration identities around each operation.
4. Build the final normal/symbol workloads and all three Rust tools from that
   same root. Register each executable only after the build succeeds and
   its input inventory remains equal to the previously validated snapshot.
   Preserve build commands, input ID, output hashes, and symbols. Bootstrap
   then starts the registered frozen runner directly in `--frozen-run` mode.
   A failed check or changed input cannot proceed to measurement.
5. Run five-second profiler smoke captures at 64 and 4,096 hashes for each
   protocol/operation: eight captures. Confirm usable demangled symbols,
   expected worker stacks, the complete environment policy as observed inside
   the launched harness, and intact raw/XML/folded/SVG evidence. Check logs for
   the source-identified diagnostic messages, allowing Cargo/profiler progress
   output. If a smoke failure requires source or tooling changes, return to
   step 1 and refresh provenance before proceeding.
6. Allow the host to settle after builds, checks, and smoke captures; record
   the settling interval and load/power observations. Run the normal
   baseline-before and the symbol baseline under the shared environment policy.
   Warm-up is still performed by each benchmark as specified in section 3.
7. Run 30 seconds of repeated workload for all 28 primary selections,
   serially, and repeat the eight endpoint captures at full duration. The
   primary workload is about 14 minutes; repeats add four minutes, before
   preparation, export, and analysis overhead. Recheck provenance around every
   attempt and validate each capture before promoting its SVG.
8. Inspect sample counts, unknown/truncated stacks, and non-workload overhead.
   Aim for at least 10,000 usable sample rows per primary capture, distinguishing
   row counts from weighted CPU time. Extend low-sample captures in fresh
   attempts. Resolve poor symbols or substantial unrelated work before drawing
   conclusions. Record any residual limitation explicitly.
9. After the final capture/repeat/retry, run baseline-after from the prebuilt
   normal variant, with the same runtime policy and documented settling
   conditions. Check before/after drift as specified in section 3. Any required
   rebuild or source fix returns to the validation/provenance sequence; it
   cannot silently replace code within the same measurement series.
10. Validate the artifact inventory and write the report. Report-only edits
   can reuse unchanged evidence. No formatting, implementation fix, or compiler
   configuration change may retroactively describe old captures as new ones.

Required Rust tests use fake child executables and temporary directories;
they do not require profiling permissions:

- Build and launch with `CARGO_TARGET_DIR` containing spaces. Verify the
  runner/helpers come from that directory even if stale binaries exist under
  the default path; verify normal and symbol workload variants remain distinct.
- Pause a fake compiler just before it reads a source file. Change the editing
  checkout's file from A to B, allow the read, then restore A before compilation
  finishes. The accepted build must read A from the private copy. Passing only
  pre/post hashes of the editing checkout is insufficient. Also test a
  persistent editing-checkout change after freezing: it cannot alter the
  recorded snapshot or compiled bytes.
- Change an input during snapshot preparation and require a failed/retried
  candidate. Attempt writes to sealed source files/directories during checks
  and require failure; checks may only write to designated outputs. Reject
  symlink/path-dependency escapes into the editing checkout, and verify the
  source copy does not share hardlinks with it.
- Give the editing checkout a differing ancestor Cargo configuration. Verify
  final checks, explicit builds, and a fake cargo-flamegraph internal build
  use the private manifest, current directory, configuration, toolchain, and
  each operation's registered target directory; cargo-flamegraph must use the
  symbol directory. Verify the accepted runner/helpers were built
  from the snapshot and the bootstrap never supplies measurement results.
- For every key in `measurement-env.json`, exercise absent, empty, `0`, and
  `1` parent states, and a non-Unicode value on this Unix host. Test every
  command category, including both normal baselines, the symbol baseline,
  correctness runs, profiler wrappers, and repeats. All controlled keys must
  be absent in the actual child. Preserve unrelated variables and helper
  configuration. Configure subprocesses with `Command::env`; do not mutate
  process-global environment in concurrent tests.
- Make a fake recorder reintroduce a diagnostic key into the launched harness.
  Its environment validation must fail even when no diagnostic text has yet
  been printed. Confirm baseline symbol settings cannot leak from the parent.
- Exercise record/export exits 0, 1, and 54, SIGINT/SIGTERM termination,
  interruption after harness success, and copy/write failures. A fake profiler
  returning 0 and leaving an SVG cannot override failed/missing wrapper status.
  Check normalization to wrapper exit 1 and preservation of original status.
- Delete the working trace as upstream does and verify the archive survives.
  Reject identical/nested scratch/archive destinations. Check XML/folded bytes
  remain unchanged and child pipes cannot deadlock.
- Reject preexisting attempt directories, stale/mismatched metadata, and
  insufficient workload duration; give every retry a new directory.
- Reconstruct staged-plus-unstaged edits, staged new files, untracked source,
  binary changes, deletions, renames, executable modes, and paths containing
  spaces from the source snapshot. A detected change to a frozen embedded PCS
  TOML file or source must invalidate that series; editing the original
  checkout or generating a report cannot redefine the frozen build identity.
  Verify the user's Git index and source contents are unchanged by snapshot
  creation and validation.

## 6. Write the report and package the SVGs

Write the final artifacts under
`reports/performance/preimage-flamegraphs/<UTC-run-id>/`:

```text
report.md
index.html                         # local gallery, 7 rows × 4 SVG links
manifest.json                      # environment, commands, provenance
source/                            # snapshot/tree archive, patch, inputs.json, plan, path mapping
builds.json                        # executable identities for each build role
reference.csv
baseline-before.csv
baseline-after.csv
baseline-symbols.csv
hotspots.csv                        # inclusive/self weights and denominators
svg/flock-prove-0064.svg            # published only from a validated primary attempt
svg/full-zk-verify-4096.svg
cases/<case>/<attempt-id>/         # smoke/primary/repeat/retry evidence and status
```

Keep bulky raw traces in a companion archive if necessary; preserve an artifact
inventory and checksums. The manifest maps each of the 28 primary SVGs to its
validated source attempt and lists repeat and failed attempts separately.
Copy primary SVGs into `svg/` only after acceptance checks succeed. Deliver
the Markdown report and SVGs together with working relative links. The gallery
should work locally without a service.

The report must include:

1. Environment and methodology, historical versus fresh results, and any
   capture limitations or build-setting effects.
2. All seven rows of unprofiled timings and proof sizes, prove/verify ratios,
   randomized full-ZK size ranges, and size overhead calculated as
   `(full_zk_bytes / flock_bytes - 1) * 100`.
3. A seven-row table linking four SVGs per row; preview representative small
   and large cases and retain direct links to every SVG.
4. Top inclusive and self CPU hotspots for each case, with source locations
   and appropriate aggregation into field arithmetic, PCS/Merkle work,
   sumchecks, VEIL work, transcript/RNG, allocation, and scheduling where the
   measured stacks support those categories. Do not double-count nested
   inclusive frames as disjoint percentages.
5. Scaling observations and non-ZK/full-ZK differences supported by the
   captures, including repeat variability. CPU flamegraph widths show sampled
   CPU share across threads; they are not wall-clock latency percentages.
6. Ranked optimization candidates with evidence, expected mechanism, and a
   concrete follow-up experiment. Keep hypotheses distinct from measurements;
   this task does not implement optimizations or claim predicted speedups.

Preserve the table's interpretation: full-ZK batches of 64 and 128 pad to
256 slots, while non-ZK uses smaller circuits and ad hoc PCS schedules below
the registry floor. Proof sizes exclude witness commitments, public digests,
and bundle framing. Flamegraphs explain CPU work; the separately measured
serialized sizes establish size overhead.

## Completion criteria

- [ ] Work is on the recorded branch with a conventional prefix; existing
      changes and branches are preserved.
- [ ] No commit or push has occurred without explicit user approval for that
      action; the complete local results are ready for review.
- [ ] All 28 primary SVGs are present, nonempty, valid XML, and render correctly.
- [ ] Correct operation/size/protocol labels and actual worker stacks are checked.
- [ ] Baseline proofs and all verification calls succeed; profiling proof checks
      and loop overhead are disclosed accurately.
- [ ] Baselines, captures, and repeats use the same runtime-environment policy;
      custom Cargo target paths select the newly built Rust runner and helpers.
- [ ] All diagnostic keys and default-policy overrides are absent as required;
      the harness reports the actual environment, including through xctrace.
- [ ] Implementation checks passed before measurements; the uncommitted source
      snapshot existed before final checks/builds, reconstructs all build inputs,
      and was the actual source root used by final tools and profiler builds.
- [ ] Every accepted executable pairs successful frozen-source validation and
      build records with unchanged input identity; edit-and-restore races in
      the editing checkout cannot affect the compiled bytes.
- [ ] Every published capture has matching harness and wrapper success metadata;
      interrupted, partial, stale, or failed attempts cannot qualify.
- [ ] Archived traces survive recorder cleanup, and scratch/archive paths are
      distinct; smoke, primary, repeat, and retry attempts cannot overwrite each other.
- [ ] Raw evidence, folded stacks, repeat captures, build provenance, and exact
      reproduction commands are retained.
- [ ] The report links every SVG, includes measured hotspot analysis and fresh
      baselines, and distinguishes the published table from current results.
- [ ] No missing or unusable capture is presented as completed work.
