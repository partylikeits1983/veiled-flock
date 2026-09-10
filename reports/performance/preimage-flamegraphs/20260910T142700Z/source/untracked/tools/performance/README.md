# Preimage performance profiles

This local Rust workflow profiles the seven sizes in the README performance
table, with separate FLOCK/full-ZK prove/verify captures. It creates 28 primary
SVGs, eight endpoint repeats, fresh unprofiled CSV baselines, a report and a
local HTML gallery. The default workload is 30 seconds per capture; validation,
compilation, smoke recordings and export add time.

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
`incomplete.json` and logs. Fix source in the editing checkout and use a new run
directory; do not modify a frozen source tree or reuse failed evidence.

To regenerate only the report from completed evidence:

```sh
cargo run --locked --release -p flock-performance --bin profile_preimages -- \
  --report reports/performance/preimage-flamegraphs/20260910T150000Z
```

Open `index.html` locally or follow the relative links in `report.md`. Bulky
raw traces and debug artifacts can be packaged separately when sharing, while
retaining the artifact checksums and source-to-capture mapping.
