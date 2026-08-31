use std::{
    env,
    ffi::{OsStr, OsString},
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, ExitStatus, Stdio},
    thread,
    time::Instant,
};

const CORE_FEATURES: &[&str] = &["zk", "symbolic"];
const PROVER_FEATURES: &[&str] = &["veil"];
const NO_FEATURES: &[&str] = &[];
const DIRECT_SHA256_NEEDLES: &[&str] = &[
    "use sha2::",
    "sha2::compress",
    "Sha256::digest",
    "Sha256::new",
];
const SUPERSEDED_ZK_SURFACE_NEEDLES: &[&str] =
    &["R1csProofZkA1", "prove_r1cs_zk_a1", "verify_r1cs_zk_a1"];

const CERTIFICATES: &[Certificate] = &[
    // Framed random oracle, tree nonces/channels, and SIMD parity.
    core_lib("ro::tests::native_tree_hasher_matches_one_shot_reference"),
    core_lib("ro::tests::external_backend_reproduces_native_digests_and_records"),
    core_lib("merkle::tests::tree_root_separates_nonce_channel_depth_level_index"),
    core_lib("merkle::tests::external_framed_tree_matches_native_and_records_every_node"),
    core_lib("merkle::tests::framed_midstate_simd_matches_scalar_all_tail_shapes"),
    // Hiding PCS commitments, L0 masking, and Ligerito full-ZK grinding ledger.
    core_lib("pcs::commit::tests::commit_zk_matches_wide_oracle"),
    core_lib("pcs::tests::zk_field_mask_hiding_open_roundtrip"),
    core_lib("pcs::zk_audit::pcs_rank_audit_witness_image_covered"),
    core_lib("pcs::zk_audit::pcs_rank_audit_negative_control_without_g"),
    core_lib("pcs::ligerito::fold_grind_taper_tests::secure_aggregate_bits_are_pinned"),
    core_lib(
        "pcs::ligerito::fold_grind_taper_tests::secure_nonce_count_matches_the_ledger_fold_count",
    ),
    core_lib(
        "pcs::ligerito::fold_grind_taper_tests::udr_level_grinds_every_fold_round_at_full_width",
    ),
    core_lib("pcs::ligerito::fold_grind_taper_tests::zk_l0_ledger_charges_the_c_combination"),
    core_lib("pcs::ligerito::fold_grind_taper_tests::zk_l0_ledger_rejects_a_johnson_level"),
    core_lib("pcs::ligerito::tests::secure_profile_reports_additive_whole_opening_soundness"),
    core_lib("r1cs::tests::statement_digest_binds_zk_layout"),
    core_lib("zerocheck::tests::prove_verify_zk_roundtrip_honest"),
    core_lib("zerocheck::tests::verify_zk_rejects_mutations"),
    core_lib("zerocheck::tests::zk_gamma_cancellation_unique_and_fs_ordering"),
    // Symbolic kernels, mask coverage, and the closed-form PCS translator.
    core_test(
        "symbolic_kernels",
        "concrete_symbolic_kernels_match_native_references",
    ),
    core_test(
        "symbolic_kernels",
        "toy_exact_polynomials_match_evaluation_and_degree_semantics",
    ),
    core_test(
        "symbolic_kernels",
        "challenge_dependent_inversion_is_not_part_of_sym_scalar",
    ),
    core_test(
        "symbolic_mask_coverage",
        "symbolic_mask_matrix_matches_native_and_has_100_bit_margin",
    ),
    core_test(
        "symbolic_pcs_translator",
        "closed_form_translation_preserves_open_rows_and_combined_vector",
    ),
    core_test(
        "symbolic_pcs_translator",
        "structural_l0_rank_certificate_matches_actual_ntt_on_every_small_query_set",
    ),
    core_test(
        "symbolic_pcs_translator",
        "l0_entropy_counting_gate_holds_for_fixture_and_production",
    ),
    // VEIL F128 code, ZK dot/Hadamard proofs, and shifted constraint certificates.
    veil_lib("code::tests::zk_certificate_uses_exact_operand_and_product_dimensions"),
    veil_lib("code::tests::product_code_is_multiplicative_and_reduces_pointwise"),
    veil_lib("code::tests::hadamard_reduction_identity_holds_on_every_basis_pair"),
    veil_lib("code::tests::square_encoder_rejects_the_extra_highest_degree_coefficient"),
    veil_lib("code::tests::every_two_queries_are_masked_by_two_padding_symbols_in_tiny_code"),
    veil_lib("commitment::tests::multi_opening_roundtrip_and_mutation_rejection"),
    veil_lib("constraints::tests::shifted_circuit_proves_and_verifies"),
    veil_lib("constraints::tests::linear_only_circuit_roundtrip"),
    veil_lib("constraints::tests::unsatisfied_shifted_circuit_is_not_provable"),
    veil_lib("constraints::tests::succinct_flock_profile_has_a_concrete_additive_soundness_bound"),
    veil_lib("constraints::tests::succinct_soundness_certificate_rejects_an_underqueried_profile"),
    veil_lib("dot_product::tests::dot_product_proof_roundtrip"),
    veil_lib("dot_product::tests::dot_product_proof_rejects_claim_and_opening_mutations"),
    veil_lib("hadamard::tests::hadamard_and_dot_roundtrip"),
    veil_lib("hadamard::tests::false_hadamard_relation_is_rejected"),
    veil_lib("hadamard::tests::opening_mutation_is_rejected"),
    // Full-ZK public relation, transcript binding, simulator, and proof bundle.
    prover_lib("digest_bind::tests::padding_rule_is_bound"),
    prover_lib("digest_bind::tests::reordering_changes_statement_and_target"),
    prover_lib("digest_bind::tests::distinct_digest_lists_give_distinct_targets"),
    prover_lib("preimage_extractor::tests::recorded_leaf_queries_reconstruct_committed_message"),
    prover_lib("sim_game::tests::active_bound_composes_across_proofs"),
    prover_lib("sim_oracle::tests::oracle_pow_state_digest_is_an_oracle_query"),
    prover_lib("sim_oracle::tests::programming_forces_the_next_challenge"),
    prover_lib("sim_oracle::tests::reprogramming_a_queried_point_is_refused"),
    prover_lib(
        "succinct_veil::tests::production_entry_point_is_pinned_to_the_certified_relation_and_secure_pcs",
    ),
    prover_lib(
        "succinct_veil::tests::every_registered_batch_shape_has_checked_mask_and_soundness_parameters",
    ),
    prover_lib(
        "succinct_veil::tests::production_mask_layout_matches_every_visible_private_coordinate",
    ),
    prover_lib("succinct_veil::tests::l0_hiding_budget_fails_closed_above_the_mask_dimension"),
    prover_lib("succinct_veil::tests::ring_constraint_map_matches_packed_field_scaling"),
    prover_lib(
        "succinct_veil::tests::simulator_sumcheck_solve_preserves_uniform_zero_and_one_challenges",
    ),
    prover_lib("succinct_veil::tests::succinct_shape_rejects_nonidentity_c"),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::largest_supported_zk_shape_grinds_every_udr_fold_round",
    ),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::zk_setup_rejects_batches_above_current_certificate_ceiling",
    ),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::succinct_veil_preimage_roundtrip_and_mutations",
    ),
    prover_lib("r1cs_hashes::blake3_preimage::tests::succinct_ring_messages_use_fresh_masks"),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::succinct_veil_public_only_simulator_is_accepted",
    ),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::succinct_simulator_composes_on_one_shared_oracle",
    ),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::succinct_simulator_query_cap_covers_every_registered_shape",
    ),
    prover_lib(
        "r1cs_hashes::blake3_preimage::tests::succinct_simulator_aborts_on_a_prequeried_programming_point",
    ),
    prover_lib("r1cs_hashes::blake3_preimage::tests::wrong_preimage_refused_by_prover"),
    prover_lib("r1cs_hashes::blake3_preimage::tests::reordered_digests_rejected"),
    prover_lib("r1cs_hashes::blake3_preimage::tests::proof_for_other_digests_does_not_transfer"),
    prover_lib("proof_io::tests::veil_bincode_limit_leaves_room_for_header"),
    prover_bin(
        "veiled_flock",
        "tests::decoder_rejects_an_unbounded_digest_vector",
    ),
    prover_bin("veiled_flock", "tests::decoder_rejects_bare_legacy_bincode"),
    prover_bin("veiled_flock", "tests::decoder_rejects_oversized_input"),
];

#[derive(Clone, Copy)]
struct Certificate {
    package: &'static str,
    features: &'static [&'static str],
    target: Target,
    name: &'static str,
}

#[derive(Clone, Copy)]
enum Target {
    Lib,
    Test(&'static str),
    Bin(&'static str),
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RowStatus {
    Ok,
    Failed,
    Vacuous,
}

struct ManifestRow {
    label: String,
    status: RowStatus,
    seconds: u64,
}

struct Manifest {
    rows: Vec<ManifestRow>,
    path: Option<PathBuf>,
}

struct Args {
    manifest_path: Option<PathBuf>,
}

enum ParsedArgs {
    Run(Args),
    Help,
}

struct Finding {
    path: PathBuf,
    line_number: usize,
    line: String,
}

enum Stream {
    Stdout,
    Stderr,
}

const fn core_lib(name: &'static str) -> Certificate {
    Certificate {
        package: "flock-core",
        features: CORE_FEATURES,
        target: Target::Lib,
        name,
    }
}

const fn core_test(target_name: &'static str, name: &'static str) -> Certificate {
    Certificate {
        package: "flock-core",
        features: CORE_FEATURES,
        target: Target::Test(target_name),
        name,
    }
}

const fn veil_lib(name: &'static str) -> Certificate {
    Certificate {
        package: "veil-f128",
        features: NO_FEATURES,
        target: Target::Lib,
        name,
    }
}

const fn prover_lib(name: &'static str) -> Certificate {
    Certificate {
        package: "flock-prover",
        features: PROVER_FEATURES,
        target: Target::Lib,
        name,
    }
}

const fn prover_bin(target_name: &'static str, name: &'static str) -> Certificate {
    Certificate {
        package: "flock-prover",
        features: PROVER_FEATURES,
        target: Target::Bin(target_name),
        name,
    }
}

impl Args {
    fn parse<I>(mut args: I) -> Result<ParsedArgs, String>
    where
        I: Iterator<Item = OsString>,
    {
        let mut manifest_path = None;
        while let Some(arg) = args.next() {
            if arg == "--manifest" {
                let path = args
                    .next()
                    .ok_or_else(|| "missing path after --manifest".to_owned())?;
                manifest_path = Some(PathBuf::from(path));
            } else if arg == "--help" || arg == "-h" {
                return Ok(ParsedArgs::Help);
            } else {
                return Err(format!(
                    "unknown argument '{}'\n{}",
                    arg.to_string_lossy(),
                    Self::usage()
                ));
            }
        }
        Ok(ParsedArgs::Run(Self { manifest_path }))
    }

    fn usage() -> &'static str {
        "usage: cargo run --locked --release -p zk-certify -- [--manifest PATH]"
    }
}

impl Certificate {
    fn label(self) -> String {
        match self.target {
            Target::Lib => format!("{}::--lib::{}", self.package, self.name),
            Target::Test(target_name) => {
                format!("{}::--test:{}::{}", self.package, target_name, self.name)
            }
            Target::Bin(target_name) => {
                format!("{}::--bin:{}::{}", self.package, target_name, self.name)
            }
        }
    }

    fn cargo_args(self) -> Vec<String> {
        let mut args = vec![
            "test".to_owned(),
            "--locked".to_owned(),
            "--release".to_owned(),
            "-p".to_owned(),
            self.package.to_owned(),
        ];

        if !self.features.is_empty() {
            args.push("--features".to_owned());
            args.push(self.features.join(","));
        }

        match self.target {
            Target::Lib => args.push("--lib".to_owned()),
            Target::Test(target_name) => {
                args.push("--test".to_owned());
                args.push(target_name.to_owned());
            }
            Target::Bin(target_name) => {
                args.push("--bin".to_owned());
                args.push(target_name.to_owned());
            }
        }

        args.extend([
            self.name.to_owned(),
            "--".to_owned(),
            "--include-ignored".to_owned(),
            "--exact".to_owned(),
            "--nocapture".to_owned(),
        ]);
        args
    }
}

impl RowStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Failed => "FAILED",
            Self::Vacuous => "VACUOUS",
        }
    }
}

impl ManifestRow {
    fn ok(label: impl Into<String>, seconds: u64) -> Self {
        Self {
            label: label.into(),
            status: RowStatus::Ok,
            seconds,
        }
    }

    fn failed(label: impl Into<String>, seconds: u64) -> Self {
        Self {
            label: label.into(),
            status: RowStatus::Failed,
            seconds,
        }
    }

    fn vacuous(label: impl Into<String>, seconds: u64) -> Self {
        Self {
            label: label.into(),
            status: RowStatus::Vacuous,
            seconds,
        }
    }

    fn is_ok(&self) -> bool {
        self.status == RowStatus::Ok
    }

    fn render(&self) -> String {
        format!(
            "{} {} {}s\n",
            self.label,
            self.status.as_str(),
            self.seconds
        )
    }
}

impl Manifest {
    fn new(path: Option<PathBuf>) -> Self {
        Self {
            rows: Vec::new(),
            path,
        }
    }

    fn push(&mut self, row: ManifestRow) {
        self.rows.push(row);
    }

    fn render(&self) -> String {
        self.rows.iter().map(ManifestRow::render).collect()
    }

    fn print(&self, complete: bool) {
        if complete {
            println!("\n=== manifest ===");
        } else {
            println!("\n=== manifest (INCOMPLETE, status 1) ===");
        }
        print!("{}", self.render());
    }

    fn write(&self) -> Result<(), String> {
        if let Some(path) = &self.path {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|err| {
                    format!(
                        "failed to create manifest directory '{}': {err}",
                        parent.display()
                    )
                })?;
            }
            fs::write(path, self.render())
                .map_err(|err| format!("failed to write manifest '{}': {err}", path.display()))?;
        }
        Ok(())
    }
}

fn main() -> ExitCode {
    let args = match Args::parse(env::args_os().skip(1)) {
        Ok(ParsedArgs::Run(args)) => args,
        Ok(ParsedArgs::Help) => {
            println!("{}", Args::usage());
            return ExitCode::SUCCESS;
        }
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        }
    };

    match run(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}

fn run(args: Args) -> Result<(), ()> {
    let root = workspace_root();
    let manifest_path = args
        .manifest_path
        .map(|path| absolutize_manifest_path(&root, path));
    let mut manifest = Manifest::new(manifest_path);

    for certificate in CERTIFICATES {
        let row = run_one_certificate(&root, *certificate);
        let ok = row.is_ok();
        manifest.push(row);
        if !ok {
            manifest.print(false);
            write_manifest_or_report(&manifest);
            return Err(());
        }
    }

    for (label, check) in SOURCE_CHECKS {
        let row = run_source_check(&root, label, *check);
        let ok = row.is_ok();
        manifest.push(row);
        if !ok {
            manifest.print(false);
            write_manifest_or_report(&manifest);
            return Err(());
        }
    }

    manifest.print(true);
    if let Err(message) = manifest.write() {
        eprintln!("ERROR: {message}");
        return Err(());
    }
    Ok(())
}

type SourceCheck = fn(&Path) -> Result<(), String>;

const SOURCE_CHECKS: &[(&str, SourceCheck)] = &[
    (
        "source::no-direct-sha256-outside-reviewed-random-oracle",
        check_no_direct_sha256,
    ),
    (
        "source::no-superseded-zk-surface",
        check_no_superseded_zk_surface,
    ),
    (
        "source::no-tracked-shell-scripts",
        check_no_tracked_shell_scripts,
    ),
];

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("zk-certify crate lives two levels below the workspace root")
        .to_path_buf()
}

fn absolutize_manifest_path(root: &Path, path: PathBuf) -> PathBuf {
    if path.is_absolute() {
        path
    } else {
        root.join(path)
    }
}

fn write_manifest_or_report(manifest: &Manifest) {
    if let Err(message) = manifest.write() {
        eprintln!("ERROR: {message}");
    }
}

fn run_one_certificate(root: &Path, certificate: Certificate) -> ManifestRow {
    let label = certificate.label();
    let args = certificate.cargo_args();
    println!("=== {label} ===");

    let started = Instant::now();
    match spawn_and_tee(root, &args) {
        Ok((status, stdout)) => {
            let seconds = started.elapsed().as_secs();
            if !status.success() {
                eprintln!(
                    "ERROR: '{label}' failed with {}",
                    status_description(status)
                );
                return ManifestRow::failed(label, seconds);
            }

            let passed = last_passed_count(&stdout);
            if passed < 1 {
                eprintln!("ERROR: '{}' matched no tests", certificate.name);
                return ManifestRow::vacuous(label, seconds);
            }

            ManifestRow::ok(label, seconds)
        }
        Err(message) => {
            eprintln!("ERROR: {message}");
            ManifestRow::failed(label, started.elapsed().as_secs())
        }
    }
}

fn spawn_and_tee(root: &Path, args: &[String]) -> Result<(ExitStatus, Vec<u8>), String> {
    let mut child = Command::new("cargo")
        .args(args)
        .current_dir(root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|err| format!("failed to spawn cargo {}: {err}", args.join(" ")))?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "failed to capture cargo stdout".to_owned())?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| "failed to capture cargo stderr".to_owned())?;

    let stdout_thread = thread::spawn(move || tee_pipe(stdout, Stream::Stdout));
    let stderr_thread = thread::spawn(move || tee_pipe(stderr, Stream::Stderr));

    let status = child
        .wait()
        .map_err(|err| format!("failed to wait for cargo {}: {err}", args.join(" ")))?;
    let stdout = join_reader(stdout_thread, "stdout")?;
    let _stderr = join_reader(stderr_thread, "stderr")?;
    Ok((status, stdout))
}

fn tee_pipe<R: Read>(reader: R, stream: Stream) -> io::Result<Vec<u8>> {
    match stream {
        Stream::Stdout => {
            let mut stdout = io::stdout().lock();
            tee_to(reader, &mut stdout)
        }
        Stream::Stderr => {
            let mut stderr = io::stderr().lock();
            tee_to(reader, &mut stderr)
        }
    }
}

fn tee_to<R: Read, W: Write>(mut reader: R, writer: &mut W) -> io::Result<Vec<u8>> {
    let mut collected = Vec::new();
    let mut buf = [0_u8; 8192];
    loop {
        let read = reader.read(&mut buf)?;
        if read == 0 {
            break;
        }
        writer.write_all(&buf[..read])?;
        writer.flush()?;
        collected.extend_from_slice(&buf[..read]);
    }
    Ok(collected)
}

fn join_reader(
    handle: thread::JoinHandle<io::Result<Vec<u8>>>,
    stream: &str,
) -> Result<Vec<u8>, String> {
    handle
        .join()
        .map_err(|_| format!("cargo {stream} reader panicked"))?
        .map_err(|err| format!("failed to read cargo {stream}: {err}"))
}

fn status_description(status: ExitStatus) -> String {
    status
        .code()
        .map_or_else(|| "signal".to_owned(), |code| format!("exit status {code}"))
}

fn last_passed_count(output: &[u8]) -> u64 {
    let text = String::from_utf8_lossy(output);
    let mut search_from = 0;
    let mut last = 0;
    while let Some(relative) = text[search_from..].find(" passed") {
        let end = search_from + relative;
        let start = text[..end]
            .rfind(|ch: char| !ch.is_ascii_digit())
            .map_or(0, |index| index + 1);
        if start < end
            && let Ok(count) = text[start..end].parse::<u64>()
        {
            last = count;
        }
        search_from = end + " passed".len();
    }
    last
}

fn run_source_check(root: &Path, label: &str, check: SourceCheck) -> ManifestRow {
    println!("=== {label} ===");
    let started = Instant::now();
    match check(root) {
        Ok(()) => ManifestRow::ok(label, started.elapsed().as_secs()),
        Err(message) => {
            eprintln!("ERROR: {message}");
            ManifestRow::failed(label, started.elapsed().as_secs())
        }
    }
}

fn check_no_direct_sha256(root: &Path) -> Result<(), String> {
    let mut findings = Vec::new();
    for rel in ["crates/flock-core/src", "crates/flock-prover/src"] {
        let dir = root.join(rel);
        scan_files(
            &dir,
            &mut |path| path.extension() == Some(OsStr::new("rs")),
            &mut |path, line_number, line| {
                let rel_path = relative_path(root, path);
                if rel_path == Path::new("crates/flock-core/src/ro.rs")
                    || rel_path == Path::new("crates/flock-core/src/challenger.rs")
                {
                    return;
                }

                if DIRECT_SHA256_NEEDLES
                    .iter()
                    .any(|needle| line.contains(needle))
                {
                    findings.push(Finding {
                        path: rel_path.to_path_buf(),
                        line_number,
                        line: line.to_owned(),
                    });
                }
            },
        )?;
    }

    report_findings(findings, "direct SHA-256 call outside ro.rs/challenger.rs")
}

fn check_no_superseded_zk_surface(root: &Path) -> Result<(), String> {
    let mut findings = Vec::new();
    for rel in ["crates", "docs", "SPEC.md", "README.md"] {
        let path = root.join(rel);
        scan_files(&path, &mut |_| true, &mut |path, line_number, line| {
            let rel_path = relative_path(root, path);
            if rel_path.starts_with(Path::new("tools/zk-certify")) {
                return;
            }

            if contains_superseded_zk_surface(line) {
                findings.push(Finding {
                    path: rel_path.to_path_buf(),
                    line_number,
                    line: line.to_owned(),
                });
            }
        })?;
    }

    report_findings(findings, "superseded or versioned ZK surface found")
}

fn check_no_tracked_shell_scripts(root: &Path) -> Result<(), String> {
    let output = Command::new("git")
        .args(["ls-files", "*.sh"])
        .current_dir(root)
        .output()
        .map_err(|err| format!("failed to enumerate tracked shell scripts: {err}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "failed to enumerate tracked shell scripts: {stderr}"
        ));
    }

    let scripts = String::from_utf8_lossy(&output.stdout);
    if scripts.trim().is_empty() {
        Ok(())
    } else {
        print!("{scripts}");
        Err("tracked shell scripts found".to_owned())
    }
}

fn scan_files<F, G>(path: &Path, include: &mut F, visit: &mut G) -> Result<(), String>
where
    F: FnMut(&Path) -> bool,
    G: FnMut(&Path, usize, &str),
{
    if path.is_dir() {
        let mut entries = fs::read_dir(path)
            .map_err(|err| format!("failed to read directory '{}': {err}", path.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| {
                format!(
                    "failed to read directory entry in '{}': {err}",
                    path.display()
                )
            })?;
        entries.sort_by_key(|entry| entry.path());

        for entry in entries {
            scan_files(&entry.path(), include, visit)?;
        }
        return Ok(());
    }

    if !path.is_file() || !include(path) {
        return Ok(());
    }

    let contents = match fs::read_to_string(path) {
        Ok(contents) => contents,
        Err(err) if err.kind() == io::ErrorKind::InvalidData => return Ok(()),
        Err(err) => return Err(format!("failed to read '{}': {err}", path.display())),
    };

    for (index, line) in contents.lines().enumerate() {
        visit(path, index + 1, line);
    }
    Ok(())
}

fn report_findings(findings: Vec<Finding>, message: &str) -> Result<(), String> {
    if findings.is_empty() {
        return Ok(());
    }

    for finding in findings {
        println!(
            "{}:{}:{}",
            finding.path.display(),
            finding.line_number,
            finding.line
        );
    }
    Err(message.to_owned())
}

fn relative_path<'a>(root: &'a Path, path: &'a Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

fn contains_superseded_zk_surface(line: &str) -> bool {
    SUPERSEDED_ZK_SURFACE_NEEDLES
        .iter()
        .any(|needle| line.contains(needle))
        || contains_versioned_veil_flock_domain(line)
}

fn contains_versioned_veil_flock_domain(line: &str) -> bool {
    let needle = "veil-flock";
    let mut search_from = 0;
    while let Some(relative) = line[search_from..].find(needle) {
        let tail_start = search_from + relative + needle.len();
        let tail = &line[tail_start..];
        let tail_end = tail.find(['"', ' ']).unwrap_or(tail.len());
        if contains_dash_v_digit(&tail[..tail_end]) {
            return true;
        }
        search_from = tail_start;
    }
    false
}

fn contains_dash_v_digit(text: &str) -> bool {
    text.as_bytes()
        .windows(3)
        .any(|window| window[0] == b'-' && window[1] == b'v' && window[2].is_ascii_digit())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_treats_help_as_successful_mode() {
        match Args::parse([OsString::from("--help")].into_iter()) {
            Ok(ParsedArgs::Help) => {}
            _ => panic!("expected help mode"),
        }
    }

    #[test]
    fn parser_accepts_manifest_path() {
        match Args::parse(
            [
                OsString::from("--manifest"),
                OsString::from("target/manifest"),
            ]
            .into_iter(),
        ) {
            Ok(ParsedArgs::Run(args)) => {
                assert_eq!(args.manifest_path, Some(PathBuf::from("target/manifest")));
            }
            _ => panic!("expected runnable args"),
        }
    }

    #[test]
    fn parser_rejects_unknown_args() {
        match Args::parse([OsString::from("--unknown")].into_iter()) {
            Err(message) => assert!(message.contains("unknown argument")),
            Ok(_) => panic!("expected parse error"),
        }
    }

    #[test]
    fn passed_count_uses_the_last_reported_test_result() {
        let output = b"test result: ok. 0 passed; 0 failed\ntest result: ok. 3 passed; 0 failed\n";

        assert_eq!(last_passed_count(output), 3);
    }

    #[test]
    fn superseded_surface_detects_legacy_and_versioned_names() {
        assert!(contains_superseded_zk_surface("pub struct R1csProofZkA1;"));
        assert!(contains_superseded_zk_surface("\"veil-flock-v1\""));
        assert!(!contains_superseded_zk_surface("\"veil-flock\""));
    }
}
