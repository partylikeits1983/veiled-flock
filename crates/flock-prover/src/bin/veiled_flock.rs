//! Minimal end-to-end CLI for succinct VEIL-FLOCK.

use std::{env, fs, io::Read, process::ExitCode, time::Instant};

use flock_prover::{
    proof_io::{MAX_VEIL_FLOCK_BUNDLE_BYTES, VeilFlockProofBundle},
    r1cs_hashes::blake3_preimage::{
        Blake3PreimageZkSetup, DIGEST_BYTES, MAX_ZK_PREIMAGE_BLOCKS, MESSAGE_BYTES,
    },
};

const MAX_MESSAGES: usize = MAX_ZK_PREIMAGE_BLOCKS;
const MAX_BUNDLE_BYTES: u64 = MAX_VEIL_FLOCK_BUNDLE_BYTES;
const DIGEST_HEX_BYTES: usize = DIGEST_BYTES * 2;
const MAX_DIGEST_FILE_BYTES: u64 = (MAX_MESSAGES * (DIGEST_HEX_BYTES + 2)) as u64;
type Bundle = VeilFlockProofBundle;
type Digest = [u8; DIGEST_BYTES];

fn usage() -> String {
    format!(
        "\
veiled_flock — succinct VEIL argument for 64-byte BLAKE3 preimages

Usage:
  veiled_flock prove  --message FILE --out FILE
  veiled_flock verify --in FILE --digests FILE
  veiled_flock demo

The message file must contain 1..={MAX_MESSAGES} concatenated 64-byte messages. The
proof bundle contains their public BLAKE3 digests and the VEIL proof, but never
the messages. The digest file must contain the expected public BLAKE3 digest list,
one 64-character hex digest per line.
"
    )
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            let usage = usage();
            eprintln!("error: {error}\n\n{usage}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    flock_prover::init_perf_thread_pool();
    eprintln!("UNAUDITED: not independently audited; do not use for production secrets");
    let mut args = env::args().skip(1);
    match args.next().as_deref() {
        Some("prove") => {
            let parsed = parse_paths(args)?;
            run_prove(parsed)
        }
        Some("verify") => {
            let parsed = parse_paths(args)?;
            run_verify(parsed)
        }
        Some("demo") => run_demo(args),
        Some("help" | "--help" | "-h") => {
            let usage = usage();
            print!("{usage}");
            Ok(())
        }
        Some(command) => Err(format!("unknown command '{command}'")),
        None => Err("missing command".to_string()),
    }
}

fn run_prove(paths: Paths) -> Result<(), String> {
    let message_path = paths.message.ok_or("prove: --message is required")?;
    let output = paths.output.ok_or("prove: --out is required")?;
    let bytes =
        fs::read(&message_path).map_err(|error| format!("cannot read {message_path}: {error}"))?;
    if bytes.is_empty() || !bytes.len().is_multiple_of(MESSAGE_BYTES) {
        return Err(format!(
            "message file must be a non-empty multiple of {MESSAGE_BYTES} bytes; got {}",
            bytes.len()
        ));
    }
    let messages = bytes.as_chunks::<MESSAGE_BYTES>().0.to_vec();
    let bundle = prove(messages)?;
    let encoded = encode_bundle(&bundle)?;
    fs::write(&output, &encoded).map_err(|error| format!("cannot write {output}: {error}"))?;
    eprintln!("wrote {} bytes to {output}", encoded.len());
    Ok(())
}

fn run_verify(paths: Paths) -> Result<(), String> {
    let input = paths.input.ok_or("verify: --in is required")?;
    let digest_path = paths.digests.ok_or("verify: --digests is required")?;
    let bytes = read_bundle(&input)?;
    let bundle = decode_bundle(&bytes)?;
    let expected_digests = read_digests(&digest_path)?;
    verify_expected_digests(&bundle.digests, &expected_digests)?;
    verify(&bundle)?;
    eprintln!("verified {input} ({} bytes)", bytes.len());
    print_digests(&bundle.digests);
    Ok(())
}

fn run_demo(mut args: impl Iterator<Item = String>) -> Result<(), String> {
    if args.next().is_some() {
        return Err("demo takes no arguments".to_string());
    }
    let messages = vec![
        std::array::from_fn(|index| index as u8),
        std::array::from_fn(|index| (255 - index) as u8),
    ];
    let bundle = prove(messages)?;
    verify(&bundle)?;
    let bytes = encode_bundle(&bundle)?;
    eprintln!("demo complete: proof bundle is {} bytes", bytes.len());
    Ok(())
}

fn prove(messages: Vec<[u8; MESSAGE_BYTES]>) -> Result<Bundle, String> {
    if messages.is_empty() || messages.len() > MAX_MESSAGES {
        return Err(format!("proofs support 1..={MAX_MESSAGES} messages"));
    }
    let digests = messages
        .iter()
        .map(|message| *blake3::hash(message).as_bytes())
        .collect::<Vec<_>>();
    let setup = Blake3PreimageZkSetup::new(messages.len());
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(&messages, &digests)
        .map_err(|error| format!("proof generation failed: {error:?}"))?;
    eprintln!("proved in {:.3}s", started.elapsed().as_secs_f64());
    Ok(Bundle::new(digests, commitment, proof))
}

fn verify(bundle: &Bundle) -> Result<(), String> {
    validate_digest_count(bundle.digests.len(), "bundle digest list")?;
    let setup = Blake3PreimageZkSetup::new(bundle.digests.len());
    let started = Instant::now();
    setup
        .verify(&bundle.commitment, &bundle.proof, &bundle.digests)
        .map_err(|error| format!("verification failed: {error:?}"))?;
    eprintln!("verified in {:.3}s", started.elapsed().as_secs_f64());
    Ok(())
}

fn read_bundle(path: &str) -> Result<Vec<u8>, String> {
    read_limited_file(path, MAX_BUNDLE_BYTES, "proof bundle")
}

fn encode_bundle(bundle: &Bundle) -> Result<Vec<u8>, String> {
    bundle
        .to_bytes()
        .map_err(|error| format!("cannot encode proof: {error}"))
}

fn decode_bundle(bytes: &[u8]) -> Result<Bundle, String> {
    ensure_size_limit(bytes.len(), MAX_BUNDLE_BYTES, "proof bundle")?;
    Bundle::from_bytes(bytes).map_err(|error| format!("cannot decode proof bundle: {error}"))
}

fn read_digests(path: &str) -> Result<Vec<Digest>, String> {
    let bytes = read_limited_file(path, MAX_DIGEST_FILE_BYTES, "digest file")?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|error| format!("digest file {path} is not UTF-8: {error}"))?;
    parse_digests_text(text)
}

fn read_limited_file(path: &str, limit: u64, label: &str) -> Result<Vec<u8>, String> {
    let file =
        fs::File::open(path).map_err(|error| format!("cannot read {label} {path}: {error}"))?;
    let mut bytes = Vec::new();
    file.take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {label} {path}: {error}"))?;
    ensure_size_limit(bytes.len(), limit, label)?;
    Ok(bytes)
}

fn ensure_size_limit(len: usize, limit: u64, label: &str) -> Result<(), String> {
    if len as u64 > limit {
        return Err(format!("{label} exceeds the {limit}-byte limit"));
    }
    Ok(())
}

fn parse_digests_text(text: &str) -> Result<Vec<Digest>, String> {
    let digests = text
        .split_whitespace()
        .enumerate()
        .map(|(index, token)| parse_digest_hex(index, token))
        .collect::<Result<Vec<_>, _>>()?;
    validate_digest_count(digests.len(), "digest file")?;
    Ok(digests)
}

fn validate_digest_count(count: usize, label: &str) -> Result<(), String> {
    if !(1..=MAX_MESSAGES).contains(&count) {
        return Err(format!("{label} must contain 1..={MAX_MESSAGES} digests"));
    }
    Ok(())
}

fn parse_digest_hex(index: usize, token: &str) -> Result<Digest, String> {
    let hex = token.as_bytes();
    if hex.len() != DIGEST_HEX_BYTES {
        return Err(format!(
            "digest {index} must be {DIGEST_HEX_BYTES} hex characters, got {}",
            token.len()
        ));
    }

    let mut digest = [0u8; DIGEST_BYTES];
    let (hex_bytes, remainder) = hex.as_chunks::<2>();
    debug_assert!(remainder.is_empty());
    for (byte, hex_byte) in digest.iter_mut().zip(hex_bytes) {
        *byte = parse_hex_byte(hex_byte).map_err(|error| format!("digest {index}: {error}"))?;
    }
    Ok(digest)
}

fn parse_hex_byte(hex: &[u8; 2]) -> Result<u8, String> {
    let high = hex_value(hex[0]).ok_or_else(|| invalid_hex_byte(hex))?;
    let low = hex_value(hex[1]).ok_or_else(|| invalid_hex_byte(hex))?;
    Ok((high << 4) | low)
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn invalid_hex_byte(hex: &[u8]) -> String {
    format!("invalid hex byte '{}'", String::from_utf8_lossy(hex))
}

fn verify_expected_digests(
    bundle_digests: &[Digest],
    expected_digests: &[Digest],
) -> Result<(), String> {
    if bundle_digests.len() != expected_digests.len() {
        return Err(format!(
            "bundle digest list does not match expected digest file: bundle has {}, expected {}",
            bundle_digests.len(),
            expected_digests.len()
        ));
    }
    if let Some(index) = bundle_digests
        .iter()
        .zip(expected_digests)
        .position(|(bundle_digest, expected_digest)| bundle_digest != expected_digest)
    {
        return Err(format!(
            "bundle digest {index} does not match expected digest file"
        ));
    }
    Ok(())
}

fn print_digests(digests: &[Digest]) {
    eprintln!("verified digests:");
    for digest in digests {
        eprintln!("{}", digest_hex(digest));
    }
}

fn digest_hex(digest: &Digest) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(DIGEST_HEX_BYTES);
    for byte in digest {
        write!(&mut out, "{byte:02x}").expect("write to string");
    }
    out
}

#[derive(Default)]
struct Paths {
    message: Option<String>,
    output: Option<String>,
    input: Option<String>,
    digests: Option<String>,
}

fn parse_paths(mut args: impl Iterator<Item = String>) -> Result<Paths, String> {
    let mut paths = Paths::default();
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("{flag} requires a path"))?;
        match flag.as_str() {
            "--message" => set_path(&mut paths.message, &flag, value)?,
            "--out" => set_path(&mut paths.output, &flag, value)?,
            "--in" => set_path(&mut paths.input, &flag, value)?,
            "--digests" => set_path(&mut paths.digests, &flag, value)?,
            _ => return Err(format!("unknown flag '{flag}'")),
        }
    }
    Ok(paths)
}

fn set_path(slot: &mut Option<String>, flag: &str, value: String) -> Result<(), String> {
    if slot.replace(value).is_some() {
        return Err(format!("{flag} was provided more than once"));
    }
    Ok(())
}

#[cfg(test)]
#[path = "veiled_flock/tests.rs"]
mod tests;
