//! Minimal end-to-end CLI for succinct VEIL-FLOCK.

use std::{env, fs, io::Read, process::ExitCode, time::Instant};

use flock_prover::{
    proof_io::{MAX_VEIL_FLOCK_BUNDLE_BYTES, VeilFlockProofBundle},
    r1cs_hashes::blake3_preimage::{
        Blake3PreimageZkSetup, DIGEST_BYTES, MAX_ZK_PREIMAGE_BLOCKS, MESSAGE_BYTES,
    },
};

const MAX_MESSAGES: usize = MAX_ZK_PREIMAGE_BLOCKS;
// Bound file reads and decoder allocation for untrusted proof bundles.
const MAX_BUNDLE_BYTES: u64 = MAX_VEIL_FLOCK_BUNDLE_BYTES;
const MAX_DIGEST_FILE_BYTES: u64 = (MAX_MESSAGES * (DIGEST_BYTES * 2 + 1)) as u64;
type Bundle = VeilFlockProofBundle;

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
            let message_path = parsed.message.ok_or("prove: --message is required")?;
            let output = parsed.output.ok_or("prove: --out is required")?;
            let bytes = fs::read(&message_path)
                .map_err(|error| format!("cannot read {message_path}: {error}"))?;
            if bytes.is_empty() || !bytes.len().is_multiple_of(MESSAGE_BYTES) {
                return Err(format!(
                    "message file must be a non-empty multiple of {MESSAGE_BYTES} bytes; got {}",
                    bytes.len()
                ));
            }
            let messages = bytes.as_chunks::<MESSAGE_BYTES>().0.to_vec();
            let bundle = prove(messages)?;
            let encoded = encode_bundle(&bundle)?;
            fs::write(&output, &encoded)
                .map_err(|error| format!("cannot write {output}: {error}"))?;
            eprintln!("wrote {} bytes to {output}", encoded.len());
            Ok(())
        }
        Some("verify") => {
            let parsed = parse_paths(args)?;
            let input = parsed.input.ok_or("verify: --in is required")?;
            let digest_path = parsed.digests.ok_or("verify: --digests is required")?;
            let bytes = read_bundle(&input)?;
            let bundle = decode_bundle(&bytes)?;
            let expected_digests = read_digests(&digest_path)?;
            verify_expected_digests(&bundle.digests, &expected_digests)?;
            verify(&bundle)?;
            eprintln!("verified {input} ({} bytes)", bytes.len());
            print_digests(&bundle.digests);
            Ok(())
        }
        Some("demo") => {
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
        Some("help" | "--help" | "-h") => {
            let usage = usage();
            print!("{usage}");
            Ok(())
        }
        Some(command) => Err(format!("unknown command '{command}'")),
        None => Err("missing command".to_string()),
    }
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
    if bundle.digests.is_empty() || bundle.digests.len() > MAX_MESSAGES {
        return Err("invalid bundle statement shape".to_string());
    }
    let setup = Blake3PreimageZkSetup::new(bundle.digests.len());
    let started = Instant::now();
    setup
        .verify(&bundle.commitment, &bundle.proof, &bundle.digests)
        .map_err(|error| format!("verification failed: {error:?}"))?;
    eprintln!("verified in {:.3}s", started.elapsed().as_secs_f64());
    Ok(())
}

fn read_bundle(path: &str) -> Result<Vec<u8>, String> {
    let file = fs::File::open(path).map_err(|error| format!("cannot read {path}: {error}"))?;
    let mut bytes = Vec::new();
    file.take(MAX_BUNDLE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {path}: {error}"))?;
    if bytes.len() as u64 > MAX_BUNDLE_BYTES {
        return Err(format!(
            "proof bundle exceeds the {MAX_BUNDLE_BYTES}-byte limit"
        ));
    }
    Ok(bytes)
}

fn encode_bundle(bundle: &Bundle) -> Result<Vec<u8>, String> {
    bundle
        .to_bytes()
        .map_err(|error| format!("cannot encode proof: {error}"))
}

fn decode_bundle(bytes: &[u8]) -> Result<Bundle, String> {
    if bytes.len() as u64 > MAX_BUNDLE_BYTES {
        return Err(format!(
            "proof bundle exceeds the {MAX_BUNDLE_BYTES}-byte limit"
        ));
    }
    Bundle::from_bytes(bytes).map_err(|error| format!("cannot decode proof bundle: {error}"))
}

fn read_digests(path: &str) -> Result<Vec<[u8; DIGEST_BYTES]>, String> {
    let file =
        fs::File::open(path).map_err(|error| format!("cannot read digest file {path}: {error}"))?;
    let mut bytes = Vec::new();
    file.take(MAX_DIGEST_FILE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read digest file {path}: {error}"))?;
    if bytes.len() as u64 > MAX_DIGEST_FILE_BYTES {
        return Err(format!(
            "digest file exceeds the {MAX_DIGEST_FILE_BYTES}-byte limit"
        ));
    }
    let text = std::str::from_utf8(&bytes)
        .map_err(|error| format!("digest file {path} is not UTF-8: {error}"))?;
    parse_digests_text(text)
}

fn parse_digests_text(text: &str) -> Result<Vec<[u8; DIGEST_BYTES]>, String> {
    let mut digests = Vec::new();
    for (index, token) in text.split_whitespace().enumerate() {
        if token.len() != DIGEST_BYTES * 2 {
            return Err(format!(
                "digest {} must be {} hex characters, got {}",
                index,
                DIGEST_BYTES * 2,
                token.len()
            ));
        }
        let mut digest = [0u8; DIGEST_BYTES];
        for byte_index in 0..DIGEST_BYTES {
            let start = byte_index * 2;
            digest[byte_index] = parse_hex_byte(&token[start..start + 2])
                .map_err(|error| format!("digest {index}: {error}"))?;
        }
        digests.push(digest);
    }
    if digests.is_empty() || digests.len() > MAX_MESSAGES {
        return Err(format!(
            "digest file must contain 1..={MAX_MESSAGES} digests"
        ));
    }
    Ok(digests)
}

fn parse_hex_byte(hex: &str) -> Result<u8, String> {
    u8::from_str_radix(hex, 16).map_err(|_| format!("invalid hex byte '{hex}'"))
}

fn verify_expected_digests(
    bundle_digests: &[[u8; DIGEST_BYTES]],
    expected_digests: &[[u8; DIGEST_BYTES]],
) -> Result<(), String> {
    if bundle_digests.len() != expected_digests.len() {
        return Err(format!(
            "bundle digest list does not match expected digest file: bundle has {}, expected {}",
            bundle_digests.len(),
            expected_digests.len()
        ));
    }
    for (index, (bundle_digest, expected_digest)) in
        bundle_digests.iter().zip(expected_digests).enumerate()
    {
        if bundle_digest != expected_digest {
            return Err(format!(
                "bundle digest {index} does not match expected digest file"
            ));
        }
    }
    Ok(())
}

fn print_digests(digests: &[[u8; DIGEST_BYTES]]) {
    eprintln!("verified digests:");
    for digest in digests {
        eprintln!("{}", digest_hex(digest));
    }
}

fn digest_hex(digest: &[u8; DIGEST_BYTES]) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(DIGEST_BYTES * 2);
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
            "--message" => paths.message = Some(value),
            "--out" => paths.output = Some(value),
            "--in" => paths.input = Some(value),
            "--digests" => paths.digests = Some(value),
            _ => return Err(format!("unknown flag '{flag}'")),
        }
    }
    Ok(paths)
}

#[cfg(test)]
#[path = "veiled_flock/tests.rs"]
mod tests;
