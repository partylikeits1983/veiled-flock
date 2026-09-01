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
type Bundle = VeilFlockProofBundle;

fn usage() -> String {
    format!(
        "\
veiled_flock — succinct VEIL argument for 64-byte BLAKE3 preimages

Usage:
  veiled_flock prove  --message FILE --out FILE [--digest-out FILE]
  veiled_flock verify --in FILE --digests FILE
  veiled_flock demo

The message file must contain 1..={MAX_MESSAGES} concatenated 64-byte messages. The
proof bundle contains a transport copy of their public BLAKE3 digests and the
VEIL proof, but never the messages. Verification requires the expected digest
list as 64-character hex digests separated by whitespace.
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
            if let Some(digest_output) = parsed.digest_output {
                write_digest_list(&digest_output, &bundle.digests)?;
                eprintln!(
                    "wrote {} expected digest(s) to {digest_output}",
                    bundle.digests.len()
                );
            }
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
            let expected_digests = read_digest_list(&digest_path)?;
            let bytes = read_bundle(&input)?;
            let bundle = decode_bundle(&bytes)?;
            verify(&bundle, &expected_digests)?;
            eprintln!(
                "verified {input} ({} bytes) against {digest_path}",
                bytes.len()
            );
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
            verify(&bundle, &bundle.digests)?;
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

fn verify(bundle: &Bundle, expected_digests: &[[u8; 32]]) -> Result<(), String> {
    validate_expected_digests(&bundle.digests, expected_digests)?;
    let setup = Blake3PreimageZkSetup::new(expected_digests.len());
    let started = Instant::now();
    setup
        .verify(&bundle.commitment, &bundle.proof, expected_digests)
        .map_err(|error| format!("verification failed: {error:?}"))?;
    eprintln!("verified in {:.3}s", started.elapsed().as_secs_f64());
    Ok(())
}

fn validate_expected_digests(
    bundle_digests: &[[u8; 32]],
    expected_digests: &[[u8; 32]],
) -> Result<(), String> {
    if expected_digests.is_empty() || expected_digests.len() > MAX_MESSAGES {
        return Err("invalid expected statement shape".to_string());
    }
    if bundle_digests != expected_digests {
        return Err("bundle digest list does not match verifier statement".to_string());
    }
    Ok(())
}

fn write_digest_list(path: &str, digests: &[[u8; 32]]) -> Result<(), String> {
    fs::write(path, encode_digest_list(digests))
        .map_err(|error| format!("cannot write {path}: {error}"))
}

fn read_digest_list(path: &str) -> Result<Vec<[u8; 32]>, String> {
    let text = fs::read_to_string(path).map_err(|error| format!("cannot read {path}: {error}"))?;
    parse_digest_list(&text)
}

fn parse_digest_list(text: &str) -> Result<Vec<[u8; 32]>, String> {
    let mut digests = Vec::new();
    for (index, token) in text.split_whitespace().enumerate() {
        if token.len() != 2 * DIGEST_BYTES {
            return Err(format!(
                "digest {} must be {} hex characters",
                index + 1,
                2 * DIGEST_BYTES
            ));
        }
        let mut digest = [0u8; DIGEST_BYTES];
        let (pairs, []) = token.as_bytes().as_chunks::<2>() else {
            unreachable!("digest hex length was checked above");
        };
        for (byte, [hi_char, lo_char]) in digest.iter_mut().zip(pairs) {
            let hi = hex_nibble(*hi_char)
                .ok_or_else(|| format!("digest {} contains non-hex characters", index + 1))?;
            let lo = hex_nibble(*lo_char)
                .ok_or_else(|| format!("digest {} contains non-hex characters", index + 1))?;
            *byte = (hi << 4) | lo;
        }
        digests.push(digest);
        if digests.len() > MAX_MESSAGES {
            return Err(format!(
                "digest list supports at most {MAX_MESSAGES} digests"
            ));
        }
    }
    if digests.is_empty() {
        return Err("digest list is empty".to_string());
    }
    Ok(digests)
}

fn encode_digest_list(digests: &[[u8; 32]]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(digests.len() * (2 * DIGEST_BYTES + 1));
    for digest in digests {
        for byte in digest {
            out.push(HEX[(byte >> 4) as usize] as char);
            out.push(HEX[(byte & 0x0f) as usize] as char);
        }
        out.push('\n');
    }
    out
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
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

#[derive(Default)]
struct Paths {
    message: Option<String>,
    output: Option<String>,
    input: Option<String>,
    digests: Option<String>,
    digest_output: Option<String>,
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
            "--digest-out" => paths.digest_output = Some(value),
            _ => return Err(format!("unknown flag '{flag}'")),
        }
    }
    Ok(paths)
}

#[cfg(test)]
#[path = "veiled_flock/tests.rs"]
mod tests;
