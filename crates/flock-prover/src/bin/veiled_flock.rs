//! Minimal end-to-end CLI for succinct experimental VEIL-FLOCK.

use std::{env, fs, process::ExitCode, time::Instant};

use flock_prover::{
    challenger::FsChallenger,
    pcs::Commitment,
    r1cs_hashes::blake3_preimage::{Blake3PreimageZkSetup, DIGEST_BYTES, MESSAGE_BYTES},
    succinct_veil::SuccinctVeilProof,
    zk::ZkRng,
};
use serde::{Deserialize, Serialize};

const DOMAIN: &[u8] = b"veiled-flock-cli-succinct-v0";
const MAGIC: [u8; 8] = *b"VFLK0003";

#[derive(Serialize, Deserialize)]
struct Bundle {
    magic: [u8; 8],
    digests: Vec<[u8; DIGEST_BYTES]>,
    commitment: Commitment,
    proof: SuccinctVeilProof,
}

const USAGE: &str = "\
veiled_flock — experimental ZK proof of a 64-byte BLAKE3 preimage

Usage:
  veiled_flock prove  --message FILE --out FILE
  veiled_flock verify --in FILE
  veiled_flock demo

The message file must contain one or more concatenated 64-byte messages. The
proof bundle contains their public BLAKE3 digests and the VEIL proof, but never
the messages.
";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}\n\n{USAGE}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    flock_prover::init_perf_thread_pool();
    eprintln!("EXPERIMENTAL: not independently audited; do not use for production secrets");
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
            let messages = bytes
                .chunks_exact(MESSAGE_BYTES)
                .map(|chunk| chunk.try_into().expect("checked chunk size"))
                .collect();
            let bundle = prove(messages)?;
            let encoded = bincode::serialize(&bundle)
                .map_err(|error| format!("cannot encode proof: {error}"))?;
            fs::write(&output, &encoded)
                .map_err(|error| format!("cannot write {output}: {error}"))?;
            eprintln!("wrote {} bytes to {output}", encoded.len());
            Ok(())
        }
        Some("verify") => {
            let parsed = parse_paths(args)?;
            let input = parsed.input.ok_or("verify: --in is required")?;
            let bytes =
                fs::read(&input).map_err(|error| format!("cannot read {input}: {error}"))?;
            let bundle: Bundle = bincode::deserialize(&bytes)
                .map_err(|error| format!("cannot decode proof bundle: {error}"))?;
            let canonical = bincode::serialize(&bundle)
                .map_err(|error| format!("cannot canonicalize proof bundle: {error}"))?;
            if canonical != bytes {
                return Err("non-canonical encoding or trailing bytes".to_string());
            }
            verify(&bundle)?;
            eprintln!("verified {input} ({} bytes)", bytes.len());
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
            let bytes = bincode::serialize(&bundle)
                .map_err(|error| format!("cannot encode proof: {error}"))?;
            eprintln!("demo complete: proof bundle is {} bytes", bytes.len());
            Ok(())
        }
        Some("help" | "--help" | "-h") => {
            print!("{USAGE}");
            Ok(())
        }
        Some(command) => Err(format!("unknown command '{command}'")),
        None => Err("missing command".to_string()),
    }
}

fn prove(messages: Vec<[u8; MESSAGE_BYTES]>) -> Result<Bundle, String> {
    let digests = messages
        .iter()
        .map(|message| *blake3::hash(message).as_bytes())
        .collect::<Vec<_>>();
    let setup = Blake3PreimageZkSetup::new_succinct(messages.len());
    let mut rng = ZkRng::from_entropy();
    let mut challenger = FsChallenger::new(DOMAIN);
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
        .map_err(|error| format!("proof generation failed: {error:?}"))?;
    eprintln!("proved in {:.3}s", started.elapsed().as_secs_f64());
    Ok(Bundle {
        magic: MAGIC,
        digests,
        commitment,
        proof,
    })
}

fn verify(bundle: &Bundle) -> Result<(), String> {
    if bundle.magic != MAGIC || bundle.digests.is_empty() {
        return Err("invalid bundle header or statement shape".to_string());
    }
    let setup = Blake3PreimageZkSetup::new_succinct(bundle.digests.len());
    let mut challenger = FsChallenger::new(DOMAIN);
    let started = Instant::now();
    setup
        .verify_succinct(
            &bundle.commitment,
            &bundle.proof,
            &bundle.digests,
            &mut challenger,
        )
        .map_err(|error| format!("verification failed: {error:?}"))?;
    eprintln!("verified in {:.3}s", started.elapsed().as_secs_f64());
    Ok(())
}

#[derive(Default)]
struct Paths {
    message: Option<String>,
    output: Option<String>,
    input: Option<String>,
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
            _ => return Err(format!("unknown flag '{flag}'")),
        }
    }
    Ok(paths)
}
