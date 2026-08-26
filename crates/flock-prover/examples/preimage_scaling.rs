//! Reproducible release benchmark for the pinned BLAKE3-preimage relation.
//!
//! Compares the full-ZK VEIL-FLOCK protocol with the same non-ZK FLOCK
//! relation and Secure Ligerito profile. Setup construction and digest
//! generation are excluded from timings. One untimed warm-up precedes the
//! reported samples.

use std::time::{Duration, Instant};

use bincode::Options;
use flock_core::challenger::FsChallenger;
use flock_prover::{
    proof_io::{R1csProofBundleLigerito, VeilFlockProofBundle},
    r1cs_hashes::blake3_preimage::{Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES},
};
use serde::Serialize;

const SIZES: [usize; 4] = [256, 512, 1024, 2048];
const FLOCK_BENCHMARK_DOMAIN: &[u8] = b"flock-blake3-preimage-scaling";

#[derive(Clone, Copy)]
struct Sample {
    prove: Duration,
    verify: Duration,
    bundle_bytes: usize,
}

#[derive(Clone, Copy)]
struct ZkComponents {
    statement: u64,
    outer_commitment: u64,
    masked_piop: u64,
    masked_ring: u64,
    pcs: u64,
    veil: u64,
    freshness: u64,
}

#[derive(Clone, Copy)]
struct FlockComponents {
    commitment: u64,
    zerocheck: u64,
    lincheck: u64,
    pcs: u64,
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let argument = std::env::args().nth(1);
    if argument.as_deref() == Some("shapes") {
        for size in SIZES {
            let setup = Blake3PreimageZkSetup::new(size);
            println!(
                "hashes={size} slots={} m={} digest={}",
                setup.n_block_slots(),
                setup.r1cs.m,
                hex(&setup.r1cs.statement_digest())
            );
        }
        return;
    }
    let samples = argument
        .map(|value| {
            value
                .parse::<usize>()
                .expect("sample count must be an integer")
        })
        .unwrap_or(5);
    assert!(samples > 0, "sample count must be positive");

    println!(
        "hashes,protocol,prove_ms_median,verify_ms_median,bundle_bytes_median,bundle_bytes_min,bundle_bytes_max"
    );
    for size in SIZES {
        benchmark_size(size, samples);
    }
}

fn benchmark_size(size: usize, samples: usize) {
    let messages = messages(size);
    let digests = Blake3PreimageSetup::digests_of(&messages);

    let flock = Blake3PreimageSetup::new(size);
    let _ = sample_flock(&flock, &messages, &digests);
    let mut flock_samples = (0..samples)
        .map(|_| sample_flock(&flock, &messages, &digests))
        .collect::<Vec<_>>();
    let mut flock_timings = flock_samples
        .iter()
        .map(|(sample, _)| *sample)
        .collect::<Vec<_>>();
    print_samples(size, "FLOCK-non-ZK-Secure", &mut flock_timings);
    let flock_components = flock_samples.pop().expect("sample").1;
    eprintln!(
        "flock-components hashes={size} commitment={} zerocheck={} lincheck={} pcs={}",
        flock_components.commitment,
        flock_components.zerocheck,
        flock_components.lincheck,
        flock_components.pcs,
    );
    drop(flock);

    let zk = Blake3PreimageZkSetup::new(size);
    let piop = flock_prover::succinct_veil::certify_flock_piop_soundness(
        &zk.r1cs,
        zk.r1cs.csc_lincheck_circuit(),
    )
    .expect("supported FLOCK PIOP shape");
    let veil = flock_prover::succinct_veil::certify_shifted_veil_soundness(&zk.r1cs)
        .expect("supported VEIL constraint shape");
    let effective_m = zk.pcs_params.log_msg_len() + flock_core::pcs::LOG_PACKING;
    let config_source = flock_core::pcs::ligerito::embedded_security_config(
        effective_m,
        flock_core::pcs::ligerito::LigeritoProfile::Secure,
    )
    .expect("registered Secure profile");
    let config = flock_core::pcs::ligerito::LigeritoSecurityConfig::from_toml_str(config_source)
        .expect("valid Secure profile");
    let (prover_config, _) = config
        .to_prover_verifier_configs()
        .expect("executable Secure profile");
    eprintln!(
        "shape hashes={size} slots={} r1cs_m={} pcs_m={} masks={} l0_queries={} l0_padding={} query_bits={:?} fold_bits={:?} piop_bits={:.3} veil_bits={:.3} digest={}",
        zk.n_block_slots(),
        zk.r1cs.m,
        effective_m,
        flock_prover::succinct_veil::certify_global_masking(&zk.r1cs)
            .expect("supported masking shape")
            .visible_private_f128,
        prover_config.queries[0],
        (1usize << zk.pcs_params.witness_log_msg_len()) / zk.pcs_params.num_ntts(),
        prover_config.grinding_bits,
        prover_config.fold_grinding_bits,
        piop.bits(),
        veil.bits(),
        hex(&zk.r1cs.statement_digest())
    );
    let _ = sample_zk(&zk, &messages, &digests);
    let mut zk_samples = Vec::with_capacity(samples);
    let mut component_samples = Vec::with_capacity(samples);
    for _ in 0..samples {
        let (sample, measured_components) = sample_zk(&zk, &messages, &digests);
        zk_samples.push(sample);
        component_samples.push(measured_components);
    }
    print_samples(size, "VEIL-FLOCK-full-ZK", &mut zk_samples);
    let components = median_components(&component_samples);
    eprintln!(
        "components hashes={size} statement={} outer_commitment={} masked_piop={} masked_ring={} pcs={} veil={} freshness={}",
        components.statement,
        components.outer_commitment,
        components.masked_piop,
        components.masked_ring,
        components.pcs,
        components.veil,
        components.freshness,
    );
}

fn sample_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
) -> (Sample, FlockComponents) {
    let mut prover_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(messages, digests, &mut prover_challenger)
        .expect("non-ZK FLOCK proof generation");
    let prove = started.elapsed();

    let mut verifier_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests, &mut verifier_challenger)
        .expect("non-ZK FLOCK verification");
    let verify = started.elapsed();
    let components = FlockComponents {
        commitment: encoded_size(&commitment),
        zerocheck: encoded_size(&proof.zerocheck),
        lincheck: encoded_size(&proof.lincheck),
        pcs: encoded_size(&proof.pcs_open),
    };
    let bundle_bytes = R1csProofBundleLigerito { commitment, proof }
        .to_bytes()
        .len();
    (
        Sample {
            prove,
            verify,
            bundle_bytes,
        },
        components,
    )
}

fn sample_zk(
    setup: &Blake3PreimageZkSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
) -> (Sample, ZkComponents) {
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(messages, digests)
        .expect("full-ZK VEIL-FLOCK proof generation");
    let prove = started.elapsed();

    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests)
        .expect("full-ZK VEIL-FLOCK verification");
    let verify = started.elapsed();

    let components = ZkComponents {
        statement: encoded_size(&digests),
        outer_commitment: encoded_size(&commitment),
        masked_piop: encoded_size(&proof.masked_zerocheck) + encoded_size(&proof.masked_lincheck),
        masked_ring: encoded_size(&proof.masked_ring_claims)
            + encoded_size(&proof.public_direct_blind_values),
        pcs: encoded_size(&proof.pcs_open),
        veil: encoded_size(&proof.veil),
        freshness: encoded_size(&proof.proof_nonce)
            + encoded_size(&proof.tree_nonces)
            + encoded_size(&proof.blind_grind_nonce),
    };
    let bundle_bytes = VeilFlockProofBundle::new(digests.to_vec(), commitment, proof)
        .to_bytes()
        .expect("serialize full-ZK bundle")
        .len();
    (
        Sample {
            prove,
            verify,
            bundle_bytes,
        },
        components,
    )
}

fn print_samples(size: usize, protocol: &str, samples: &mut [Sample]) {
    samples.sort_unstable_by_key(|sample| sample.prove);
    let prove = samples[samples.len() / 2].prove.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.verify);
    let verify = samples[samples.len() / 2].verify.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.bundle_bytes);
    let median = samples[samples.len() / 2].bundle_bytes;
    println!(
        "{size},{protocol},{prove:.3},{verify:.3},{median},{},{}",
        samples.first().expect("sample").bundle_bytes,
        samples.last().expect("sample").bundle_bytes,
    );
}

fn encoded_size<T: Serialize>(value: &T) -> u64 {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .serialized_size(value)
        .expect("measure serialized component")
}

fn median_components(samples: &[ZkComponents]) -> ZkComponents {
    let median = |select: fn(&ZkComponents) -> u64| {
        let mut values = samples.iter().map(select).collect::<Vec<_>>();
        values.sort_unstable();
        values[values.len() / 2]
    };
    ZkComponents {
        statement: median(|value| value.statement),
        outer_commitment: median(|value| value.outer_commitment),
        masked_piop: median(|value| value.masked_piop),
        masked_ring: median(|value| value.masked_ring),
        pcs: median(|value| value.pcs),
        veil: median(|value| value.veil),
        freshness: median(|value| value.freshness),
    }
}

fn messages(size: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..size)
        .map(|message_index| {
            std::array::from_fn(|byte_index| {
                let word = (message_index as u64)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .rotate_left((byte_index % 64) as u32)
                    ^ byte_index as u64;
                word as u8
            })
        })
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
