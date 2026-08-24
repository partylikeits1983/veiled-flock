//! Apples-to-apples benchmark for `BLAKE3(message[i]) = digest[i]`.
//!
//! The default batch is 256, where ordinary FLOCK and VEIL+FLOCK use the
//! same padded R1CS shape (`m = 22`).  In addition to median/MAD timings, the
//! benchmark serializes every top-level proof field separately so the size
//! overhead is attributable to the hiding witness PCS or the inner VEIL
//! certificate instead of being reported as one opaque ratio.

use std::{hint::black_box, time::Instant};

use flock_core::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::{
    Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES,
};
use serde::Serialize;

const FLOCK_DOMAIN: &[u8] = b"veil-vs-flock-benchmark-flock-v1";
const VEIL_DOMAIN: &[u8] = b"veil-vs-flock-benchmark-veil-v1";

#[derive(Clone, Copy, Debug, Serialize)]
struct Timing {
    median_seconds: f64,
    mad_seconds: f64,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct ModeTiming {
    prove: Timing,
    verify: Timing,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct FlockSizes {
    total_bytes: usize,
    commitment_bytes: usize,
    zerocheck_bytes: usize,
    lincheck_bytes: usize,
    witness_pcs_bytes: usize,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct VeilSizes {
    total_bytes: usize,
    commitment_bytes: usize,
    masked_zerocheck_bytes: usize,
    masked_lincheck_bytes: usize,
    nonce_and_output_claim_bytes: usize,
    hiding_witness_pcs_bytes: usize,
    veil_hadamard_bytes: usize,
    veil_linear_bytes: usize,
    veil_metadata_bytes: usize,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct PcsGeometry {
    committed_message_log: usize,
    merkle_leaves: usize,
    leaf_bytes: usize,
    committed_f128: usize,
}

#[derive(Debug, Serialize)]
struct Report {
    relation: &'static str,
    batch: usize,
    padded_slots: usize,
    runs: usize,
    flock_timing: ModeTiming,
    veil_timing: ModeTiming,
    flock_sizes: FlockSizes,
    veil_sizes: VeilSizes,
    flock_pcs_geometry: PcsGeometry,
    veil_pcs_geometry: PcsGeometry,
    prove_overhead: f64,
    verify_overhead: f64,
    proof_size_overhead: f64,
}

fn serialized_size<T: Serialize>(value: &T) -> usize {
    bincode::serialized_size(value).expect("serialize benchmark proof field") as usize
}

fn messages(batch: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..batch)
        .map(|item| {
            std::array::from_fn(|byte| {
                (item as u64)
                    .wrapping_mul(131)
                    .wrapping_add((byte as u64).wrapping_mul(17)) as u8
            })
        })
        .collect()
}

fn distribution(mut samples: Vec<f64>) -> Timing {
    samples.sort_by(f64::total_cmp);
    let median = samples[samples.len() / 2];
    let mut deviations = samples
        .into_iter()
        .map(|sample| (sample - median).abs())
        .collect::<Vec<_>>();
    deviations.sort_by(f64::total_cmp);
    Timing {
        median_seconds: median,
        mad_seconds: deviations[deviations.len() / 2],
    }
}

fn pcs_geometry(parameters: &flock_core::pcs::PcsParams) -> PcsGeometry {
    PcsGeometry {
        committed_message_log: parameters.log_msg_len(),
        merkle_leaves: parameters.n_leaves(),
        leaf_bytes: parameters.leaf_size_bytes(),
        committed_f128: parameters.codeword_len_f128(),
    }
}

fn bench_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
    runs: usize,
) -> (ModeTiming, FlockSizes) {
    let mut prove_times = Vec::with_capacity(runs);
    let mut verify_times = Vec::with_capacity(runs);
    let mut sizes = None;
    for run in 0..=runs {
        let mut prover = FsChallenger::new(FLOCK_DOMAIN);
        let started = Instant::now();
        let (proof, commitment) = setup
            .prove(black_box(messages), black_box(digests), &mut prover)
            .expect("ordinary FLOCK proof");
        let prove_seconds = started.elapsed().as_secs_f64();

        let mut verifier = FsChallenger::new(FLOCK_DOMAIN);
        let started = Instant::now();
        setup
            .verify(
                black_box(&commitment),
                black_box(&proof),
                black_box(digests),
                &mut verifier,
            )
            .expect("ordinary FLOCK verification");
        let verify_seconds = started.elapsed().as_secs_f64();

        let measured = FlockSizes {
            total_bytes: serialized_size(&(&commitment, &proof)),
            commitment_bytes: serialized_size(&commitment),
            zerocheck_bytes: serialized_size(&proof.zerocheck),
            lincheck_bytes: serialized_size(&proof.lincheck),
            witness_pcs_bytes: serialized_size(&proof.pcs_open),
        };
        assert_eq!(
            measured.total_bytes,
            measured.commitment_bytes
                + measured.zerocheck_bytes
                + measured.lincheck_bytes
                + measured.witness_pcs_bytes,
            "ordinary FLOCK size attribution missed a serialized field"
        );
        sizes = Some(measured);
        if run > 0 {
            prove_times.push(prove_seconds);
            verify_times.push(verify_seconds);
        }
    }
    (
        ModeTiming {
            prove: distribution(prove_times),
            verify: distribution(verify_times),
        },
        sizes.expect("at least one benchmark run"),
    )
}

fn bench_veil(
    setup: &Blake3PreimageZkSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
    runs: usize,
) -> (ModeTiming, VeilSizes) {
    let mut prove_times = Vec::with_capacity(runs);
    let mut verify_times = Vec::with_capacity(runs);
    let mut sizes = None;
    for run in 0..=runs {
        let mut rng = flock_core::zk::ZkRng::from_seed([run as u8 + 1; 32]);
        let mut prover = FsChallenger::new(VEIL_DOMAIN);
        let started = Instant::now();
        let (proof, commitment) = setup
            .prove_succinct(
                black_box(messages),
                black_box(digests),
                &mut rng,
                &mut prover,
            )
            .expect("VEIL+FLOCK proof");
        let prove_seconds = started.elapsed().as_secs_f64();

        let mut verifier = FsChallenger::new(VEIL_DOMAIN);
        let started = Instant::now();
        setup
            .verify_succinct(
                black_box(&commitment),
                black_box(&proof),
                black_box(digests),
                &mut verifier,
            )
            .expect("VEIL+FLOCK verification");
        let verify_seconds = started.elapsed().as_secs_f64();

        let veil_hadamard_bytes = serialized_size(&proof.veil.hadamard);
        let veil_linear_bytes = serialized_size(&proof.veil.linear);
        let veil_total_bytes = serialized_size(&proof.veil);
        let measured = VeilSizes {
            total_bytes: serialized_size(&(&commitment, &proof)),
            commitment_bytes: serialized_size(&commitment),
            masked_zerocheck_bytes: serialized_size(&proof.masked_zerocheck),
            masked_lincheck_bytes: serialized_size(&proof.masked_lincheck),
            nonce_and_output_claim_bytes: proof.proof_nonce.len() + 2 * 16,
            hiding_witness_pcs_bytes: serialized_size(&proof.pcs_open),
            veil_hadamard_bytes,
            veil_linear_bytes,
            veil_metadata_bytes: veil_total_bytes - veil_hadamard_bytes - veil_linear_bytes,
        };
        assert_eq!(
            measured.total_bytes,
            measured.commitment_bytes
                + measured.masked_zerocheck_bytes
                + measured.masked_lincheck_bytes
                + measured.nonce_and_output_claim_bytes
                + measured.hiding_witness_pcs_bytes
                + measured.veil_hadamard_bytes
                + measured.veil_linear_bytes
                + measured.veil_metadata_bytes,
            "VEIL+FLOCK size attribution missed a serialized field"
        );
        sizes = Some(measured);
        if run > 0 {
            prove_times.push(prove_seconds);
            verify_times.push(verify_seconds);
        }
    }
    (
        ModeTiming {
            prove: distribution(prove_times),
            verify: distribution(verify_times),
        },
        sizes.expect("at least one benchmark run"),
    )
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let batch = std::env::var("VEIL_BENCH_BATCH")
        .map_or(256, |value| value.parse().expect("VEIL_BENCH_BATCH"));
    let runs =
        std::env::var("VEIL_BENCH_RUNS").map_or(3, |value| value.parse().expect("VEIL_BENCH_RUNS"));
    assert!(batch > 0 && batch <= 256 && runs > 0);

    let messages = messages(batch);
    let digests = Blake3PreimageSetup::digests_of(&messages);
    let flock_setup = Blake3PreimageSetup::new(batch);
    let veil_setup = Blake3PreimageZkSetup::new_succinct(batch);
    if batch != 256 {
        eprintln!(
            "note: VEIL+FLOCK pads to 256 slots; ordinary FLOCK uses {} slots; use batch=256 for identical circuit geometry",
            1usize << flock_setup.n_blocks_log()
        );
    }

    let (flock_timing, flock_sizes) = bench_flock(&flock_setup, &messages, &digests, runs);
    let (veil_timing, veil_sizes) = bench_veil(&veil_setup, &messages, &digests, runs);
    let report = Report {
        relation: "BLAKE3(message[i]) = digest[i], message[i] is exactly 64 bytes",
        batch,
        padded_slots: veil_setup.n_block_slots(),
        runs,
        flock_timing,
        veil_timing,
        flock_sizes,
        veil_sizes,
        flock_pcs_geometry: pcs_geometry(&flock_setup.pcs_params),
        veil_pcs_geometry: pcs_geometry(&veil_setup.pcs_params),
        prove_overhead: veil_timing.prove.median_seconds / flock_timing.prove.median_seconds,
        verify_overhead: veil_timing.verify.median_seconds / flock_timing.verify.median_seconds,
        proof_size_overhead: veil_sizes.total_bytes as f64 / flock_sizes.total_bytes as f64,
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&report).expect("serialize benchmark report")
    );
}
