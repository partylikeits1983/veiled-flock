use flock_core::{challenger::FsChallenger, zk::ZkRng};

use super::*;

fn vector(length: usize, offset: u64) -> Vec<F128> {
    (0..length)
        .map(|index| {
            F128::new(
                offset + index as u64,
                (offset ^ index as u64).rotate_left(13),
            )
        })
        .collect()
}

fn fixture() -> (VectorParameters, Vec<F128>, Vec<F128>, Vec<F128>, Vec<F128>) {
    let parameters = VectorParameters::with_security(21, 3, 9, 4).unwrap();
    let a = vector(21, 10);
    let b = vector(21, 100);
    let c = a.iter().zip(&b).map(|(a, b)| *a * *b).collect();
    let dot = vector(21, 1000);
    (parameters, a, b, c, dot)
}

#[test]
fn hadamard_and_dot_roundtrip() {
    let (parameters, a, b, c, dot) = fixture();
    let mut rng = ZkRng::from_seed([21; 32]);
    let ctx = RoContext::native([1; 32]);
    let data = commit_hadamard(&a, &b, &c, parameters, &mut rng, &ctx, RoChannel::MaskP).unwrap();
    let mut prover_challenger = FsChallenger::new(b"veil-f128-hadamard-test");
    let proof = prove_hadamard_and_dots(&dot, data, &mut prover_challenger).unwrap();
    let mut verifier_challenger = FsChallenger::new(b"veil-f128-hadamard-test");
    verify_hadamard_and_dots(
        &dot,
        &proof,
        &mut verifier_challenger,
        &ctx,
        RoChannel::MaskP,
    )
    .unwrap();
}

#[test]
fn false_hadamard_relation_is_rejected() {
    let (parameters, a, b, mut c, dot) = fixture();
    c[7] += F128::ONE;
    let mut rng = ZkRng::from_seed([22; 32]);
    let ctx = RoContext::native([2; 32]);
    let data = commit_hadamard(&a, &b, &c, parameters, &mut rng, &ctx, RoChannel::MaskP).unwrap();
    let mut prover_challenger = FsChallenger::new(b"veil-f128-hadamard-false");
    let proof = prove_hadamard_and_dots(&dot, data, &mut prover_challenger).unwrap();
    let mut verifier_challenger = FsChallenger::new(b"veil-f128-hadamard-false");
    assert!(
        verify_hadamard_and_dots(
            &dot,
            &proof,
            &mut verifier_challenger,
            &ctx,
            RoChannel::MaskP,
        )
        .is_err(),
        "a false pointwise product must fail the random reduction check"
    );
}

#[test]
fn opening_mutation_is_rejected() {
    let (parameters, a, b, c, dot) = fixture();
    let mut rng = ZkRng::from_seed([23; 32]);
    let ctx = RoContext::native([3; 32]);
    let data = commit_hadamard(&a, &b, &c, parameters, &mut rng, &ctx, RoChannel::MaskP).unwrap();
    let mut prover_challenger = FsChallenger::new(b"veil-f128-hadamard-mutation");
    let mut proof = prove_hadamard_and_dots(&dot, data, &mut prover_challenger).unwrap();
    proof.opening.rows[0] += F128::ONE;
    let mut verifier_challenger = FsChallenger::new(b"veil-f128-hadamard-mutation");
    assert!(
        verify_hadamard_and_dots(
            &dot,
            &proof,
            &mut verifier_challenger,
            &ctx,
            RoChannel::MaskP,
        )
        .is_err()
    );
}
