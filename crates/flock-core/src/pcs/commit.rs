//! PCS commit phase: pack → RS encode (additive NTT) → Merkle root.
//!
//! Uses [`AdditiveNttF128`], the binius-style LCH NTT with neighbors-last
//! pairing. The commit produces a non-systematic RS codeword (treating the
//! packed witness as novel-basis coefficients, zero-padded to the larger
//! domain, then forward-NTT'd).
//!
//! ## Layout
//!
//! With parameters `(m, log_inv_rate)`:
//! - `log_msg_len = m − LOG_PACKING` (= log2 of packed witness length)
//! - `k_code      = log_msg_len + log_inv_rate` (= log2 of codeword length)
//!
//! The codeword is a flat sequence of `2^k_code` F_{2^128} elements. Each
//! Merkle leaf is **one** F_{2^128} element = 16 bytes.

use crate::field::F128;
use crate::merkle::{self, Hash};
use crate::ntt::AdditiveNttF128;
use crate::pcs::pack::LOG_PACKING;
use serde::{Deserialize, Serialize};

/// PCS configuration. Polynomial-basis subspace `{1, x, x², …}` for the NTT.
///
/// Interleaved RS: the packed witness is split into `2^log_batch_size`
/// independent sub-NTTs of size `2^log_dim` each. Each Merkle leaf holds one
/// codeword position across all `2^log_batch_size` lanes
/// (`2^log_batch_size · 16` bytes per leaf). This trades leaf-call SHA-256
/// overhead (was 16 B leaves, now 512 B leaves at default `log_batch_size=5`)
/// for much fewer Merkle nodes and better scaling to large `m`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PcsParams {
    pub m: usize,
    pub log_inv_rate: usize,
    /// Number of parallel sub-NTTs = `2^log_batch_size`. Default 5 (= 32 lanes).
    pub log_batch_size: usize,
    /// Ligerito parameter profile (fast/slim/secure). Selects which embedded
    /// security config (queries, OOD samples, grinding schedule) drives the
    /// PCS opening; must agree with `log_inv_rate`
    /// (`profile.log_inv_rate() == log_inv_rate`). Defaults to `Fast`.
    #[serde(default)]
    pub profile: crate::pcs::ligerito::LigeritoProfile,
    /// Zero-knowledge mode. The committed message becomes
    /// `[mask ‖ z_packed]` (uniform low half, witness in the top half), and a
    /// full-support blinder codeword `g` is committed alongside it in shared
    /// wide Merkle leaves. Doubles both the message dimension and the leaf
    /// width; the opening folds `F = message′ + c·g` for an FS challenge `c`.
    /// Requires the `zk` cargo feature.
    #[serde(default)]
    pub zk: bool,
}

impl PcsParams {
    /// Log length of the **committed** message (= log2 packed witness length,
    /// +1 in zk mode for the low-half mask block).
    pub fn log_msg_len(&self) -> usize {
        self.m - LOG_PACKING + (self.zk as usize)
    }
    /// Log length of the packed **witness** (excludes the zk mask block).
    pub fn witness_log_msg_len(&self) -> usize {
        self.m - LOG_PACKING
    }
    /// Log lane count actually committed per Merkle leaf: the f′ lanes, plus
    /// the blinder-`g` lanes in zk mode.
    pub fn log_lanes_committed(&self) -> usize {
        self.log_batch_size + (self.zk as usize)
    }
    /// Per-sub-NTT log dimension (= number of "position" coords).
    pub fn log_dim(&self) -> usize {
        self.log_msg_len() - self.log_batch_size
    }
    /// Codeword size (log) per sub-NTT.
    pub fn k_code(&self) -> usize {
        self.log_dim() + self.log_inv_rate
    }
    /// Number of Merkle leaves (= per-sub-NTT codeword length).
    pub fn n_positions(&self) -> usize {
        1usize << self.k_code()
    }
    /// `num_ntts` = `2^log_batch_size`.
    pub fn num_ntts(&self) -> usize {
        1usize << self.log_batch_size
    }
    /// Total codeword length in F_{2^128} elements
    /// (= `n_positions() * num_ntts()`, ×2 in zk mode for the `g` lanes).
    pub fn codeword_len_f128(&self) -> usize {
        self.n_positions() << self.log_lanes_committed()
    }
    /// `log_2` of the F_{2^128} count per **initial** Merkle leaf
    /// (= `log_batch_size`; in zk mode +1 — each leaf carries the f′ lanes
    /// followed by the `g` lanes at the same position).
    pub fn log_leaf_f128_count(&self) -> usize {
        self.log_lanes_committed()
    }
    /// Number of initial-tree Merkle leaves
    /// (= `codeword_len_f128() / 2^log_batch_size = 2^k_code`).
    pub fn n_leaves(&self) -> usize {
        self.codeword_len_f128() >> self.log_leaf_f128_count()
    }
    /// Merkle leaf size in bytes = `num_ntts() * 16`.
    pub fn leaf_size_bytes(&self) -> usize {
        16usize << self.log_leaf_f128_count()
    }

    fn validate(&self) {
        assert!(
            self.m >= LOG_PACKING + self.log_batch_size,
            "m={} too small (need m ≥ LOG_PACKING + log_batch_size = {})",
            self.m,
            LOG_PACKING + self.log_batch_size,
        );
        assert!(
            self.log_inv_rate >= 1,
            "log_inv_rate must be ≥ 1 for a non-trivial RS code",
        );
        #[cfg(not(feature = "zk"))]
        assert!(
            !self.zk,
            "PcsParams.zk requires the `zk` cargo feature",
        );
    }
}

/// Public commitment (Merkle root + params).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Commitment {
    pub root: Hash,
    pub params: PcsParams,
}

/// Prover-side state retained after commit for use in the opening phase.
///
/// **The packed witness is NOT stored here.** The caller is responsible for
/// retaining its own copy of the packed witness across commit + open. This
/// avoids ~4 GB of duplication at large `m`, dropping peak commit memory by
/// a factor of ~1.5 (e.g. at m=35: 13 GB → 9 GB).
pub struct ProverData {
    pub codeword: Vec<F128>,
    pub merkle_tree: Vec<Hash>,
    /// zk mode only: the uniform low-half mask block of the committed message
    /// `message′ = [zk_mask ‖ z_packed]` (length `2^{m−7}`; empty otherwise).
    pub zk_mask: Vec<F128>,
    /// zk mode only: the full-support blinder codeword `g` (length `2^{m−6}`;
    /// empty otherwise). The opening runs on `F = message′ + c·g`.
    pub zk_blind: Vec<F128>,
}

// Recycle the codeword buffer (the prover's largest single allocation —
// 128 MB at m = 29) through the scratch pool instead of unmapping it.
impl Drop for ProverData {
    fn drop(&mut self) {
        crate::scratch::give_f128(std::mem::take(&mut self.codeword));
        if !self.zk_mask.is_empty() {
            crate::scratch::give_f128(std::mem::take(&mut self.zk_mask));
        }
        if !self.zk_blind.is_empty() {
            crate::scratch::give_f128(std::mem::take(&mut self.zk_blind));
        }
    }
}

/// Commit to a witness in **F_{2^128}-packed** form (polynomial basis: bit
/// `r` of `z_packed[i]` = logical bit `i·128 + r`).
///
/// Uses **interleaved RS encoding**: `num_ntts = 2^log_batch_size` independent
/// sub-NTTs share the same domain and twiddles, processed via the SoA
/// interleaved transform. The codeword is stored position-major SoA
/// (`codeword[pos · num_ntts + lane]`); each Merkle leaf is one position =
/// `num_ntts` F_{2^128} = `num_ntts · 16` bytes.
///
/// **Takes the witness by reference**. The returned [`ProverData`] does NOT
/// retain a copy of the packed witness — the caller is responsible for
/// keeping its own copy across commit + open. This frees ~4 GB during the
/// NTT/Merkle phase at large `m`.
///
/// `z_packed.len()` must equal `2^(m - LOG_PACKING) = 2^(m - 7)`.
pub fn commit(z_packed: &[F128], params: &PcsParams) -> (Commitment, ProverData) {
    params.validate();
    assert!(!params.zk, "zk params require commit_zk");
    assert_eq!(z_packed.len(), 1usize << params.log_msg_len());

    let codeword_len = params.codeword_len_f128();

    // ---- Codeword buffer (SoA): codeword[pos * num_ntts + lane].
    // Copy first 2^log_msg_len positions from packed witness; zero-pad the rest.
    //
    // At large m the codeword buffer is huge (128 MB at m=29, 512 MB at m=31).
    // `vec![F128::ZERO; n]` would eagerly zero all 128 MB upfront, then
    // immediately overwrite the lower half with `z_packed` — half the zero-fill
    // is wasted. Instead allocate uninit, write each half exactly once: copy
    // `z_packed` into the lower half, and zero-fill JUST the upper half (the
    // RS-encoding zero coefficients that the NTT's first-layer butterfly will
    // read). Saves ~64 MB of memory writes at m=29 (~9 ms).
    let codeword = crate::scratch::take_f128(codeword_len);
    commit_into(z_packed, params, codeword)
}

/// Like [`commit`], but reuses a caller-provided codeword buffer instead of
/// allocating its own. The buffer must have length `codeword_len`; its
/// CONTENTS may be arbitrary (uninit/stale) — every slot is written here:
/// `z_packed` is replicated into all `2^log_inv_rate` sub-blocks (the exact
/// state after the first `log_inv_rate` NTT layers on `[z, 0, …, 0]`), in
/// parallel. Buffers from [`prefault_codeword_during`] or the scratch pool
/// are already resident, so no write faults.
pub fn commit_into(
    z_packed: &[F128],
    params: &PcsParams,
    mut codeword: Vec<F128>,
) -> (Commitment, ProverData) {
    params.validate();
    assert!(!params.zk, "zk params require commit_zk");
    assert_eq!(z_packed.len(), 1usize << params.log_msg_len());
    let codeword_len = params.codeword_len_f128();
    assert_eq!(
        codeword.len(),
        codeword_len,
        "commit_into: prebuilt codeword buffer has wrong length"
    );

    // RS encoding of [z, 0, …, 0] starts with `log_inv_rate` butterfly layers
    // whose bottom inputs are all zero — each is a pure copy, so after those
    // layers the buffer holds 2^log_inv_rate replicas of z. Write that state
    // directly (replicating z costs the same writes as the zero-fill it
    // replaces) and start the NTT at layer `log_inv_rate`, skipping those
    // layers' full-buffer reads and multiplies.
    replicate_message_fill(&mut codeword, z_packed);

    finalize_commit(codeword, params)
}

/// Zero-knowledge commit: commits `message′ = [mask ‖ z_packed]` (uniform
/// low-half mask, witness in the top half) **and** a full-support uniform
/// blinder `g` of the same length, in shared wide Merkle leaves:
///
/// ```text
/// leaf(pos) = [ f′ lane symbols (num_ntts) ‖ g lane symbols (num_ntts) ]
/// ```
///
/// Both are RS-encoded by the same interleaved NTT (2·num_ntts lanes). The
/// opening phase runs the Ligerito recursion on `F = message′ + c·g` for an
/// FS challenge `c` sampled after the basis is fixed; the mask block hides
/// the raw f′ rows revealed at L0, and `g` hides everything downstream
/// (recursive rows, sumcheck messages, the final residual).
///
/// Mask randomness comes from `rng` — a prover-secret DRBG, never the FS
/// transcript. The sampled `mask` and `g` are returned in
/// [`ProverData::zk_mask`] / [`ProverData::zk_blind`].
#[cfg(feature = "zk")]
pub fn commit_zk<R: crate::zk::MaskSampler + ?Sized>(
    z_packed: &[F128],
    params: &PcsParams,
    rng: &mut R,
) -> (Commitment, ProverData) {
    params.validate();
    assert!(params.zk, "commit_zk requires PcsParams.zk");
    assert_eq!(z_packed.len(), 1usize << params.witness_log_msg_len());

    let w = z_packed.len();
    let mut mask = crate::scratch::take_f128(w);
    rng.fill_f128(&mut mask);
    let mut blind = crate::scratch::take_f128(2 * w);
    rng.fill_f128(&mut blind);

    let mut codeword = crate::scratch::take_f128(params.codeword_len_f128());
    replicate_message_fill_zk(
        &mut codeword,
        &mask,
        z_packed,
        &blind,
        params.num_ntts(),
    );
    let (commitment, mut pd) = finalize_commit(codeword, params);
    pd.zk_mask = mask;
    pd.zk_blind = blind;
    (commitment, pd)
}

/// Fill the wide zk codeword buffer with the replicated interleaved message —
/// the exact state after the first `log_inv_rate` forward-NTT layers on the
/// zero-padded wide coefficient vector. Lane `j < num_ntts` of position `p`
/// carries `message′[p·num_ntts + j]` (`message′ = [mask ‖ z_packed]` flat);
/// lane `num_ntts + j` carries `g[p·num_ntts + j]`.
#[cfg(feature = "zk")]
pub(crate) fn replicate_message_fill_zk(
    codeword: &mut [F128],
    mask: &[F128],
    z_packed: &[F128],
    g: &[F128],
    num_ntts: usize,
) {
    use rayon::prelude::*;
    debug_assert_eq!(mask.len(), z_packed.len());
    debug_assert_eq!(g.len(), 2 * z_packed.len());
    let wide = 2 * num_ntts;
    debug_assert!(codeword.len().is_multiple_of(wide));
    let msg_positions = g.len() / num_ntts;
    let mask_positions = mask.len() / num_ntts;
    debug_assert!((codeword.len() / wide).is_multiple_of(msg_positions));
    codeword
        .par_chunks_mut(wide)
        .with_min_len(1 << 10)
        .enumerate()
        .for_each(|(pos, leaf)| {
            let p = pos % msg_positions;
            let f_src = if p < mask_positions {
                &mask[p * num_ntts..(p + 1) * num_ntts]
            } else {
                let q = p - mask_positions;
                &z_packed[q * num_ntts..(q + 1) * num_ntts]
            };
            leaf[..num_ntts].copy_from_slice(f_src);
            leaf[num_ntts..].copy_from_slice(&g[p * num_ntts..(p + 1) * num_ntts]);
        });
}

/// Fill `codeword` with `2^r` replicas of `msg` (`r = log2(codeword.len() /
/// msg.len())`) — the exact state after the first `r` forward-NTT layers on
/// the zero-padded coefficient vector `[msg, 0, …, 0]`. Pair with
/// `forward_transform_interleaved_from_layer(…, r)`. Every slot of `codeword`
/// is written (input contents may be stale/uninit).
pub(crate) fn replicate_message_fill(codeword: &mut [F128], msg: &[F128]) {
    use rayon::prelude::*;
    let msg_len = msg.len();
    debug_assert!(codeword.len().is_multiple_of(msg_len));
    const COPY_CHUNK: usize = 1 << 16;
    if msg_len >= COPY_CHUNK {
        // Both are powers of two, so chunks never straddle a replica boundary.
        codeword
            .par_chunks_mut(COPY_CHUNK)
            .enumerate()
            .for_each(|(i, dst)| {
                let src_off = (i * COPY_CHUNK) % msg_len;
                dst.copy_from_slice(&msg[src_off..src_off + dst.len()]);
            });
    } else {
        for rep in codeword.chunks_mut(msg_len) {
            rep.copy_from_slice(msg);
        }
    }
}

/// Shared tail of [`commit`] / [`commit_into`]: interleaved forward additive
/// NTT (RS-encode every lane) then the initial Merkle tree over codeword rows.
fn finalize_commit(mut codeword: Vec<F128>, params: &PcsParams) -> (Commitment, ProverData) {
    let timing = std::env::var_os("FLOCK_COMMIT_TIMING").is_some();
    let t_ntt = std::time::Instant::now();
    // ---- Interleaved forward additive NTT: 2^log_batch_size independent
    // sub-NTTs with shared twiddles. Each sub-NTT operates on its lane of the
    // SoA buffer. The first `log_inv_rate` layers were pre-applied by the
    // caller's replicate-fill (commit_into), so start past them.
    let ntt = AdditiveNttF128::standard(params.k_code());
    ntt.forward_transform_interleaved_from_layer(
        &mut codeword,
        // In zk mode the leaf-width lanes include the blinder-g lanes; the
        // NTT treats them as additional independent sub-NTTs.
        1usize << params.log_lanes_committed(),
        params.log_inv_rate,
    );
    if timing {
        eprintln!(
            "[commit-timing] ntt: {:.2} ms",
            t_ntt.elapsed().as_secs_f64() * 1e3
        );
    }
    let t_merkle = std::time::Instant::now();

    // ---- Merkle commitment: one leaf per codeword position = num_ntts F128.
    // Zero-copy: cast the codeword Vec<F128> directly to &[u8]. F128 is
    // repr(C, align(16)) with two u64s laid out little-endian — same bytes
    // as the explicit lo.to_le_bytes() + hi.to_le_bytes() serialization.
    let codeword_bytes: &[u8] = unsafe {
        core::slice::from_raw_parts(
            codeword.as_ptr() as *const u8,
            codeword.len() * core::mem::size_of::<F128>(),
        )
    };
    // Initial tree: one leaf per codeword position, each containing the
    // row-batch lanes (num_ntts F_{2^128} values = 2^log_batch_size). This is
    // Ligerito's L0 commitment.
    let merkle_tree = merkle::merkle_tree(codeword_bytes, params.n_leaves());
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    if timing {
        eprintln!(
            "[commit-timing] merkle: {:.2} ms",
            t_merkle.elapsed().as_secs_f64() * 1e3
        );
    }

    (
        Commitment {
            root,
            params: params.clone(),
        },
        ProverData {
            codeword,
            merkle_tree,
            zk_mask: Vec::new(),
            zk_blind: Vec::new(),
        },
    )
}

/// Tag the current thread as background QoS. On macOS the scheduler then
/// strongly prefers efficiency (E) cores — ideal for the fault/bandwidth-bound
/// codeword pre-fault, which we want OFF the performance cores running witness
/// generation. No-op on other platforms.
#[cfg(target_os = "macos")]
fn set_background_qos() {
    // QOS_CLASS_BACKGROUND = 0x09. Declared inline to avoid a libc dependency.
    unsafe extern "C" {
        fn pthread_set_qos_class_self_np(qos_class: u32, relative_priority: i32) -> i32;
    }
    unsafe {
        let _ = pthread_set_qos_class_self_np(0x09, 0);
    }
}
#[cfg(not(target_os = "macos"))]
fn set_background_qos() {}

/// Allocate + zero-fill (pre-fault) the codeword buffer that [`commit_into`]
/// will consume, on a background-QoS (E-core) thread, **while** `gen` runs on
/// the caller's performance threads. Returns `(Some(buf), gen_result)`.
///
/// The codeword alloc is page-fault-bound (first-touch of a fresh 64–512 MB
/// buffer) and scales ~1.0×, so overlapping it with witness generation hides it
/// almost entirely (measured ~99% at m=29 — see `benches/ecore_offload_probe`).
///
/// **Gated for honest single-threaded behavior:** when the rayon pool has ≤ 1
/// thread (i.e. `RAYON_NUM_THREADS=1`), this spawns **zero** OS threads — it
/// runs `gen` and returns `None`, leaving [`commit`] to allocate inline. The
/// whole offload is therefore invisible to truly-serial runs.
pub fn prefault_codeword_during<R>(
    params: &PcsParams,
    generate: impl FnOnce() -> R,
) -> (Option<Vec<F128>>, R) {
    if rayon::current_num_threads() <= 1 || std::env::var_os("FLOCK_NO_PREFAULT").is_some() {
        // Truly single-threaded (or explicitly disabled): no extra OS thread;
        // commit allocates inline. FLOCK_NO_PREFAULT lets benchmarks A/B the
        // offload and keeps fixed-thread-count sweeps honest.
        return (None, generate());
    }
    let codeword_len = params.codeword_len_f128();
    // Warm path: a pooled buffer is already resident — there is nothing to
    // pre-fault, and commit_into writes every slot itself. Skip the thread.
    if let Some(buf) = crate::scratch::try_take_f128(codeword_len) {
        return (Some(buf), generate());
    }
    // Cold path: allocate + first-touch on a background-QoS thread, hidden
    // under witness generation. (commit_into rewrites all slots, so the
    // zero values themselves don't matter — the page faults do.)
    std::thread::scope(|s| {
        let h = s.spawn(move || {
            set_background_qos();
            let mut buf: Vec<F128> = crate::alloc_uninit_f128_vec(codeword_len);
            unsafe {
                std::ptr::write_bytes(buf.as_mut_ptr(), 0u8, codeword_len);
            }
            buf
        });
        let r = generate();
        (Some(h.join().unwrap()), r)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn bits(&mut self, n: usize) -> Vec<bool> {
            (0..n).map(|_| self.next_u64() & 1 == 1).collect()
        }
    }

    fn default_params(m: usize) -> PcsParams {
        PcsParams {
            m,
            log_inv_rate: 1,
            log_batch_size: 1,
            profile: Default::default(),
            zk: false,
        }
    }

    /// The replicate-fill + start-at-layer-`log_inv_rate` fast path must be
    /// byte-identical to the definitional encoding: zero-padded coefficients
    /// through the FULL forward NTT. Covers rate 1/2 and 1/4 and both
    /// interleaving widths.
    #[test]
    fn commit_matches_full_ntt_oracle() {
        use crate::ntt::AdditiveNttF128;
        let mut rng = Rng::new(0xFEED);
        for (m, log_inv_rate, log_batch_size) in [(10, 1, 1), (12, 1, 2), (12, 2, 1), (14, 2, 3)] {
            let params = PcsParams {
                m,
                log_inv_rate,
                log_batch_size,
                profile: Default::default(),
                zk: false,
            };
            let z = rng.bits(1 << m);
            let z_packed = super::super::pack::pack_witness(&z, m);

            let (commitment, pd) = commit(&z_packed, &params);

            // Oracle: explicit [z, 0, …, 0] coefficients, full NTT from layer 0.
            let mut oracle = vec![F128::ZERO; params.codeword_len_f128()];
            oracle[..z_packed.len()].copy_from_slice(&z_packed);
            let ntt = AdditiveNttF128::standard(params.k_code());
            ntt.forward_transform_interleaved(&mut oracle, params.num_ntts());

            assert_eq!(
                pd.codeword, oracle,
                "codeword mismatch at m={m} r={log_inv_rate}"
            );
            let oracle_bytes: &[u8] = unsafe {
                core::slice::from_raw_parts(oracle.as_ptr() as *const u8, oracle.len() * 16)
            };
            let oracle_root = *crate::merkle::merkle_tree(oracle_bytes, params.n_leaves())
                .last()
                .unwrap();
            assert_eq!(
                commitment.root, oracle_root,
                "root mismatch at m={m} r={log_inv_rate}"
            );
        }
    }

    /// zk commit must equal the definitional wide encoding: the interleaved
    /// coefficient vector `[message′ ‖ g]` (per-position: f′ lanes then g
    /// lanes), zero-padded, through the FULL forward NTT with 2·num_ntts
    /// lanes, Merkle-committed over wide leaves.
    #[cfg(feature = "zk")]
    #[test]
    fn commit_zk_matches_wide_oracle() {
        use crate::ntt::AdditiveNttF128;
        use crate::zk::{MaskSampler, ZkRng};
        let mut rng = Rng::new(0xC0FFEE);
        for (m, log_inv_rate, log_batch_size) in [(12, 1, 2), (13, 2, 3)] {
            let params = PcsParams {
                m,
                log_inv_rate,
                log_batch_size,
                profile: Default::default(),
                zk: true,
            };
            let z = rng.bits(1 << m);
            let z_packed = super::super::pack::pack_witness(&z, m);
            let w = z_packed.len();

            let mut mask_rng = ZkRng::from_seed([3u8; 32]);
            let (commitment, pd) = commit_zk(&z_packed, &params, &mut mask_rng);

            // Reproduce the masks from the same seed, in the same order.
            let mut oracle_rng = ZkRng::from_seed([3u8; 32]);
            let mut mask = vec![F128::ZERO; w];
            oracle_rng.fill_f128(&mut mask);
            let mut g = vec![F128::ZERO; 2 * w];
            oracle_rng.fill_f128(&mut g);
            assert_eq!(pd.zk_mask, mask);
            assert_eq!(pd.zk_blind, g);

            // Definitional wide coefficient vector, full NTT from layer 0.
            let num_ntts = params.num_ntts();
            let wide = 2 * num_ntts;
            let msg_positions = (2 * w) / num_ntts;
            let mut oracle = vec![F128::ZERO; params.codeword_len_f128()];
            let msg_prime: Vec<F128> = mask.iter().chain(z_packed.iter()).copied().collect();
            for p in 0..msg_positions {
                for j in 0..num_ntts {
                    oracle[p * wide + j] = msg_prime[p * num_ntts + j];
                    oracle[p * wide + num_ntts + j] = g[p * num_ntts + j];
                }
            }
            let ntt = AdditiveNttF128::standard(params.k_code());
            ntt.forward_transform_interleaved(&mut oracle, wide);
            assert_eq!(pd.codeword, oracle, "zk codeword mismatch at m={m}");

            let oracle_bytes: &[u8] = unsafe {
                core::slice::from_raw_parts(oracle.as_ptr() as *const u8, oracle.len() * 16)
            };
            let oracle_root = *crate::merkle::merkle_tree(oracle_bytes, params.n_leaves())
                .last()
                .unwrap();
            assert_eq!(commitment.root, oracle_root, "zk root mismatch at m={m}");

            // Determinism under the seed; fresh masks under a new seed.
            let mut rng_same = ZkRng::from_seed([3u8; 32]);
            let (c2, _pd2) = commit_zk(&z_packed, &params, &mut rng_same);
            assert_eq!(commitment.root, c2.root);
            let mut rng_other = ZkRng::from_seed([4u8; 32]);
            let (c3, _pd3) = commit_zk(&z_packed, &params, &mut rng_other);
            assert_ne!(commitment.root, c3.root, "root must depend on the masks");
        }
    }

    #[cfg(feature = "zk")]
    #[test]
    #[should_panic(expected = "zk params require commit_zk")]
    fn plain_commit_rejects_zk_params() {
        let params = PcsParams {
            m: 10,
            log_inv_rate: 1,
            log_batch_size: 1,
            profile: Default::default(),
            zk: true,
        };
        let z_packed = vec![F128::ZERO; 1 << 3];
        let _ = commit(&z_packed, &params);
    }

    #[test]
    fn commit_runs_and_produces_root() {
        let mut rng = Rng::new(42);
        for m in [8usize, 10, 12] {
            let z = rng.bits(1 << m);
            let z_packed = super::super::pack::pack_witness(&z, m);
            let params = default_params(m);
            let (commitment, prover_data) = commit(&z_packed, &params);
            assert_eq!(prover_data.codeword.len(), params.codeword_len_f128());
            assert_eq!(
                prover_data.merkle_tree.last().copied().unwrap(),
                commitment.root
            );
            assert_eq!(z_packed.len(), 1 << params.log_msg_len());
        }
    }

    #[test]
    fn commit_is_deterministic() {
        let mut rng = Rng::new(7);
        let m = 10;
        let z = rng.bits(1 << m);
        let z_packed = super::super::pack::pack_witness(&z, m);
        let params = default_params(m);
        let (c1, _) = commit(&z_packed, &params);
        let (c2, _) = commit(&z_packed, &params);
        assert_eq!(c1.root, c2.root);
    }

    #[test]
    fn commit_root_sensitive_to_witness() {
        let mut rng = Rng::new(99);
        let m = 10;
        let mut z = rng.bits(1 << m);
        let params = default_params(m);
        let (c1, _) = commit(&super::super::pack::pack_witness(&z, m), &params);
        z[7] ^= true;
        let (c2, _) = commit(&super::super::pack::pack_witness(&z, m), &params);
        assert_ne!(c1.root, c2.root);
    }

    #[test]
    fn rs_encoding_is_linear() {
        let mut rng = Rng::new(123);
        let m = 9;
        let params = default_params(m);
        let z1 = rng.bits(1 << m);
        let z2 = rng.bits(1 << m);
        let z_xor: Vec<bool> = z1.iter().zip(&z2).map(|(a, b)| a ^ b).collect();
        let pack = |z: &[bool]| super::super::pack::pack_witness(z, m);
        let (_, pd1) = commit(&pack(&z1), &params);
        let (_, pd2) = commit(&pack(&z2), &params);
        let (_, pd_x) = commit(&pack(&z_xor), &params);
        for (i, (&c1, &c2)) in pd1.codeword.iter().zip(&pd2.codeword).enumerate() {
            assert_eq!(c1 + c2, pd_x.codeword[i], "linearity fails at i={i}");
        }
    }

    #[test]
    fn codeword_doubles_message_length() {
        let mut rng = Rng::new(2);
        let m = 10;
        let params = default_params(m);
        let z = rng.bits(1 << m);
        let z_packed = super::super::pack::pack_witness(&z, m);
        let (_, pd) = commit(&z_packed, &params);
        assert_eq!(pd.codeword.len(), 2 * z_packed.len());
    }
}
