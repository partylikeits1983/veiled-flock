//! Zero-knowledge mode support: the prover-side DRBG that feeds every mask,
//! and the randomizer-witness block layout shared by the hash encoders.
//!
//! Two mask species support the earlier FLOCK transcript-masking construction:
//!
//! 1. **Randomizer witness rows** — extra R1CS rows of the form `u·1 = u`
//!    (A-type; the row's A entry is a self-loop on a fresh witness column
//!    holding a uniform bit, B selects the constant-1 wire) and `1·u′ = u′`
//!    (B-type, symmetric). At fixed challenges the transcript is affine in
//!    each species separately — zerocheck round messages are bilinear across
//!    the two, since sumcheck folds merge A- and B-regions — so masking is
//!    argued conditionally: fix the B-bits, the transcript is affine in the
//!    A-bits with full image, and mix over the B-bits. With enough bits every
//!    revealed value is uniform.
//!    [`ZkBlockLayout`] describes where they live inside a block; it is part
//!    of the statement and is bound into `BlockR1cs::statement_digest`.
//! 2. **PCS masks** — the low-half mask block and the blinder codeword `g` of
//!    the hiding commitment (`pcs::commit_zk`).
//!
//! Both draw from [`ZkRng`], which is seeded from OS entropy (or a fixed seed
//! in tests) and is **independent of the Fiat–Shamir transcript**: mask
//! randomness reaches the transcript only through the committed witness /
//! codeword, so every mask is committed before any challenge that could
//! depend on it.
//!
//! This module always compiles (the layout types are plain data consumed by
//! `BlockR1cs`), but OS entropy — and every prove path that needs it — is
//! gated behind the `zk` cargo feature.

use crate::field::F128;
use serde::{Deserialize, Serialize};

/// Source of prover-secret mask material. Implemented by [`ZkRng`]; tests use
/// playback/zero implementations to probe or break the masking on purpose.
pub trait MaskSampler {
    fn fill_u64s(&mut self, out: &mut [u64]);

    fn fill_f128(&mut self, out: &mut [F128]) {
        for slot in out.iter_mut() {
            let mut pair = [0u64; 2];
            self.fill_u64s(&mut pair);
            *slot = F128 {
                lo: pair[0],
                hi: pair[1],
            };
        }
    }
}

/// Prover-side deterministic random bit generator: a BLAKE3 XOF keyed by a
/// 32-byte seed. Deterministic given the seed (tests, the rank audit);
/// [`ZkRng::from_entropy`] seeds from the OS. `fork` derives an independent,
/// domain-separated child stream so one per-proof instance can feed both the
/// witness randomizers and the PCS masks.
pub struct ZkRng {
    key: [u8; 32],
    forks: u64,
    reader: blake3::OutputReader,
}

impl ZkRng {
    pub fn from_seed(key: [u8; 32]) -> Self {
        let mut h = blake3::Hasher::new_keyed(&key);
        h.update(b"flock-zk-drbg-v0");
        Self {
            key,
            forks: 0,
            reader: h.finalize_xof(),
        }
    }

    /// Seed from OS entropy. Panics if the OS entropy source is unavailable
    /// (a proof produced without real entropy would silently not be hiding).
    #[cfg(feature = "zk")]
    pub fn from_entropy() -> Self {
        let mut key = [0u8; 32];
        getrandom::getrandom(&mut key).expect("flock-zk: OS entropy unavailable");
        Self::from_seed(key)
    }

    /// Derive an independent child stream. Children are domain-separated by
    /// `label` and by a per-parent fork counter, and do not perturb the
    /// parent's own output stream.
    pub fn fork(&mut self, label: &[u8]) -> Self {
        let mut h = blake3::Hasher::new_keyed(&self.key);
        h.update(b"flock-zk-fork-v0");
        h.update(&self.forks.to_le_bytes());
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label);
        self.forks += 1;
        Self::from_seed(*h.finalize().as_bytes())
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.reader.fill(&mut b);
        u64::from_le_bytes(b)
    }
}

impl MaskSampler for ZkRng {
    fn fill_u64s(&mut self, out: &mut [u64]) {
        // One bulk XOF read; u64 has no invalid bit patterns.
        let bytes: &mut [u8] =
            unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<u8>(), out.len() * 8) };
        self.reader.fill(bytes);
        // Canonicalize endianness so streams are platform-independent.
        for v in out.iter_mut() {
            *v = u64::from_le(*v);
        }
    }

    fn fill_f128(&mut self, out: &mut [F128]) {
        let words: &mut [u64] = unsafe {
            std::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<u64>(), out.len() * 2)
        };
        self.fill_u64s(words);
    }
}

/// Plays back a fixed F128 buffer (then panics). Used by the rank-audit tests
/// to probe the prover with unit-vector masks.
pub struct PlaybackSampler<'a> {
    pub data: &'a [F128],
    pub pos: usize,
}

impl MaskSampler for PlaybackSampler<'_> {
    fn fill_u64s(&mut self, out: &mut [u64]) {
        assert!(
            out.len().is_multiple_of(2),
            "PlaybackSampler: odd u64 request"
        );
        let n = out.len() / 2;
        for (i, chunk) in out.as_chunks_mut::<2>().0.iter_mut().enumerate() {
            let v = self.data[self.pos + i];
            chunk[0] = v.lo;
            chunk[1] = v.hi;
        }
        self.pos += n;
    }
}

/// Emits all-zero masks. Negative control ONLY: proofs made with this are NOT
/// zero-knowledge — the leakage tests use it to prove they would catch an
/// unwired mask.
pub struct ZeroSampler;

impl MaskSampler for ZeroSampler {
    fn fill_u64s(&mut self, out: &mut [u64]) {
        out.fill(0);
    }
}

/// Per-encoder randomizer sizing: how many 128-bit randomizer chunks each
/// block carries, split into the A-type and B-type groups (see module docs),
/// plus whether the chain-mask slot pair is allocated.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkConfig {
    /// A-type randomizer chunks per block (`u·1 = u` rows).
    pub rand_chunks_a: usize,
    /// B-type randomizer chunks per block (`1·u′ = u′` rows).
    pub rand_chunks_b: usize,
    /// Allocate the region-aligned mask slot pair for the chain-shift
    /// argument's committed mask (chain-capable encoders only).
    pub chain_mask: bool,
}

impl ZkConfig {
    /// Conservative default sizing for a batch statement of `2^{m-k_log}`
    /// blocks: budget `128 · V_free` random bits across the batch, where
    /// `V_free` counts every masked transcript value (zerocheck round-1
    /// vectors, all round pairs, final evals, lincheck rounds + z_partial,
    /// chain rounds, two s_hat_v vectors) plus slack. The leakage-rank audit
    /// measures the true requirement; this errs high.
    pub fn sized_for(m: usize, k_log: usize, has_chain: bool) -> Self {
        assert!(m >= 13 && k_log >= 7 && m >= k_log);
        let n_log = m - k_log;
        let v_free = 128                    // zerocheck round1_ab + round1_c
            + 2 * (m - 6)                   // zerocheck multilinear rounds
            + 2                             // final_a_eval, final_b_eval
            + 2 * (k_log - 6)               // lincheck rounds
            + 64                            // lincheck z_partial
            // Chain shift-sumcheck messages. The extended chain (Part 7) observes
            // 2·|S| more — covered by the slack below; its pad budget is MaskLayout's.
            + if has_chain { 2 * (n_log + 1) + 2 } else { 0 }
            + 256                           // two s_hat_v vectors
            + 64; // slack
        let required_bits = 128 * v_free;
        let blocks = 1usize << n_log;
        let per_block_bits = required_bits.div_ceil(blocks);
        // B-type only needs to cover the b̂-side functionals (a handful of
        // values); one chunk per block is already far above the requirement.
        let rand_chunks_a = per_block_bits.div_ceil(128).max(1);
        ZkConfig {
            rand_chunks_a,
            rand_chunks_b: 1,
            chain_mask: has_chain,
        }
    }
}

/// Resolved per-block randomizer geometry. Stored in `BlockR1cs::zk`,
/// absorbed into `statement_digest`, consumed by witness generation and the
/// lincheck circuits.
///
/// Block layout (bit indices within one `2^k_log`-bit block):
///
/// ```text
/// [0, useful_bits)                 real witness rows (unchanged)
/// [rand_bit_base, +128·chunks_a)   A-type randomizer bits  (a = z = u, b = 1)
/// [.., +128·chunks_b)              B-type randomizer bits  (b = z = u′, a = 1)
/// [mask_pair_bit_base, +2·2^r)     chain-mask slot pair (optional, aligned
///                                  to 2^{r+1}; also A-type rows)
/// [useful_bits_zk, 2^k_log)        zero padding (as before)
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkBlockLayout {
    /// First randomizer bit (= pre-zk `useful_bits` rounded up to a 128-bit
    /// chunk boundary).
    pub rand_bit_base: usize,
    pub chunks_a: usize,
    pub chunks_b: usize,
    /// Base bit of the chain-mask slot pair (two `2^region_log`-bit slots at
    /// a `2^{region_log+1}`-aligned offset), if allocated.
    pub mask_pair_bit_base: Option<usize>,
    /// Log2 size of each chain-mask slot (the chain fold's region size).
    pub mask_region_log: usize,
    /// End of the last randomizer section = the zk-extended `useful_bits`.
    pub useful_bits_zk: usize,
}

impl ZkBlockLayout {
    /// Compute the layout for a block of `2^k_log` rows whose real witness
    /// occupies `[0, useful_bits)`. `region_log` is required iff
    /// `cfg.chain_mask`. Panics if the sections don't fit in the block.
    pub fn new(
        k_log: usize,
        useful_bits: usize,
        region_log: Option<usize>,
        cfg: &ZkConfig,
    ) -> Self {
        let k = 1usize << k_log;
        let rand_bit_base = useful_bits.next_multiple_of(128);
        let a_end = rand_bit_base + 128 * cfg.rand_chunks_a;
        let b_end = a_end + 128 * cfg.rand_chunks_b;
        let (mask_pair_bit_base, mask_region_log, end) = if cfg.chain_mask {
            let r = region_log.expect("chain_mask requires region_log");
            let pair_align = 1usize << (r + 1);
            let base = b_end.next_multiple_of(pair_align);
            (Some(base), r, base + pair_align)
        } else {
            (None, 0, b_end)
        };
        assert!(
            end <= k,
            "zk randomizer sections overflow the block: end={end} > 2^{k_log}",
        );
        ZkBlockLayout {
            rand_bit_base,
            chunks_a: cfg.rand_chunks_a,
            chunks_b: cfg.rand_chunks_b,
            mask_pair_bit_base,
            mask_region_log,
            useful_bits_zk: end,
        }
    }

    /// Bit indices (== row indices == column indices; the rows are self-loops
    /// under `C = I`) of the A-type randomizer bits, **including** the
    /// chain-mask slot pair (whose rows are also `u·1 = u`).
    pub fn a_bits(&self) -> impl Iterator<Item = usize> + '_ {
        let general = self.rand_bit_base..self.rand_bit_base + 128 * self.chunks_a;
        let pair = self
            .mask_pair_bit_base
            .map(|b| b..b + (2 << self.mask_region_log))
            .unwrap_or(0..0);
        general.chain(pair)
    }

    /// Bit indices of the B-type randomizer bits.
    pub fn b_bits(&self) -> impl Iterator<Item = usize> {
        let start = self.rand_bit_base + 128 * self.chunks_a;
        start..start + 128 * self.chunks_b
    }

    /// Total randomizer bits per block (both groups + mask pair).
    pub fn rand_bits_per_block(&self) -> usize {
        128 * (self.chunks_a + self.chunks_b)
            + if self.mask_pair_bit_base.is_some() {
                2 << self.mask_region_log
            } else {
                0
            }
    }

    /// Absorb into a statement hasher (order + a tag byte per field; the
    /// layout determines which polynomial family the statement quantifies
    /// over, so it is part of the statement).
    pub fn absorb_into(&self, h: &mut blake3::Hasher) {
        h.update(b"flock-zk-layout-v0");
        h.update(&(self.rand_bit_base as u64).to_le_bytes());
        h.update(&(self.chunks_a as u64).to_le_bytes());
        h.update(&(self.chunks_b as u64).to_le_bytes());
        match self.mask_pair_bit_base {
            Some(b) => {
                h.update(&[1u8]);
                h.update(&(b as u64).to_le_bytes());
            }
            None => {
                h.update(&[0u8]);
            }
        }
        h.update(&(self.mask_region_log as u64).to_le_bytes());
        h.update(&(self.useful_bits_zk as u64).to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn drbg_deterministic_and_forks_independent() {
        let mut a = ZkRng::from_seed([7u8; 32]);
        let mut b = ZkRng::from_seed([7u8; 32]);
        let xa: Vec<u64> = (0..8).map(|_| a.next_u64()).collect();
        let xb: Vec<u64> = (0..8).map(|_| b.next_u64()).collect();
        assert_eq!(xa, xb);

        // Forks: distinct from parent stream, distinct across labels and
        // across repeated forks with the same label; parent stream unchanged.
        let mut p1 = ZkRng::from_seed([9u8; 32]);
        let mut p2 = ZkRng::from_seed([9u8; 32]);
        let mut c1 = p1.fork(b"x");
        let mut c2 = p1.fork(b"x");
        let mut c3 = p1.fork(b"y");
        let s1 = c1.next_u64();
        let s2 = c2.next_u64();
        let s3 = c3.next_u64();
        assert_ne!(s1, s2);
        assert_ne!(s1, s3);
        // Parent output is unaffected by forking.
        for _ in 0..3 {
            let _ = p2.fork(b"ignored");
        }
        let p1_rest: Vec<u64> = (0..4).map(|_| p1.next_u64()).collect();
        let p2_rest: Vec<u64> = (0..4).map(|_| p2.next_u64()).collect();
        assert_eq!(p1_rest, p2_rest);
        // fill_f128 agrees with the word stream.
        let mut w = ZkRng::from_seed([7u8; 32]);
        let mut f = [F128::ZERO; 4];
        w.fill_f128(&mut f);
        assert_eq!(f[0].lo, xa[0]);
        assert_eq!(f[0].hi, xa[1]);
        assert_eq!(f[3].hi, xa[7]);
    }

    #[test]
    fn layout_math() {
        // BLAKE3-shaped block: k_log=14, useful_bits=15409, region_log=8.
        // 2 A-chunks + 1 B-chunk end at 15872 = 31·512, so the chain pair
        // aligns flush and the block is filled exactly.
        let cfg = ZkConfig {
            rand_chunks_a: 2,
            rand_chunks_b: 1,
            chain_mask: true,
        };
        let l = ZkBlockLayout::new(14, 15409, Some(8), &cfg);
        assert_eq!(l.rand_bit_base, 15488);
        assert_eq!(l.b_bits().next().unwrap(), 15488 + 256);
        assert_eq!(l.mask_pair_bit_base, Some(15872));
        assert_eq!(l.useful_bits_zk, 16384);
        assert_eq!(l.rand_bits_per_block(), 384 + 512);
        assert_eq!(l.a_bits().count(), 256 + 512);
        assert_eq!(l.b_bits().count(), 128);

        // One more A-chunk pushes the pair past the block end ⇒ panic.
        let too_big = ZkConfig {
            rand_chunks_a: 3,
            ..cfg
        };
        let r = std::panic::catch_unwind(|| ZkBlockLayout::new(14, 15409, Some(8), &too_big));
        assert!(r.is_err(), "expected overflow panic");

        // Without the chain pair, 3 A-chunks fit fine.
        let no_chain = ZkConfig {
            rand_chunks_a: 3,
            rand_chunks_b: 1,
            chain_mask: false,
        };
        let l2 = ZkBlockLayout::new(14, 15409, None, &no_chain);
        assert_eq!(l2.useful_bits_zk, 16000);
        assert_eq!(l2.rand_bits_per_block(), 512);
        assert_eq!(l2.a_bits().count(), 384);
        assert_eq!(l2.b_bits().count(), 128);
    }

    #[test]
    fn sized_for_is_sane() {
        let cfg = ZkConfig::sized_for(22, 14, false);
        assert!(cfg.rand_chunks_a >= 1 && cfg.rand_chunks_b >= 1);
        // Total bits across the batch must cover the budget.
        let blocks = 1usize << (22 - 14);
        assert!(blocks * 128 * cfg.rand_chunks_a >= 128 * 500);
    }

    #[test]
    fn playback_and_zero_samplers() {
        let data = [F128 { lo: 1, hi: 2 }, F128 { lo: 3, hi: 4 }];
        let mut p = PlaybackSampler {
            data: &data,
            pos: 0,
        };
        let mut out = [F128::ZERO; 2];
        p.fill_f128(&mut out);
        assert_eq!(out, data);
        let mut z = ZeroSampler;
        let mut w = [7u64; 4];
        z.fill_u64s(&mut w);
        assert_eq!(w, [0; 4]);
    }
}
