#![cfg_attr(not(feature = "std"), no_std)]

//! `flock-core`: the protocol library and verifier for Flock's R1CS-over-GF(2)
//! sumcheck/zerocheck PIOP with a multilinear PCS.
//!
//! This crate carries everything the verifier needs. It is portable — the NEON
//! kernels in `field`, `ntt`, `lincheck`, `zerocheck`, and `merkle` have scalar
//! fallbacks — though it is tuned for Apple silicon. The end-to-end prover, the
//! hash R1CS encoders, and the CLI live in the `flock-prover` crate built on
//! top of this one.
//!
//! Protocol flow:
//!   1. Prover commits to the witness z ∈ GF(2)^n via a multilinear PCS.
//!   2. Prover computes the row-witnesses a = A·z, b = B·z, c = C·z.
//!   3. Zerocheck PIOP reduces a·b ⊕ c = 0 to evaluation claims on (â, b̂, ĉ) at ρ.
//!   4. Lincheck PIOP reduces those to a single evaluation claim ẑ(ρ') = v.
//!   5. PCS opens ẑ at ρ'.
//!
//! Workspace-wide Clippy `allow`s for the hand-tuned numeric kernels are
//! declared in `[workspace.lints.clippy]` at the repo root.

#[cfg(not(feature = "std"))]
use std::prelude::v1::*;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! eprintln {
    ($($arg:tt)*) => {{
        let _ = core::format_args!($($arg)*);
    }};
}

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! println {
    ($($arg:tt)*) => {{
        let _ = core::format_args!($($arg)*);
    }};
}

#[cfg(not(feature = "std"))]
#[doc(hidden)]
pub mod std_compat {
    pub use alloc::{borrow, boxed, string, vec};
    pub use core::{
        array, cmp, convert, default, fmt, hash, hint, iter, marker, mem, ops, ptr, result, slice,
        str,
    };

    pub mod collections {
        pub use alloc::collections::{BTreeMap, BTreeSet};
        pub type HashMap<K, V> = BTreeMap<K, V>;
        pub type HashSet<T> = BTreeSet<T>;
    }

    pub mod env {
        use alloc::string::String;
        use core::fmt;

        #[derive(Debug, Clone, Copy)]
        pub struct VarError;

        impl fmt::Display for VarError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("environment variables are unavailable without std")
            }
        }

        pub fn var(_: &str) -> Result<String, VarError> {
            Err(VarError)
        }

        pub fn var_os(_: &str) -> Option<()> {
            None
        }
    }

    pub mod error {
        pub trait Error: super::fmt::Debug + super::fmt::Display {}
    }

    pub mod prelude {
        #[cfg(not(feature = "parallel"))]
        pub use crate::rayon_compat::{
            IntoParallelIterator, ParIter, ParallelSlice, ParallelSliceMut,
        };

        pub mod v1 {
            pub use alloc::boxed::Box;
            pub use alloc::string::{String, ToString};
            pub use alloc::vec::Vec;
            pub use core::clone::Clone;
            pub use core::cmp::{Eq, Ord, PartialEq, PartialOrd};
            pub use core::convert::{AsMut, AsRef, From, Into, TryFrom, TryInto};
            pub use core::default::Default;
            pub use core::iter::{DoubleEndedIterator, ExactSizeIterator, Extend, FromIterator};
            pub use core::marker::{Copy, Send, Sized, Sync, Unpin};
            pub use core::option::Option::{self, None, Some};
            pub use core::result::Result::{self, Err, Ok};
            pub use core::stringify;
            pub use core::todo;
            pub use core::unimplemented;
            pub use core::unreachable;
            pub use core::write;

            pub trait F64Ext {
                fn ceil(self) -> f64;
                fn exp2(self) -> f64;
                fn floor(self) -> f64;
                fn log2(self) -> f64;
                fn powf(self, n: f64) -> f64;
                fn powi(self, n: i32) -> f64;
                fn round(self) -> f64;
                fn sqrt(self) -> f64;
            }

            impl F64Ext for f64 {
                fn ceil(self) -> f64 {
                    libm::ceil(self)
                }

                fn exp2(self) -> f64 {
                    libm::exp2(self)
                }

                fn floor(self) -> f64 {
                    libm::floor(self)
                }

                fn log2(self) -> f64 {
                    libm::log2(self)
                }

                fn powf(self, n: f64) -> f64 {
                    libm::pow(self, n)
                }

                fn powi(self, n: i32) -> f64 {
                    libm::pow(self, n as f64)
                }

                fn round(self) -> f64 {
                    libm::round(self)
                }

                fn sqrt(self) -> f64 {
                    libm::sqrt(self)
                }
            }
        }
    }

    pub mod sync {
        pub use alloc::sync::Arc;
        use core::cell::UnsafeCell;
        use core::ops::{Deref, DerefMut};
        pub use core::sync::atomic;

        pub struct Mutex<T>(UnsafeCell<T>);
        pub struct MutexGuard<'a, T>(&'a mut T);

        unsafe impl<T: Send> Sync for Mutex<T> {}

        impl<T> Mutex<T> {
            pub const fn new(value: T) -> Self {
                Self(UnsafeCell::new(value))
            }

            pub fn lock(&self) -> Result<MutexGuard<'_, T>, ()> {
                Ok(MutexGuard(unsafe { &mut *self.0.get() }))
            }
        }

        impl<T> Deref for MutexGuard<'_, T> {
            type Target = T;

            fn deref(&self) -> &Self::Target {
                self.0
            }
        }

        impl<T> DerefMut for MutexGuard<'_, T> {
            fn deref_mut(&mut self) -> &mut Self::Target {
                self.0
            }
        }

        pub struct OnceLock<T>(UnsafeCell<Option<T>>);

        unsafe impl<T: Sync> Sync for OnceLock<T> {}

        impl<T: core::fmt::Debug> core::fmt::Debug for OnceLock<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple("OnceLock").field(&self.get()).finish()
            }
        }

        impl<T> Default for OnceLock<T> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<T> OnceLock<T> {
            pub const fn new() -> Self {
                Self(UnsafeCell::new(None))
            }

            pub fn get(&self) -> Option<&T> {
                unsafe { (&*self.0.get()).as_ref() }
            }

            pub fn set(&self, value: T) -> Result<(), T> {
                let slot = unsafe { &mut *self.0.get() };
                if slot.is_some() {
                    Err(value)
                } else {
                    *slot = Some(value);
                    Ok(())
                }
            }

            pub fn get_or_init<F: FnOnce() -> T>(&self, init: F) -> &T {
                let slot = unsafe { &mut *self.0.get() };
                if slot.is_none() {
                    *slot = Some(init());
                }
                slot.as_ref().unwrap()
            }
        }
    }

    pub mod thread {
        #[derive(Clone, Copy, Debug)]
        pub struct AvailableParallelism(usize);

        impl AvailableParallelism {
            pub fn get(self) -> usize {
                self.0
            }
        }

        pub fn available_parallelism() -> Result<AvailableParallelism, ()> {
            Ok(AvailableParallelism(1))
        }
    }

    pub mod time {
        use core::ops::{Add, AddAssign, Sub};

        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
        pub struct Duration {
            nanos: u128,
        }

        impl Duration {
            pub const ZERO: Self = Self { nanos: 0 };
            pub const MAX: Self = Self { nanos: u128::MAX };

            pub const fn from_secs(secs: u64) -> Self {
                Self {
                    nanos: secs as u128 * 1_000_000_000,
                }
            }

            pub const fn from_millis(millis: u64) -> Self {
                Self {
                    nanos: millis as u128 * 1_000_000,
                }
            }

            pub fn as_secs_f64(self) -> f64 {
                self.nanos as f64 / 1_000_000_000.0
            }

            pub fn as_millis(self) -> u128 {
                self.nanos / 1_000_000
            }
        }

        impl Add for Duration {
            type Output = Duration;

            fn add(self, rhs: Duration) -> Self::Output {
                Duration {
                    nanos: self.nanos.saturating_add(rhs.nanos),
                }
            }
        }

        impl AddAssign for Duration {
            fn add_assign(&mut self, rhs: Duration) {
                *self = *self + rhs;
            }
        }

        impl Sub for Duration {
            type Output = Duration;

            fn sub(self, rhs: Duration) -> Self::Output {
                Duration {
                    nanos: self.nanos.saturating_sub(rhs.nanos),
                }
            }
        }

        #[derive(Clone, Copy, Debug)]
        pub struct Instant;

        impl Instant {
            pub fn now() -> Self {
                Self
            }

            pub fn elapsed(self) -> Duration {
                Duration::ZERO
            }
        }
    }
}

#[cfg(not(feature = "std"))]
extern crate self as std;

#[cfg(not(feature = "std"))]
pub use std_compat::{
    array, borrow, boxed, cmp, collections, convert, default, env, error, fmt, hash, hint, iter,
    marker, mem, ops, prelude, ptr, result, slice, str, string, sync, thread, time, vec,
};

#[cfg(not(feature = "parallel"))]
#[doc(hidden)]
pub mod rayon_compat {
    pub struct ThreadPool;

    impl ThreadPool {
        pub fn install<R>(&self, op: impl FnOnce() -> R) -> R {
            op()
        }
    }

    pub struct ThreadPoolBuilder;

    impl ThreadPoolBuilder {
        pub fn new() -> Self {
            Self
        }

        pub fn num_threads(self, _: usize) -> Self {
            self
        }

        pub fn stack_size(self, _: usize) -> Self {
            self
        }

        pub fn thread_name<F, S>(self, _: F) -> Self
        where
            F: Fn(usize) -> S,
        {
            self
        }

        pub fn build(self) -> Result<ThreadPool, ()> {
            Ok(ThreadPool)
        }

        pub fn build_global(self) -> Result<(), ()> {
            Ok(())
        }
    }

    pub fn current_num_threads() -> usize {
        1
    }

    pub fn join<A, B, RA, RB>(a: A, b: B) -> (RA, RB)
    where
        A: FnOnce() -> RA,
        B: FnOnce() -> RB,
    {
        (a(), b())
    }

    pub mod prelude {
        pub use super::{IntoParallelIterator, ParIter, ParallelSlice, ParallelSliceMut};
    }

    pub struct ParIter<I>(I);

    impl<I: Iterator> Iterator for ParIter<I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }

    impl<I: Iterator> ParIter<I> {
        pub fn with_min_len(self, _: usize) -> Self {
            self
        }

        pub fn with_max_len(self, _: usize) -> Self {
            self
        }

        pub fn map<B, F>(self, f: F) -> ParIter<core::iter::Map<I, F>>
        where
            F: FnMut(I::Item) -> B,
        {
            ParIter(self.0.map(f))
        }

        pub fn flat_map_iter<U, F>(self, f: F) -> ParIter<core::iter::FlatMap<I, U, F>>
        where
            U: IntoIterator,
            F: FnMut(I::Item) -> U,
        {
            ParIter(self.0.flat_map(f))
        }

        pub fn zip<U>(self, other: U) -> ParIter<core::iter::Zip<I, U::IntoIter>>
        where
            U: IntoIterator,
        {
            ParIter(self.0.zip(other))
        }

        pub fn enumerate(self) -> ParIter<core::iter::Enumerate<I>> {
            ParIter(self.0.enumerate())
        }

        pub fn fold<Init, Acc, F>(self, init: Init, f: F) -> ParIter<core::iter::Once<Acc>>
        where
            Init: Fn() -> Acc,
            F: FnMut(Acc, I::Item) -> Acc,
        {
            ParIter(core::iter::once(self.0.fold(init(), f)))
        }

        pub fn for_each<F>(self, f: F)
        where
            F: FnMut(I::Item),
        {
            self.0.for_each(f);
        }

        pub fn for_each_init<Init, State, F>(self, init: Init, mut f: F)
        where
            Init: Fn() -> State,
            F: FnMut(&mut State, I::Item),
        {
            let mut state = init();
            for item in self.0 {
                f(&mut state, item);
            }
        }

        pub fn reduce<Init, F>(self, init: Init, f: F) -> I::Item
        where
            Init: Fn() -> I::Item,
            F: FnMut(I::Item, I::Item) -> I::Item,
        {
            self.0.fold(init(), f)
        }

        pub fn find_first<F>(mut self, f: F) -> Option<I::Item>
        where
            F: FnMut(&I::Item) -> bool,
        {
            self.0.find(f)
        }
    }

    pub trait IntoParallelIterator {
        type Item;
        type Iter: Iterator<Item = Self::Item>;

        fn into_par_iter(self) -> ParIter<Self::Iter>;
    }

    impl<T> IntoParallelIterator for T
    where
        T: IntoIterator,
    {
        type Item = T::Item;
        type Iter = T::IntoIter;

        fn into_par_iter(self) -> ParIter<Self::Iter> {
            ParIter(self.into_iter())
        }
    }

    pub trait ParallelSlice<T> {
        fn par_iter(&self) -> ParIter<core::slice::Iter<'_, T>>;
        fn par_chunks(&self, chunk_size: usize) -> ParIter<core::slice::Chunks<'_, T>>;
    }

    impl<T> ParallelSlice<T> for [T] {
        fn par_iter(&self) -> ParIter<core::slice::Iter<'_, T>> {
            ParIter(self.iter())
        }

        fn par_chunks(&self, chunk_size: usize) -> ParIter<core::slice::Chunks<'_, T>> {
            ParIter(self.chunks(chunk_size))
        }
    }

    pub trait ParallelSliceMut<T> {
        fn par_iter_mut(&mut self) -> ParIter<core::slice::IterMut<'_, T>>;
        fn par_chunks_mut(&mut self, chunk_size: usize) -> ParIter<core::slice::ChunksMut<'_, T>>;
    }

    impl<T> ParallelSliceMut<T> for [T] {
        fn par_iter_mut(&mut self) -> ParIter<core::slice::IterMut<'_, T>> {
            ParIter(self.iter_mut())
        }

        fn par_chunks_mut(&mut self, chunk_size: usize) -> ParIter<core::slice::ChunksMut<'_, T>> {
            ParIter(self.chunks_mut(chunk_size))
        }
    }
}

#[cfg(not(feature = "parallel"))]
extern crate self as rayon;

#[cfg(not(feature = "parallel"))]
pub use rayon_compat::{
    IntoParallelIterator, ParIter, ParallelSlice, ParallelSliceMut, ThreadPool, ThreadPoolBuilder,
    current_num_threads, join,
};

#[cfg(all(feature = "std", not(feature = "parallel")))]
pub mod prelude {
    pub use crate::rayon_compat::prelude::*;
}

#[cfg(all(feature = "std", target_os = "linux"))]
use std::collections::HashSet;
#[cfg(all(feature = "std", target_arch = "aarch64"))]
use std::sync::OnceLock;

pub mod bits;
pub mod challenger;
pub mod field;
pub mod linalg;
pub mod lincheck;
pub mod merkle;
pub mod ntt;
pub mod pcs;
pub mod permutation;
pub mod proof;
pub mod r1cs;
pub mod ro;
pub mod scratch;
#[cfg(feature = "symbolic")]
pub mod symbolic;
pub mod verifier;
pub mod zerocheck;
pub mod zk;

/// Configure rayon's global thread pool to use only performance cores on
/// Apple silicon (excluding efficiency cores).
///
/// On M-series chips the 2 efficiency cores run at ~30-40% of perf-core
/// speed and become stragglers in compute-bound parallel work — the
/// work-stealing scheduler keeps assigning them tasks that hold up the perf
/// cores at synchronization barriers. Empirically, 8 threads beats 10 by
/// ~10-20% on `pcs::commit` and similar parallel-NTT workloads.
///
/// Call this **once** at program startup, before any other parallel flock
/// code runs (rayon's global pool is set on first use; if it's already
/// created, this call is a no-op).
///
/// Respects `RAYON_NUM_THREADS` — if that env var is set, this function
/// does nothing (so explicit user configuration always wins).
///
/// Returns the number of threads the pool was configured with, or `None`
/// if no change was made (either because the env var was set or because
/// rayon was already initialized).
#[cfg(feature = "std")]
pub fn init_perf_thread_pool() -> Option<usize> {
    if std::env::var("RAYON_NUM_THREADS").is_ok() {
        return None;
    }
    let n = perf_core_count();
    match rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .build_global()
    {
        Ok(()) => Some(n),
        Err(_) => None, // pool already built
    }
}

#[cfg(not(feature = "std"))]
pub fn init_perf_thread_pool() -> Option<usize> {
    None
}

/// Allocate a `Vec<T>` of length `n` whose contents are NOT zero-initialized.
/// Caller MUST write every slot before reading it.
///
/// Used to skip the eager zero-init of large ping-pong buffers in hot prover
/// paths (PCS open, Round-2 fold, NTT scratch, lincheck packing). At m=29 the
/// zero-fill of a fresh 128 MB `vec![T::default(); n]` runs sequentially on
/// the main thread (~22 ms), which caps the parallel speedup of those phases.
///
/// `T: Copy` ensures `T` has no Drop impl, so the leaked uninitialized
/// elements are a no-op on drop.
///
/// # Safety contract
///
/// Reading uninitialized memory is UB per Rust's memory model regardless of
/// whether all bit patterns are valid for `T`. Caller must ensure every slot
/// is written before any read.
// `uninit_vec` flags exactly this pattern; here it is the deliberate purpose of
// the function (the safety contract above is what makes it sound).
#[allow(clippy::uninit_vec)]
pub(crate) fn alloc_uninit_vec<T: Copy>(n: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(n);
    // SAFETY:
    // - capacity == n was just allocated, so set_len(n) is in bounds.
    // - T: Copy implies !Drop, so leaking uninit elements is a no-op.
    // - Caller upholds write-before-read.
    unsafe {
        v.set_len(n);
    }
    v
}

/// Compatibility shim — same as `alloc_uninit_vec::<F128>(n)`.
pub(crate) fn alloc_uninit_f128_vec(n: usize) -> Vec<crate::field::F128> {
    alloc_uninit_vec::<crate::field::F128>(n)
}

/// Cached [`perf_core_count`]. The uncached version may spawn `sysctl`; this
/// memoizes it so hot paths can cheaply ask "is the current rayon pool the
/// homogeneous P-core pool?" (i.e. `current_num_threads() <= this`).
#[cfg(all(feature = "std", target_arch = "aarch64"))]
pub(crate) fn perf_core_count_cached() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(perf_core_count)
}

/// Best-effort count of **physical** performance cores used to size the
/// prover's thread pool. The hot phases are CLMUL-heavy and/or
/// memory-bandwidth-bound; SMT siblings share the core's execution ports and
/// add no DRAM bandwidth, so running 2 threads per physical core only adds
/// contention (on a 32C/64T Threadripper the prove is ~16% faster at 32 threads
/// than 64). On macOS, queries `hw.perflevel0.physicalcpu` (= P-core count on
/// Apple silicon, = physical CPU count on Intel). On Linux, `available_
/// parallelism()` counts SMT siblings, so derive physical cores from `/sys`
/// topology and clamp that host-wide count to the process's affinity/cgroup
/// availability. Elsewhere, falls back to `available_parallelism()`.
#[cfg(feature = "std")]
fn perf_core_count() -> usize {
    #[cfg(target_os = "macos")]
    {
        if let Ok(out) = std::process::Command::new("sysctl")
            .args(["-n", "hw.perflevel0.physicalcpu"])
            .output()
            && let Ok(s) = std::str::from_utf8(&out.stdout)
            && let Ok(n) = s.trim().parse::<usize>()
            && n > 0
        {
            return n;
        }
    }
    #[cfg(target_os = "linux")]
    {
        if let Some(n) = linux_physical_cores()
            && n > 0
        {
            let available = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1);
            return n.min(available);
        }
    }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

/// Count distinct physical cores via `/sys` topology: one entry per unique
/// `(physical_package_id, core_id)` over the online `cpuN` directories. Returns
/// `None` if the topology can't be read (caller falls back to logical count).
#[cfg(all(feature = "std", target_os = "linux"))]
fn linux_physical_cores() -> Option<usize> {
    let mut cores: HashSet<(String, String)> = HashSet::new();
    for entry in std::fs::read_dir("/sys/devices/system/cpu").ok()? {
        let Ok(entry) = entry else {
            continue;
        };
        let path = entry.path();
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        let Some(rest) = name.strip_prefix("cpu") else {
            continue;
        };
        if rest.is_empty() || !rest.bytes().all(|b| b.is_ascii_digit()) {
            continue; // skip "cpufreq", "cpuidle", etc.
        }
        let topo = path.join("topology");
        let core_id = std::fs::read_to_string(topo.join("core_id")).ok();
        let pkg = std::fs::read_to_string(topo.join("physical_package_id")).ok();
        if let (Some(c), Some(p)) = (core_id, pkg) {
            cores.insert((p.trim().to_owned(), c.trim().to_owned()));
        }
    }
    (!cores.is_empty()).then_some(cores.len())
}
