#![no_std]

extern crate alloc;

pub use alloc::{borrow, boxed, string, vec};
pub use core::{
    arch, array, cmp, convert, default, fmt, hash, hint, iter, marker, mem, ops, ptr, result,
    slice, str,
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
    pub use crate::{IntoParallelIterator, ParIter, ParallelSlice, ParallelSliceMut};

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
                fn positive_powi(mut base: f64, mut exp: u64) -> f64 {
                    let mut acc = 1.0;
                    while exp > 0 {
                        if exp & 1 == 1 {
                            acc *= base;
                        }
                        exp >>= 1;
                        if exp > 0 {
                            base *= base;
                        }
                    }
                    acc
                }

                let exp = n as i64;
                if exp < 0 {
                    1.0 / positive_powi(self, (-exp) as u64)
                } else {
                    positive_powi(self, exp as u64)
                }
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
    use core::sync::atomic::{AtomicBool, AtomicU8, Ordering};

    pub struct Mutex<T> {
        value: UnsafeCell<T>,
        locked: AtomicBool,
    }

    pub struct MutexGuard<'a, T> {
        mutex: &'a Mutex<T>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct MutexLockError;

    unsafe impl<T: Send> Sync for Mutex<T> {}

    impl<T> Mutex<T> {
        pub const fn new(value: T) -> Self {
            Self {
                value: UnsafeCell::new(value),
                locked: AtomicBool::new(false),
            }
        }

        pub fn lock(&self) -> Result<MutexGuard<'_, T>, MutexLockError> {
            if self
                .locked
                .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                return Err(MutexLockError);
            }
            Ok(MutexGuard { mutex: self })
        }
    }

    impl<T> Deref for MutexGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            unsafe { &*self.mutex.value.get() }
        }
    }

    impl<T> DerefMut for MutexGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { &mut *self.mutex.value.get() }
        }
    }

    impl<T> Drop for MutexGuard<'_, T> {
        fn drop(&mut self) {
            self.mutex.locked.store(false, Ordering::Release);
        }
    }

    pub struct OnceLock<T> {
        value: UnsafeCell<Option<T>>,
        state: AtomicU8,
    }

    unsafe impl<T: Send + Sync> Sync for OnceLock<T> {}

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
            Self {
                value: UnsafeCell::new(None),
                state: AtomicU8::new(0),
            }
        }

        pub fn get(&self) -> Option<&T> {
            if self.state.load(Ordering::Acquire) != 2 {
                return None;
            }
            unsafe { (&*self.value.get()).as_ref() }
        }

        pub fn set(&self, value: T) -> Result<(), T> {
            match self
                .state
                .compare_exchange(0, 1, Ordering::Acquire, Ordering::Acquire)
            {
                Ok(_) => {
                    unsafe {
                        *self.value.get() = Some(value);
                    }
                    self.state.store(2, Ordering::Release);
                    Ok(())
                }
                Err(_) => Err(value),
            }
        }

        pub fn get_or_init<F: FnOnce() -> T>(&self, init: F) -> &T {
            if let Some(value) = self.get() {
                return value;
            }
            match self
                .state
                .compare_exchange(0, 1, Ordering::Acquire, Ordering::Acquire)
            {
                Ok(_) => {
                    let value = init();
                    unsafe {
                        *self.value.get() = Some(value);
                    }
                    self.state.store(2, Ordering::Release);
                }
                Err(1) => {
                    while self.state.load(Ordering::Acquire) == 1 {
                        core::hint::spin_loop();
                    }
                }
                Err(2) => {}
                Err(_) => unreachable!(),
            }
            self.get().unwrap()
        }
    }
}

pub mod thread {
    #[derive(Clone, Copy, Debug)]
    pub struct AvailableParallelism(usize);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct AvailableParallelismError;

    impl AvailableParallelism {
        pub fn get(self) -> usize {
            self.0
        }
    }

    pub fn available_parallelism() -> Result<AvailableParallelism, AvailableParallelismError> {
        Ok(AvailableParallelism(1))
    }
}

pub mod time {
    use core::iter::Sum;
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

        pub fn as_nanos(self) -> u128 {
            self.nanos
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

    impl Sum for Duration {
        fn sum<I: Iterator<Item = Duration>>(iter: I) -> Self {
            iter.fold(Duration::ZERO, Add::add)
        }
    }

    impl<'a> Sum<&'a Duration> for Duration {
        fn sum<I: Iterator<Item = &'a Duration>>(iter: I) -> Self {
            iter.copied().sum()
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

pub struct ThreadPool;

impl ThreadPool {
    pub fn install<R>(&self, op: impl FnOnce() -> R) -> R {
        op()
    }
}

pub struct ThreadPoolBuilder;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ThreadPoolBuildError;

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

    pub fn build(self) -> Result<ThreadPool, ThreadPoolBuildError> {
        Ok(ThreadPool)
    }

    pub fn build_global(self) -> Result<(), ThreadPoolBuildError> {
        Ok(())
    }
}

impl Default for ThreadPoolBuilder {
    fn default() -> Self {
        Self::new()
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

#[cfg(test)]
extern crate std as real_std;

#[cfg(test)]
mod tests {
    use super::prelude::*;
    use super::sync::{Mutex, OnceLock};
    use super::time::Duration;
    use real_std::vec;

    #[test]
    fn mutex_rejects_reentrant_lock() {
        let mutex = Mutex::new(7usize);
        let _guard = mutex.lock().unwrap();
        assert!(mutex.lock().is_err());
    }

    #[test]
    fn once_lock_initializes_once() {
        let cell = OnceLock::new();
        assert_eq!(*cell.get_or_init(|| 11), 11);
        assert_eq!(*cell.get_or_init(|| 12), 11);
        assert_eq!(cell.set(13), Err(13));
    }

    #[test]
    fn serial_parallel_iter_matches_iterator_order() {
        let values = vec![1usize, 2, 3, 4, 5];
        let reduced = values
            .clone()
            .into_par_iter()
            .map(|x| x * 2)
            .fold(|| 0, |acc, x| acc + x)
            .reduce(|| 0, |a, b| a + b);
        assert_eq!(reduced, 30);
        assert_eq!(values.into_par_iter().find_first(|x| *x == 3), Some(3));
    }

    #[test]
    fn for_each_init_reuses_single_state() {
        let mut out = vec![0usize; 3];
        out.par_iter_mut().enumerate().for_each_init(
            || 10usize,
            |state, (i, slot)| {
                *slot = *state + i;
                *state += 10;
            },
        );
        assert_eq!(out, vec![10, 21, 32]);
    }

    #[test]
    fn duration_saturates_and_sums() {
        assert_eq!(
            (Duration::MAX + Duration::from_secs(1)).as_nanos(),
            u128::MAX
        );
        assert_eq!(
            (Duration::from_secs(1) - Duration::from_secs(2)).as_nanos(),
            0
        );
        let total: Duration = [Duration::from_millis(1), Duration::from_millis(2)]
            .iter()
            .sum();
        assert_eq!(total.as_millis(), 3);
    }
}
