use crate::duration::Duration;
use crate::helpers::Helpers;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops;
use typenum::{NonZero, Unsigned};

/// Represents an instant in time.
///
/// The generic `T` can either be `u32` or `u64`, and the const generics represent the ratio of the
/// ticks contained within the instant: `instant in seconds = Numer / Denom * ticks`
#[derive(Clone, Copy, Debug)]
pub struct Instant<T, Numer, Denom> {
    ticks: T,
    _numer: PhantomData<Numer>,
    _denom: PhantomData<Denom>,
}

macro_rules! impl_instant_for_integer {
    ($i:ty) => {
        impl<Numer, Denom> Instant<$i, Numer, Denom> {
            /// Extract the ticks from an `Instant`.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(234);")]
            ///
            /// assert_eq!(i.ticks(), 234);
            /// ```
            #[inline]
            pub const fn ticks(&self) -> $i {
                self.ticks
            }

        }
        impl<Numer: Unsigned, Denom: Unsigned + NonZero> Instant<$i, Numer, Denom> {
            /// Create an `Instant` from a ticks value.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let _i = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            /// ```
            #[inline]
            pub const fn from_ticks(ticks: $i) -> Self {
                Instant { ticks, _numer: PhantomData, _denom: PhantomData  }
            }

            /// Const comparison of `Instant`s.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
            ///
            /// assert_eq!(i1.const_cmp(i2), core::cmp::Ordering::Less);
            /// ```
            ///
            /// This function takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed:
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(", stringify!($i),"::MAX);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            ///
            /// assert_eq!(i1.const_cmp(i2), core::cmp::Ordering::Less);
            /// ```
            #[inline]
            pub const fn const_cmp(self, other: Self) -> Ordering {
                if self.ticks == other.ticks {
                    Ordering::Equal
                } else {
                    let v = self.ticks.wrapping_sub(other.ticks);

                    // not using `v.cmp(<$i>::MAX / 2).reverse()` due to `cmp` being non-const
                    if v > <$i>::MAX / 2 {
                        Ordering::Less
                    } else if v < <$i>::MAX / 2 {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            /// Duration between since the start of the `Instant`. This assumes an instant which
            /// won't wrap within the execution of the program.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(11);")]
            ///
            /// assert_eq!(i.duration_since_epoch().ticks(), 11);
            /// ```
            #[inline]
            pub const fn duration_since_epoch(self) -> Duration<$i, Numer, Denom> {
                Duration::<$i, Numer, Denom>::from_ticks(self.ticks())
            }

            /// Duration between `Instant`s.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
            ///
            /// assert_eq!(i1.checked_duration_since(i2), None);
            /// assert_eq!(i2.checked_duration_since(i1).unwrap().ticks(), 1);
            /// ```
            #[inline]
            pub const fn checked_duration_since(
                self,
                other: Self,
            ) -> Option<Duration<$i, Numer, Denom>> {
                match self.const_cmp(other) {
                    Ordering::Greater | Ordering::Equal => {
                        Some(Duration::<$i, Numer, Denom>::from_ticks(
                            self.ticks.wrapping_sub(other.ticks),
                        ))
                    }
                    Ordering::Less => None,
                }
            }

            /// Subtract a `Duration` from an `Instant` while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            #[doc = concat!("let d = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            ///
            /// assert_eq!(i.checked_sub_duration(d).unwrap().ticks(), 0);
            /// ```
            pub const fn checked_sub_duration<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
                self,
                other: Duration<$i, ONumer, ODenom>,
            ) -> Option<Self> {
                if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
                    Some(Instant::<$i, Numer, Denom>::from_ticks(
                        self.ticks.wrapping_sub(other.ticks()),
                    ))
                } else {
                    if let Some(lh) = other
                        .ticks()
                        .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                        Some(Instant::<$i, Numer, Denom>::from_ticks(
                            self.ticks.wrapping_sub(ticks),
                        ))
                    } else {
                        None
                    }
                }
            }

            /// Add a `Duration` to an `Instant` while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            #[doc = concat!("let d = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
            ///
            /// assert_eq!(i.checked_add_duration(d).unwrap().ticks(), 2);
            /// ```
            pub const fn checked_add_duration<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
                self,
                other: Duration<$i, ONumer, ODenom>,
            ) -> Option<Self> {
                if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
                    Some(Instant::<$i, Numer, Denom>::from_ticks(
                        self.ticks.wrapping_add(other.ticks()),
                    ))
                } else {
                    if let Some(lh) = other
                        .ticks()
                        .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                        Some(Instant::<$i, Numer, Denom>::from_ticks(
                            self.ticks.wrapping_add(ticks),
                        ))
                    } else {
                        None
                    }
                }
            }
        }

        impl<Numer:Unsigned, Denom: Unsigned + NonZero> PartialOrd for Instant<$i, Numer, Denom> {
            /// This implementation deviates from the definition of
            /// [PartialOrd::partial_cmp](core::cmp::PartialOrd::partial_cmp):
            ///
            /// It takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed.
            ///
            /// That breaks the transitivity invariant: a < b and b < c no longer implies a < c.
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.const_cmp(*other))
            }
        }

        impl<Numer:Unsigned, Denom: Unsigned + NonZero> Ord for Instant<$i, Numer, Denom> {
            /// This implementation deviates from the definition of
            /// [Ord::cmp](core::cmp::Ord::cmp):
            ///
            /// It takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed.
            ///
            /// That breaks the transitivity invariant: a < b and b < c no longer implies a < c.
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.const_cmp(*other)
            }
        }

        impl<Numer:Unsigned, Denom: Unsigned + NonZero> PartialEq for Instant<$i, Numer, Denom> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                self.ticks.eq(&other.ticks)
            }
        }

        impl<Numer:Unsigned, Denom: Unsigned + NonZero> Eq for Instant<$i, Numer, Denom> {}

        // Instant - Instant = Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_duration_since`.
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> ops::Sub<Instant<$i, Numer, Denom>>
            for Instant<$i, Numer, Denom>
        {
            type Output = Duration<$i, Numer, Denom>;

            #[inline]
            fn sub(self, other: Self) -> Self::Output {
                if let Some(v) = self.checked_duration_since(other) {
                    v
                } else {
                    panic!("Sub failed! Other > self");
                }
            }
        }

        // Instant - Duration = Instant
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_sub_duration`.
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> ops::Sub<Duration<$i, Numer, Denom>>
            for Instant<$i, Numer, Denom>
        {
            type Output = Instant<$i, Numer, Denom>;

            #[inline]
            fn sub(self, other: Duration<$i, Numer, Denom>) -> Self::Output {
                if let Some(v) = self.checked_sub_duration(other) {
                    v
                } else {
                    panic!("Sub failed! Overflow");
                }
            }
        }

        // Instant -= Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_sub_duration`.
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> ops::SubAssign<Duration<$i, Numer, Denom>>
            for Instant<$i, Numer, Denom>
        {
            #[inline]
            fn sub_assign(&mut self, other: Duration<$i, Numer, Denom>) {
                *self = *self - other;
            }
        }

        // Instant + Duration = Instant
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_add_duration`.
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> ops::Add<Duration<$i, Numer, Denom>>
            for Instant<$i, Numer, Denom>
        {
            type Output = Instant<$i, Numer, Denom>;

            #[inline]
            fn add(self, other: Duration<$i, Numer, Denom>) -> Self::Output {
                if let Some(v) = self.checked_add_duration(other) {
                    v
                } else {
                    panic!("Add failed! Overflow");
                }
            }
        }

        // Instant += Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_add_duration`.
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> ops::AddAssign<Duration<$i, Numer, Denom>>
            for Instant<$i, Numer, Denom>
        {
            #[inline]
            fn add_assign(&mut self, other: Duration<$i, Numer, Denom>) {
                *self = *self + other;
            }
        }

        #[cfg(feature = "defmt")]
        impl<Numer:Unsigned, Denom: Unsigned + NonZero> defmt::Format for Instant<$i, Numer, Denom> {
            fn format(&self, f: defmt::Formatter) {
                if Numer == 3_600 && Denom == 1 {
                    defmt::write!(f, "{} h", self.ticks)
                } else if Numer == 60 && Denom == 1 {
                    defmt::write!(f, "{} min", self.ticks)
                } else if Numer == 1 && Denom == 1 {
                    defmt::write!(f, "{} s", self.ticks)
                } else if Numer == 1 && Denom == 1_000 {
                    defmt::write!(f, "{} ms", self.ticks)
                } else if Numer == 1 && Denom == 1_000_000 {
                    defmt::write!(f, "{} us", self.ticks)
                } else if Numer == 1 && Denom == 1_000_000_000 {
                    defmt::write!(f, "{} ns", self.ticks)
                } else {
                    defmt::write!(f, "{} ticks @ ({}/{})", self.ticks, Numer, Denom)
                }
            }
        }

        impl<Numer:Unsigned, Denom: Unsigned + NonZero> core::fmt::Display for Instant<$i, Numer, Denom> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if Numer::U64 == 3_600 && Denom::U64 == 1 {
                    write!(f, "{} h", self.ticks)
                } else if Numer::U64 == 60 && Denom::U64 == 1 {
                    write!(f, "{} min", self.ticks)
                } else if Numer::U64 == 1 && Denom::U64 == 1 {
                    write!(f, "{} s", self.ticks)
                } else if Numer::U64 == 1 && Denom::U64 == 1_000 {
                    write!(f, "{} ms", self.ticks)
                } else if Numer::U64 == 1 && Denom::U64 == 1_000_000 {
                    write!(f, "{} μs", self.ticks)
                } else if Numer::U64 == 1 && Denom::U64 == 1_000_000_000 {
                    write!(f, "{} ns", self.ticks)
                } else {
                    write!(f, "{} ticks @ ({}/{})", self.ticks, Numer::U64, Denom::U64)
                }
            }
        }
    };
}

impl_instant_for_integer!(u32);
impl_instant_for_integer!(u64);

//
// Operations between u32 Duration and u64 Instant
//

// Instant - Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::Sub<Duration<u32, Numer, Denom>>
    for Instant<u64, Numer, Denom>
{
    type Output = Instant<u64, Numer, Denom>;

    #[inline]
    fn sub(self, other: Duration<u32, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_sub_duration(other.into()) {
            v
        } else {
            panic!("Sub failed! Overflow");
        }
    }
}

// Instant -= Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::SubAssign<Duration<u32, Numer, Denom>>
    for Instant<u64, Numer, Denom>
{
    #[inline]
    fn sub_assign(&mut self, other: Duration<u32, Numer, Denom>) {
        *self = *self - other;
    }
}

// Instant + Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::Add<Duration<u32, Numer, Denom>>
    for Instant<u64, Numer, Denom>
{
    type Output = Instant<u64, Numer, Denom>;

    #[inline]
    fn add(self, other: Duration<u32, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_add_duration(other.into()) {
            v
        } else {
            panic!("Add failed! Overflow");
        }
    }
}

// Instant += Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::AddAssign<Duration<u32, Numer, Denom>>
    for Instant<u64, Numer, Denom>
{
    #[inline]
    fn add_assign(&mut self, other: Duration<u32, Numer, Denom>) {
        *self = *self + other;
    }
}

// impl<LNumer: Unsigned, LDenom: Unsigned + NonZero, RNumer: Unsigned, RDenom: Unsigned + NonZero>
//     ops::Add<Duration<u32, RNumer, RDenom>> for Duration<u64, LNumer, LDenom>
// {
//     type Output = Duration<u64, LNumer, LDenom>;
// 
//     #[inline]
//     fn add(self, other: Duration<u32, RNumer, RDenom>) -> Self::Output {
//         self.add(Duration::<u64, LNumer, LDenom>::from_ticks(
//             other.ticks() as u64
//         ))
//     }
// }
