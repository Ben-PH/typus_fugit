use core::{cmp::Ordering, marker::PhantomData, ops};

use num_traits::PrimInt;
use typenum::{NonZero, Unsigned};

use crate::{
    duration::{Duration, Period},
    helpers::Helpers,
};

#[macro_use]
mod macros;

/// Represents an instant in time, measured as [`Duration`] since a start-reference.
#[derive(Clone, Copy, Debug)]
pub struct Instant<T, Numer, Denom>
where
    T: PrimInt,
    Denom: NonZero,
{
    /// Duration since start-reference
    pub since_start: Duration<T, Numer, Denom>,
}

impl_instant_for_integer!(u32);
impl_instant_for_integer!(u64);
impl<T, Numer, Denom> Instant<T, Numer, Denom>
where
    T: PrimInt,
    Denom: NonZero,
{
    /// Extract the ticks from an `Instant`.
    ///
    /// ```
    /// # use typus_fugit::*;
    /// let i = Instant::<_, typenum::U1, typenum::U1000>::from_ticks(234);
    ///
    /// assert_eq!(i.ticks(), 234);
    /// ```
    #[inline]
    pub const fn ticks(&self) -> T {
        self.since_start.ticks
    }

    /// Create an `Instant` from a ticks value.
    ///
    /// ```
    /// # use typus_fugit::*;
    /// let _i = Instant::<_, typenum::U1, typenum::U1000>::from_ticks(1);
    /// ```
    #[inline]
    pub const fn from_ticks(ticks: T) -> Self {
        Self {
            since_start: Duration {
                ticks,
                _period: Period {
                    _numer: PhantomData,
                    _denom: PhantomData,
                },
            },
        }
    }

    /// Duration between since the start of the `Instant`. This assumes an instant which
    /// won't wrap within the execution of the program.
    ///
    /// ```
    /// # use typus_fugit::*;
    /// let i = Instant::<_, typenum::U1, typenum::U1000>::from_ticks(11);
    ///
    /// assert_eq!(i.duration_since_epoch().ticks(), 11);
    /// ```
    #[inline]
    pub const fn duration_since_epoch(self) -> Duration<T, Numer, Denom> {
        self.since_start
    }
}

// Instant -= Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<ST, OT, Numer, Denom> ops::SubAssign<Duration<OT, Numer, Denom>> for Instant<ST, Numer, Denom>
where
    ST: PrimInt,
    OT: PrimInt,
    Self: ops::Sub<Duration<OT, Numer, Denom>, Output = Self>,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn sub_assign(&mut self, other: Duration<OT, Numer, Denom>) {
        *self = *self - other;
    }
}

// Instant += Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<ST, OT, Numer, Denom> ops::AddAssign<Duration<OT, Numer, Denom>> for Instant<ST, Numer, Denom>
where
    ST: PrimInt,
    OT: PrimInt,
    Self: ops::Add<Duration<OT, Numer, Denom>, Output = Self>,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn add_assign(&mut self, other: Duration<OT, Numer, Denom>) {
        *self = *self + other;
    }
}

//
// Operations between u32 Duration and u64 Instant
//

// Instant - Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<Numer, Denom> ops::Sub<Duration<u32, Numer, Denom>> for Instant<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
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

// Instant + Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<Numer, Denom> ops::Add<Duration<u32, Numer, Denom>> for Instant<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
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
