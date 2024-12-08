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
pub struct Instant<T: PrimInt, Numer, Denom: NonZero> {
    /// Duration since start-reference
    pub since_start: Duration<T, Numer, Denom>,
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

// Instant -= Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<Numer, Denom> ops::SubAssign<Duration<u32, Numer, Denom>> for Instant<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
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

// Instant += Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<Numer, Denom> ops::AddAssign<Duration<u32, Numer, Denom>> for Instant<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
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
