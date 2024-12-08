use core::{cmp::Ordering, convert, marker::PhantomData, ops};

use num_traits::PrimInt;
use typenum::{NonZero, Unsigned, U100, U36};

use crate::{helpers::Helpers, Rate};

mod period;
pub use period::Period;

#[macro_use]
mod macros;

/// Represents a duration of time.
///
/// The generic `T` can either be `u32` or `u64`, typenums represent the Period in seconds
/// Duration in seconds is calculated as `Numer / Denom * ticks`
#[derive(Clone, Copy, Debug)]
pub struct Duration<T: PrimInt, Numer, Denom: NonZero> {
    pub(crate) ticks: T,
    pub(crate) _period: Period<Numer, Denom>,
}
impl_duration_for_integer!(u32);
impl_duration_for_integer!(u64);

//
// Operations between u32 and u64 Durations
//

impl<Numer, Denom> From<Duration<u32, Numer, Denom>> for Duration<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn from(val: Duration<u32, Numer, Denom>) -> Duration<u64, Numer, Denom> {
        Duration::<u64, Numer, Denom>::from_ticks(val.ticks() as u64)
    }
}

impl<Numer, Denom> convert::TryFrom<Duration<u64, Numer, Denom>> for Duration<u32, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Error = ();

    #[inline]
    fn try_from(val: Duration<u64, Numer, Denom>) -> Result<Duration<u32, Numer, Denom>, ()> {
        Ok(Duration::<u32, Numer, Denom>::from_ticks(
            val.ticks().try_into().map_err(|_| ())?,
        ))
    }
}

// Duration - Duration = Duration (to make shorthands work, until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer, Denom> ops::Sub<Duration<u32, Numer, Denom>> for Duration<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Output = Duration<u64, Numer, Denom>;

    #[inline]
    fn sub(self, other: Duration<u32, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_sub(Duration::<u64, Numer, Denom>::from_ticks(
            other.ticks() as u64
        )) {
            v
        } else {
            panic!("Sub failed!");
        }
    }
}

// Duration -= Duration (to make shorthands work, until const_generics_defaults is stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer, Denom> ops::SubAssign<Duration<u32, Numer, Denom>> for Duration<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn sub_assign(&mut self, other: Duration<u32, Numer, Denom>) {
        *self = *self - other;
    }
}

// Duration + Duration = Duration (to make shorthands work, until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer, Denom> ops::Add<Duration<u32, Numer, Denom>> for Duration<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Output = Duration<u64, Numer, Denom>;

    #[inline]
    fn add(self, other: Duration<u32, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_add(Duration::<u64, Numer, Denom>::from_ticks(
            other.ticks() as u64
        )) {
            v
        } else {
            panic!("Add failed!");
        }
    }
}

// Duration += Duration (to make shorthands work, until const_generics_defaults is stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer, Denom> ops::AddAssign<Duration<u32, Numer, Denom>> for Duration<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn add_assign(&mut self, other: Duration<u32, Numer, Denom>) {
        *self = *self + other;
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialOrd<Duration<u32, RNumer, RDenom>>
    for Duration<u64, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn partial_cmp(&self, other: &Duration<u32, RNumer, RDenom>) -> Option<Ordering> {
        self.partial_cmp(&Duration::<u64, RNumer, RDenom>::from_ticks(
            other.ticks() as u64
        ))
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialEq<Duration<u32, RNumer, RDenom>>
    for Duration<u64, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn eq(&self, other: &Duration<u32, RNumer, RDenom>) -> bool {
        self.eq(&Duration::<u64, RNumer, RDenom>::from_ticks(
            other.ticks() as u64
        ))
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialOrd<Duration<u64, RNumer, RDenom>>
    for Duration<u32, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn partial_cmp(&self, other: &Duration<u64, RNumer, RDenom>) -> Option<Ordering> {
        Duration::<u64, LNumer, LDenom>::from_ticks(self.ticks as u64).partial_cmp(other)
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialEq<Duration<u64, RNumer, RDenom>>
    for Duration<u32, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn eq(&self, other: &Duration<u64, RNumer, RDenom>) -> bool {
        Duration::<u64, LNumer, LDenom>::from_ticks(self.ticks as u64).eq(other)
    }
}

/// Extension trait for simple short-hands for u32 Durations
pub trait ExtU32 {
    /// Shorthand for creating a duration which represents nanoseconds.
    fn nanos<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents microseconds.
    fn micros<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents milliseconds.
    fn millis<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents seconds.
    fn secs<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents minutes.
    fn minutes<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents hours.
    fn hours<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU32 for u32 {
    #[inline]
    fn nanos<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::nanos(self)
    }

    #[inline]
    fn micros<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::micros(self)
    }

    #[inline]
    fn millis<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::millis(self)
    }

    #[inline]
    fn secs<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::secs(self)
    }

    #[inline]
    fn minutes<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::minutes(self)
    }

    #[inline]
    fn hours<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::hours(self)
    }
}

/// Extension trait for simple short-hands for u32 Durations (ceil rounded)
pub trait ExtU32Ceil {
    /// Shorthand for creating a duration which represents nanoseconds.
    fn nanos_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents microseconds.
    fn micros_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents milliseconds.
    fn millis_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents seconds.
    fn secs_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents minutes.
    fn minutes_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents hours.
    fn hours_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU32Ceil for u32 {
    #[inline]
    fn nanos_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::nanos_at_least(self)
    }

    #[inline]
    fn micros_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::micros_at_least(self)
    }

    #[inline]
    fn millis_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::millis_at_least(self)
    }

    #[inline]
    fn secs_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::secs_at_least(self)
    }

    #[inline]
    fn minutes_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::minutes_at_least(self)
    }

    #[inline]
    fn hours_at_least<Numer, Denom>(self) -> Duration<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u32, Numer, Denom>::hours_at_least(self)
    }
}

/// Extension trait for simple short-hands for u64 Durations
pub trait ExtU64 {
    /// Shorthand for creating a duration which represents nanoseconds.
    fn nanos<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents microseconds.
    fn micros<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents milliseconds.
    fn millis<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents seconds.
    fn secs<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents minutes.
    fn minutes<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents hours.
    fn hours<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU64 for u64 {
    #[inline]
    fn nanos<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::nanos(self)
    }

    #[inline]
    fn micros<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::micros(self)
    }

    #[inline]
    fn millis<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::millis(self)
    }

    #[inline]
    fn secs<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::secs(self)
    }

    #[inline]
    fn minutes<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::minutes(self)
    }

    #[inline]
    fn hours<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::hours(self)
    }
}

/// Extension trait for simple short-hands for u64 Durations (ceil rounded)
pub trait ExtU64Ceil {
    /// Shorthand for creating a duration which represents nanoseconds.
    fn nanos_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents microseconds.
    fn micros_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents milliseconds.
    fn millis_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents seconds.
    fn secs_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents minutes.
    fn minutes_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a duration which represents hours.
    fn hours_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU64Ceil for u64 {
    #[inline]
    fn nanos_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::nanos_at_least(self)
    }

    #[inline]
    fn micros_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::micros_at_least(self)
    }

    #[inline]
    fn millis_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::millis_at_least(self)
    }

    #[inline]
    fn secs_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::secs_at_least(self)
    }

    #[inline]
    fn minutes_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::minutes_at_least(self)
    }

    #[inline]
    fn hours_at_least<Numer, Denom>(self) -> Duration<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Duration::<u64, Numer, Denom>::hours_at_least(self)
    }
}
