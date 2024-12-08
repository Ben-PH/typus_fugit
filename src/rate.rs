use core::{cmp::Ordering, convert, marker::PhantomData, ops};

use num_traits::PrimInt;
use typenum::{NonZero, Unsigned, U1, U1000, U1000000};

use crate::{helpers::Helpers, Duration};

#[macro_use]
mod macros;

/// Represents a frequency.
///
/// The generic `T` can either be `u32` or `u64`, and the const generics represent the ratio of the
/// raw contained within the rate: `rate in Hz = Numer / Denom * raw`
#[derive(Clone, Copy, Debug)]
pub struct Rate<T, Numer, Denom>
where
    T: PrimInt,
    Denom: Unsigned + NonZero,
{
    pub(crate) raw: T,
    _numer: PhantomData<Numer>,
    _denom: PhantomData<Denom>,
}

impl_rate_for_integer!(u32);
impl_rate_for_integer!(u64);

impl<T, Numer, Denom> Rate<T, Numer, Denom>
where
    T: PrimInt,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    /// Create a `Rate` from a raw value.
    ///
    /// ```
    /// # use typus_fugit::*;
    /// let _d = Rate::<_, typenum::U1, typenum::U1000>::from_raw(1);
    /// ```
    #[inline]
    pub const fn from_raw(raw: T) -> Self {
        Rate {
            raw,
            _numer: PhantomData,
            _denom: PhantomData,
        }
    }

    /// Extract the raw value from a `Rate`.
    ///
    /// ```
    /// # use typus_fugit::*;
    /// let d = Rate::<_, typenum::U1, typenum::U1000>::from_raw(234);
    ///
    /// assert_eq!(d.raw(), 234);
    /// ```
    #[inline]
    pub const fn raw(&self) -> T {
        self.raw
    }
}
// Rate - Rate = Rate (only same base until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<ST, OT, Numer, Denom> ops::Sub<Rate<OT, Numer, Denom>> for Rate<ST, Numer, Denom>
where
    ST: PrimInt + From<OT>,
    OT: PrimInt,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Output = Rate<ST, Numer, Denom>;

    #[inline]
    fn sub(self, other: Rate<OT, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.raw.checked_sub(&other.raw.into()) {
            Self {
                raw: v,
                _numer: PhantomData,
                _denom: PhantomData,
            }
        } else {
            panic!("Sub failed!");
        }
    }
}

// Rate + Rate = Rate (only same base until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<ST, OT, Numer, Denom> ops::Add<Rate<OT, Numer, Denom>> for Rate<ST, Numer, Denom>
where
    ST: PrimInt + From<OT>,
    OT: PrimInt,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Output = Rate<ST, Numer, Denom>;

    #[inline]
    fn add(self, other: Rate<OT, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.raw.checked_add(&other.raw.into()) {
            Self {
                raw: v,
                _numer: PhantomData,
                _denom: PhantomData,
            }
        } else {
            panic!("Add failed!");
        }
    }
}

// Rate += Rate
impl<ST, OT, Numer, Denom> ops::AddAssign<Rate<OT, Numer, Denom>> for Rate<ST, Numer, Denom>
where
    ST: PrimInt + From<OT>,
    OT: PrimInt,
    Self: ops::Add<Rate<OT, Numer, Denom>, Output = Self>,
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn add_assign(&mut self, other: Rate<OT, Numer, Denom>) {
        *self = *self + other;
    }
}
//
// Operations between u32 and u64 Rate
//

impl<Numer, Denom> From<Rate<u32, Numer, Denom>> for Rate<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn from(val: Rate<u32, Numer, Denom>) -> Rate<u64, Numer, Denom> {
        Rate::<u64, Numer, Denom>::from_raw(val.raw() as u64)
    }
}

impl<Numer, Denom> convert::TryFrom<Rate<u64, Numer, Denom>> for Rate<u32, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    type Error = ();

    #[inline]
    fn try_from(val: Rate<u64, Numer, Denom>) -> Result<Rate<u32, Numer, Denom>, ()> {
        Ok(Rate::<u32, Numer, Denom>::from_raw(
            val.raw().try_into().map_err(|_| ())?,
        ))
    }
}

// Rate -= Rate (to make shorthands work, until const_generics_defaults is stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer, Denom> ops::SubAssign<Rate<u32, Numer, Denom>> for Rate<u64, Numer, Denom>
where
    Numer: Unsigned,
    Denom: Unsigned + NonZero,
{
    #[inline]
    fn sub_assign(&mut self, other: Rate<u32, Numer, Denom>) {
        *self = *self - other;
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialOrd<Rate<u32, RNumer, RDenom>>
    for Rate<u64, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u32, RNumer, RDenom>) -> Option<Ordering> {
        self.partial_cmp(&Rate::<u64, RNumer, RDenom>::from_raw(other.raw() as u64))
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialEq<Rate<u32, RNumer, RDenom>>
    for Rate<u64, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn eq(&self, other: &Rate<u32, RNumer, RDenom>) -> bool {
        self.eq(&Rate::<u64, RNumer, RDenom>::from_raw(other.raw() as u64))
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialOrd<Rate<u64, RNumer, RDenom>>
    for Rate<u32, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u64, RNumer, RDenom>) -> Option<Ordering> {
        Rate::<u64, LNumer, LDenom>::from_raw(self.raw as u64).partial_cmp(other)
    }
}

impl<LNumer, LDenom, RNumer, RDenom> PartialEq<Rate<u64, RNumer, RDenom>>
    for Rate<u32, LNumer, LDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    #[inline]
    fn eq(&self, other: &Rate<u64, RNumer, RDenom>) -> bool {
        Rate::<u64, LNumer, LDenom>::from_raw(self.raw as u64).eq(other)
    }
}

/// Extension trait for simple short-hands for u32 Rate
pub trait ExtU32 {
    /// Shorthand for creating a rate which represents hertz.
    #[allow(non_snake_case)]
    fn Hz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a rate which represents kilohertz.
    #[allow(non_snake_case)]
    fn kHz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a rate which represents megahertz.
    #[allow(non_snake_case)]
    fn MHz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU32 for u32 {
    #[inline]
    #[allow(non_snake_case)]
    fn Hz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u32, Numer, Denom>::Hz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn kHz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u32, Numer, Denom>::kHz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn MHz<Numer, Denom>(self) -> Rate<u32, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u32, Numer, Denom>::MHz(self)
    }
}

/// Extension trait for simple short-hands for u64 Rate
pub trait ExtU64 {
    /// Shorthand for creating a rate which represents hertz.
    #[allow(non_snake_case)]
    fn Hz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a rate which represents kilohertz.
    #[allow(non_snake_case)]
    fn kHz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;

    /// Shorthand for creating a rate which represents megahertz.
    #[allow(non_snake_case)]
    fn MHz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero;
}

impl ExtU64 for u64 {
    #[inline]
    #[allow(non_snake_case)]
    fn Hz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u64, Numer, Denom>::Hz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn kHz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u64, Numer, Denom>::kHz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn MHz<Numer, Denom>(self) -> Rate<u64, Numer, Denom>
    where
        Numer: Unsigned,
        Denom: Unsigned + NonZero,
    {
        Rate::<u64, Numer, Denom>::MHz(self)
    }
}
