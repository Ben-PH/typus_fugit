macro_rules! impl_instant_for_integer {
    ($i:ty) => {
impl<Numer: Unsigned, Denom: Unsigned + NonZero> Instant<$i, Numer, Denom> {
    /// Const comparison of `Instant`s.
    ///
    /// ```
    /// # use typus_fugit::*;
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
    /// # use typus_fugit::*;
    #[doc = concat!("let i1 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(", stringify!($i),"::MAX);")]
    #[doc = concat!("let i2 = Instant::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
    ///
    /// assert_eq!(i1.const_cmp(i2), core::cmp::Ordering::Less);
    /// ```
    #[inline]
    pub const fn const_cmp(self, other: Self) -> Ordering {
        if self.since_start.ticks == other.since_start.ticks {
            Ordering::Equal
        } else {
            let v = self.since_start.ticks.wrapping_sub(other.since_start.ticks);

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

    /// Duration between `Instant`s.
    ///
    /// ```
    /// # use typus_fugit::*;
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
                    self.since_start.ticks.wrapping_sub(other.since_start.ticks),
                ))
            }
            Ordering::Less => None,
        }
    }

    /// Subtract a `Duration` from an `Instant` while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
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
                self.since_start.ticks.wrapping_sub(other.ticks()),
            ))
        } else {
            if let Some(lh) = other
                .ticks()
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                Some(Instant::<$i, Numer, Denom>::from_ticks(
                    self.since_start.ticks.wrapping_sub(ticks),
                ))
            } else {
                None
            }
        }
    }

    /// Add a `Duration` to an `Instant` while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
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
                self.since_start.ticks.wrapping_add(other.ticks()),
            ))
        } else {
            if let Some(lh) = other
                .ticks()
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                Some(Instant::<$i, Numer, Denom>::from_ticks(
                    self.since_start.ticks.wrapping_add(ticks),
                ))
            } else {
                None
            }
        }
    }
}

impl<Numer:Unsigned, Denom: Unsigned + NonZero> PartialOrd for Instant<$i, Numer, Denom> {
    /// This implementation deviates from the definition of
    /// [`PartialOrd::partial_cmp`](core::cmp::PartialOrd::partial_cmp):
    ///
    /// It takes into account that ticks might wrap around. If the absolute
    /// values of `self` and `other` differ by more than half the possible range, it is
    /// assumed that an overflow occured and the result is reversed.
    ///
    /// That breaks the transitivity invariant: a < b and b < c no longer implies a < c.
    #[allow(clippy::non_canonical_partial_ord_impl)]
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.const_cmp(*other))
    }
}

impl<Numer:Unsigned, Denom: Unsigned + NonZero> Ord for Instant<$i, Numer, Denom> {
    /// This implementation deviates from the definition of
    /// [`Ord::cmp`](core::cmp::Ord::cmp):
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
        self.since_start.ticks.eq(&other.since_start.ticks)
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

#[cfg(feature = "defmt")]
impl<Numer:Unsigned, Denom: Unsigned + NonZero> defmt::Format for Instant<$i, Numer, Denom> {
    fn format(&self, f: defmt::Formatter) {
        if Numer::U64 == 3_600 && Denom::U64 == 1 {
            defmt::write!(f, "{} h", self.since_start.ticks)
        } else if Numer::U64 == 60 && Denom::U64 == 1 {
            defmt::write!(f, "{} min", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1 {
            defmt::write!(f, "{} s", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000 {
            defmt::write!(f, "{} ms", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000 {
            defmt::write!(f, "{} us", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000_000 {
            defmt::write!(f, "{} ns", self.since_start.ticks)
        } else {
            defmt::write!(f, "{} ticks @ ({}/{})", self.since_start.ticks, Numer::U64, Denom::U64)
        }
    }
}

impl<Numer:Unsigned, Denom: Unsigned + NonZero> core::fmt::Display for Instant<$i, Numer, Denom> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if Numer::U64 == 3_600 && Denom::U64 == 1 {
            write!(f, "{} h", self.since_start.ticks)
        } else if Numer::U64 == 60 && Denom::U64 == 1 {
            write!(f, "{} min", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1 {
            write!(f, "{} s", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000 {
            write!(f, "{} ms", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000 {
            write!(f, "{} μs", self.since_start.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000_000 {
            write!(f, "{} ns", self.since_start.ticks)
        } else {
            write!(f, "{} ticks @ ({}/{})", self.since_start.ticks, Numer::U64, Denom::U64)
        }
    }
}
    };
}
