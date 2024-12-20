macro_rules! shorthand {
    ($i:ty, $nom:ty, $denum:ty, $unit:ident, $to_unit:ident, $unital:ident, $unitstr:literal) => {
        #[doc = concat!("Convert the Duration to an integer number of ", $unitstr, ".")]
        #[inline]
        pub const fn $to_unit(&self) -> $i {
            (Helpers::<$nom, $denum, Numer, Denom>::LD_TIMES_RN as $i * self.ticks)
                / Helpers::<$nom, $denum, Numer, Denom>::RD_TIMES_LN as $i
        }

        #[doc = concat!("Shorthand for creating a duration which represents ", $unitstr, ".")]
        #[inline]
        pub const fn $unit(val: $i) -> Self {
            Self::from_ticks(
                (Helpers::<$nom, $denum, Numer, Denom>::RD_TIMES_LN as $i * val)
                    / Helpers::<$nom, $denum, Numer, Denom>::LD_TIMES_RN as $i
            )
        }

        #[doc = concat!("Shorthand for creating a duration which represents ", $unitstr, " (ceil rounded).")]
        #[inline]
        pub const fn $unital(val: $i) -> Self {
            let mul = Helpers::<$nom, $denum, Numer, Denom>::RD_TIMES_LN as $i * val;
            let ld_times_rn = Helpers::<$nom, $denum, Numer, Denom>::LD_TIMES_RN as $i;
            Self::from_ticks(if mul % ld_times_rn == 0 {
                mul / ld_times_rn
            } else {
                mul / ld_times_rn + 1
            })
        }
    };
}

macro_rules! impl_duration_for_integer {
    ($i:ty) => {
impl<Numer: Unsigned, Denom: Unsigned + NonZero> Duration<$i, Numer, Denom> {
    /// Returns true if this `Duration` spans no time
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let zero = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(0);")]
    #[doc = concat!("let one = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
    ///
    /// assert_eq!(zero.is_zero(), true);
    /// assert_eq!(one.is_zero(), false);
    /// ```
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.ticks == 0
    }

    /// Add two durations while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
    #[doc = concat!("let d2 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
    #[doc = concat!("let d3 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(", stringify!($i), "::MAX);")]
    ///
    /// assert_eq!(d1.checked_add(d2).unwrap().ticks(), 3);
    /// assert_eq!(d1.checked_add(d3), None);
    /// ```
    pub const fn checked_add<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
        other: Duration<$i, ONumer, ODenom>,
    ) -> Option<Self> {
        if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
            if let Some(ticks) = self.ticks.checked_add(other.ticks) {
                Some(Duration::<$i, Numer, Denom>::from_ticks(ticks))
            } else {
                None
            }
        } else {
            if let Some(lh) = other
                .ticks
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                if let Some(ticks) = self.ticks.checked_add(ticks) {
                    Some(Duration::<$i, Numer, Denom>::from_ticks(ticks))
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    /// Subtract two durations while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
    #[doc = concat!("let d2 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
    #[doc = concat!("let d3 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(", stringify!($i), "::MAX);")]
    ///
    /// assert_eq!(d2.checked_sub(d1).unwrap().ticks(), 1);
    /// assert_eq!(d1.checked_sub(d3), None);
    /// ```
    pub const fn checked_sub<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
        other: Duration<$i, ONumer, ODenom>,
    ) -> Option<Self> {
        if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
            if let Some(ticks) = self.ticks.checked_sub(other.ticks) {
                Some(Duration::<$i, Numer, Denom>::from_ticks(ticks))
            } else {
                None
            }
        } else {
            if let Some(lh) = other
                .ticks
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let ticks = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                if let Some(ticks) = self.ticks.checked_sub(ticks) {
                    Some(Duration::<$i, Numer, Denom>::from_ticks(ticks))
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    #[doc = concat!("Const `cmp` for ", stringify!($i))]
    #[inline(always)]
    const fn _const_cmp(a: $i, b: $i) -> Ordering {
        if a < b {
            Ordering::Less
        } else if a > b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    /// Const partial comparison.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(1);")]
    #[doc = concat!("let d2 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(1);")]
    ///
    /// assert_eq!(d1.const_partial_cmp(d2), Some(core::cmp::Ordering::Greater));
    /// ```
    #[inline]
    pub const fn const_partial_cmp<RNumer: Unsigned, RDenom: Unsigned + NonZero>(
        self,
        other: Duration<$i, RNumer, RDenom>
    ) -> Option<Ordering> {
        //
        // We want to check:
        //
        // n_lh / d_lh * lh_ticks {cmp} n_rh / d_rh * rh_ticks
        //
        // simplify to
        //
        // n_lh * d_rh * lh_ticks {cmp} n_rh * d_lh * rh_ticks
        //
        // find gdc(n_lh * d_rh, n_rh * d_lh) and use that to make the constants minimal (done
        // with the `helpers::Helpers` struct)
        //
        // then perform the comparison in a comparable basis
        //

        if Helpers::<Numer, Denom, RNumer, RDenom>::SAME_BASE {
            // If we are in the same base, comparison in trivial
            Some(Self::_const_cmp(self.ticks, other.ticks))
        } else {
            let lh = self
                .ticks
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::RD_TIMES_LN as $i);
            let rh = other
                .ticks
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::LD_TIMES_RN as $i);

            if let (Some(lh), Some(rh)) = (lh, rh) {
                Some(Self::_const_cmp(lh, rh))
            } else {
                None
            }
        }
    }

    /// Const equality check.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(1);")]
    #[doc = concat!("let d2 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(10);")]
    ///
    /// assert!(d1.const_eq(d2));
    /// ```
    #[inline]
    pub const fn const_eq<RNumer: Unsigned, RDenom: Unsigned + NonZero>(
        self,
        other: Duration<$i, RNumer, RDenom>
    ) -> bool {
        if Helpers::<Numer, Denom, RNumer, RDenom>::SAME_BASE {
            // If we are in the same base, comparison in trivial
            self.ticks == other.ticks
        } else {
            let lh = self
                .ticks
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::RD_TIMES_LN as $i);
            let rh = other
                .ticks
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::LD_TIMES_RN as $i);

            if let (Some(lh), Some(rh)) = (lh, rh) {
                lh == rh
            } else {
                false
            }
        }
    }

    /// Const try from, checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(1);")]
    #[doc = concat!("let d2 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::const_try_from(d1);")]
    ///
    /// assert_eq!(d2.unwrap().ticks(), 10);
    /// ```
    pub const fn const_try_from<INumer: Unsigned, IDenom: Unsigned + NonZero>(
        duration: Duration<$i, INumer, IDenom>,
    ) -> Option<Self> {
        if Helpers::<INumer, IDenom, Numer, Denom>::SAME_BASE {
            Some(Self::from_ticks(duration.ticks))
        } else {
            if let Some(lh) = (duration.ticks as u64)
                .checked_mul(Helpers::<INumer, IDenom, Numer, Denom>::RD_TIMES_LN as u64)
            {
                let ticks = lh / Helpers::<INumer, IDenom, Numer, Denom>::LD_TIMES_RN as u64;

                if ticks <= <$i>::MAX as u64 {
                    Some(Self::from_ticks(ticks as $i))
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    /// Const try into, checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(1);")]
    #[doc = concat!("let d2: Option<Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>> = d1.const_try_into();")]
    ///
    /// assert_eq!(d2.unwrap().ticks(), 10);
    /// ```
    #[inline]
    pub const fn const_try_into<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
    ) -> Option<Duration<$i, ONumer, ODenom>> {
        Duration::<$i, ONumer, ODenom>::const_try_from(self)
    }

    /// Const try into rate, checking for divide-by-zero.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
    #[doc = concat!("let r1: Option<Rate::<", stringify!($i), ", typenum::U1, typenum::U1>> = d1.try_into_rate();")]
    ///
    /// assert_eq!(r1.unwrap().raw(), 500);
    /// ```
    #[inline]
    pub const fn try_into_rate<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
    ) -> Option<Rate<$i, ONumer, ODenom>> {
        Rate::<$i, ONumer, ODenom>::try_from_duration(self)
    }

    /// Convert from duration to rate.
    #[inline]
    pub const fn into_rate<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
    ) -> Rate<$i, ONumer, ODenom> {
        if let Some(v) = self.try_into_rate() {
            v
        } else {
            panic!("Into rate failed, divide-by-zero!");
        }
    }

    /// Const try from rate, checking for divide-by-zero.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1>::from_raw(1);")]
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::try_from_rate(r1);")]
    ///
    /// assert_eq!(d1.unwrap().ticks(), 1_000);
    /// ```
    #[inline]
    pub const fn try_from_rate<INumer: Unsigned, IDenom: Unsigned + NonZero>(
        rate: Rate<$i, INumer, IDenom>,
    ) -> Option<Self> {
        if rate.raw > 0 {
            Some(Self::from_ticks(
                Helpers::<INumer, IDenom, Numer, Denom>::RATE_TO_DURATION_NUMERATOR as $i
                / rate.raw
            ))
        } else {
            None
        }
    }

    /// Convert from rate to duration.
    #[inline]
    pub const fn from_rate<INumer: Unsigned, IDenom: Unsigned + NonZero>(
        rate: Rate<$i, INumer, IDenom>,
    ) -> Self {
        if let Some(v) = Self::try_from_rate(rate) {
            v
        } else {
            panic!("From rate failed, divide-by-zero!");
        }
    }

    /// Convert between bases for a duration.
    ///
    /// Unfortunately not a `From` impl due to collision with the std lib.
    /// UPDATE v0.4.0: use of typenum instead of const generics may allow for this now.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(1);")]
    #[doc = concat!("let d2: Duration::<", stringify!($i), ", typenum::U1, typenum::U1000> = d1.convert();")]
    ///
    /// assert_eq!(d2.ticks(), 10);
    /// ```
    /// Can be used in const contexts. Compilation will fail if the conversion causes overflow
    /// ```compile_fail
    /// # use typus_fugit::*;
    #[doc = concat!("const TICKS: ", stringify!($i), "= ", stringify!($i), "::MAX - 10;")]
    #[doc = concat!("const D1: Duration::<", stringify!($i), ", typenum::U1, typenum::U100> = Duration::<", stringify!($i), ", typenum::U1, typenum::U100>::from_ticks(TICKS);")]
    /// // Fails conversion due to tick overflow
    #[doc = concat!("const D2: Duration::<", stringify!($i), ", typenum::U1, typenum::U200> = D1.convert();")]
    #[inline]
    pub const fn convert<ONumer: Unsigned, ODenom: Unsigned + NonZero>(
        self,
    ) -> Duration<$i, ONumer, ODenom> {
        if let Some(v) = self.const_try_into() {
            v
        } else {
            panic!("Convert failed!");
        }
    }

    shorthand!($i, typenum::U1, typenum::U1000000000, nanos, to_nanos, nanos_at_least, "nanoseconds");
    shorthand!($i, typenum::U1, typenum::U1000000, micros, to_micros, micros_at_least, "microseconds");
    shorthand!($i, typenum::U1, typenum::U1000, millis, to_millis, millis_at_least, "milliseconds");
    shorthand!($i, typenum::U1, typenum::U1, secs, to_secs, secs_at_least, "seconds");
    shorthand!($i, typenum::U60, typenum::U1, minutes, to_minutes, minutes_at_least, "minutes");
    shorthand!($i, typenum::op!(U36 * U100), typenum::U1, hours, to_hours, hours_at_least, "hours");

    /// Shorthand for creating a duration which represents hertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn Hz(val: $i) -> Self {
        Self::from_rate(crate::Hertz::<$i>::from_raw(val))
    }

    /// Shorthand for creating a duration which represents kilohertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn kHz(val: $i) -> Self {
        Self::from_rate(crate::Kilohertz::<$i>::from_raw(val))
    }

    /// Shorthand for creating a duration which represents megahertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn MHz(val: $i) -> Self {
        Self::from_rate(crate::Megahertz::<$i>::from_raw(val))
    }
}

impl<LNumer: Unsigned, LDenom: Unsigned + NonZero, RNumer: Unsigned, RDenom: Unsigned + NonZero>
    PartialOrd<Duration<$i, RNumer, RDenom>> for Duration<$i, LNumer, LDenom>
{
    #[inline]
    fn partial_cmp(&self, other: &Duration<$i, RNumer, RDenom>) -> Option<Ordering> {
        self.const_partial_cmp(*other)
    }
}

impl<Numer: Unsigned, Denom: Unsigned + NonZero> Ord for Duration<$i, Numer, Denom> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Self::_const_cmp(self.ticks, other.ticks)
    }
}

impl<LNumer: Unsigned, LDenom: Unsigned + NonZero, RNumer: Unsigned, RDenom: Unsigned + NonZero>
    PartialEq<Duration<$i, RNumer, RDenom>> for Duration<$i, LNumer, LDenom>
{
    #[inline]
    fn eq(&self, other: &Duration<$i, RNumer, RDenom>) -> bool {
        self.const_eq(*other)
    }
}

impl<Numer: Unsigned, Denom: Unsigned + NonZero> Eq for Duration<$i, Numer, Denom> {}


// integer * Duration = Duration
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::Mul<Duration<$i, Numer, Denom>> for u32 {
    type Output = Duration<$i, Numer, Denom>;

    #[inline]
    fn mul(self, mut other: Duration<$i, Numer, Denom>) -> Self::Output {
        other.ticks *= self as $i;
        other
    }
}

// Duration * integer = Duration
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::Mul<u32> for Duration<$i, Numer, Denom> {
    type Output = Duration<$i, Numer, Denom>;

    #[inline]
    fn mul(mut self, other: u32) -> Self::Output {
        self.ticks *= other as $i;
        self
    }
}

// Duration *= integer
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::MulAssign<u32>
    for Duration<$i, Numer, Denom>
{
    #[inline]
    fn mul_assign(&mut self, other: u32) {
        *self = *self * other;
    }
}

// Duration / integer = Duration
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::Div<u32> for Duration<$i, Numer, Denom> {
    type Output = Duration<$i, Numer, Denom>;

    #[inline]
    fn div(mut self, other: u32) -> Self::Output {
        self.ticks /= other as $i;
        self
    }
}

// Duration /= integer
impl<Numer: Unsigned, Denom: Unsigned + NonZero> ops::DivAssign<u32>
    for Duration<$i, Numer, Denom>
{
    #[inline]
    fn div_assign(&mut self, other: u32) {
        *self = *self / other;
    }
}

// Duration / Duration = integer
impl<LNumer: Unsigned, LDenom: Unsigned + NonZero, RNumer: Unsigned, RDenom: Unsigned + NonZero> ops::Div<Duration<$i, RNumer, RDenom>>
    for Duration<$i, LNumer, LDenom>
{
    type Output = $i;

    #[inline]
    fn div(self, other: Duration<$i, RNumer, RDenom>) -> Self::Output {
        let conv: Duration<$i, RNumer, RDenom> = self.convert();
        conv.ticks / other.ticks
    }
}

#[cfg(feature = "defmt")]
impl<Numer: Unsigned, Denom: Unsigned + NonZero> defmt::Format for Duration<$i, Numer, Denom>
{
    fn format(&self, f: defmt::Formatter) {
        if Numer::U64 == 3_600 && Denom::U64 == 1 {
            defmt::write!(f, "{} h", self.ticks)
        } else if Numer::U64 == 60 && Denom::U64 == 1 {
            defmt::write!(f, "{} min", self.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1 {
            defmt::write!(f, "{} s", self.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000 {
            defmt::write!(f, "{} ms", self.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000 {
            defmt::write!(f, "{} us", self.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000_000 {
            defmt::write!(f, "{} ns", self.ticks)
        } else {
            defmt::write!(f, "{} ticks @ ({}/{})", self.ticks, Numer::U64, Denom::U64)
        }
    }
}

impl<Numer: Unsigned, Denom: Unsigned + NonZero> core::fmt::Display for Duration<$i, Numer, Denom> {
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
            write!(f, "{} us", self.ticks)
        } else if Numer::U64 == 1 && Denom::U64 == 1_000_000_000 {
            write!(f, "{} ns", self.ticks)
        } else {
            write!(f, "{} ticks @ ({}/{})", self.ticks, Numer::U64, Denom::U64)
        }
    }
}
    };
}
