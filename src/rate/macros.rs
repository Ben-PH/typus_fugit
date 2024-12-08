macro_rules! impl_rate_for_integer {
    ($i:ty) => {
impl<Numer: Unsigned, Denom:Unsigned + NonZero> Rate<$i, Numer, Denom> {
    /// Create a `Rate` from a raw value.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let _d = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(1);")]
    /// ```
    #[inline]
    pub const fn from_raw(raw: $i) -> Self {
        Rate { raw, _numer: PhantomData, _denom: PhantomData }
    }

    /// Extract the raw value from a `Rate`.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(234);")]
    ///
    /// assert_eq!(d.raw(), 234);
    /// ```
    #[inline]
    pub const fn raw(&self) -> $i {
        self.raw
    }

    /// Add two rates while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(1);")]
    #[doc = concat!("let r2 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(2);")]
    #[doc = concat!("let r3 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(", stringify!($i), "::MAX);")]
    ///
    /// assert_eq!(r1.checked_add(r2).unwrap().raw(), 3);
    /// assert_eq!(r1.checked_add(r3), None);
    /// ```
    pub const fn checked_add<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
        other: Rate<$i, ONumer, ODenom>,
    ) -> Option<Self> {
        if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
            if let Some(raw) = self.raw.checked_add(other.raw) {
                Some(Rate::<$i, Numer, Denom>::from_raw(raw))
            } else {
                None
            }
        } else {
            if let Some(lh) = other
                .raw
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let raw = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                if let Some(raw) = self.raw.checked_add(raw) {
                    Some(Rate::<$i, Numer, Denom>::from_raw(raw))
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    /// Subtract two rates while checking for overflow.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(1);")]
    #[doc = concat!("let r2 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(2);")]
    #[doc = concat!("let r3 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(", stringify!($i), "::MAX);")]
    ///
    /// assert_eq!(r2.checked_sub(r1).unwrap().raw(), 1);
    /// assert_eq!(r1.checked_sub(r3), None);
    /// ```
    pub const fn checked_sub<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
        other: Rate<$i, ONumer, ODenom>,
    ) -> Option<Self> {
        if Helpers::<Numer, Denom, ONumer, ODenom>::SAME_BASE {
            if let Some(raw) = self.raw.checked_sub(other.raw) {
                Some(Rate::<$i, Numer, Denom>::from_raw(raw))
            } else {
                None
            }
        } else {
            if let Some(lh) = other
                .raw
                .checked_mul(Helpers::<Numer, Denom, ONumer, ODenom>::LD_TIMES_RN as $i)
            {
                let raw = lh / Helpers::<Numer, Denom, ONumer, ODenom>::RD_TIMES_LN as $i;

                if let Some(raw) = self.raw.checked_sub(raw) {
                    Some(Rate::<$i, Numer, Denom>::from_raw(raw))
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
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U100>::from_raw(1);")]
    #[doc = concat!("let r2 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(1);")]
    ///
    /// assert_eq!(r1.const_partial_cmp(r2), Some(core::cmp::Ordering::Greater));
    /// ```
    #[inline]
    pub const fn const_partial_cmp<RNumer: Unsigned, RDenom:Unsigned + NonZero>(
        self,
        other: Rate<$i, RNumer, RDenom>
    ) -> Option<Ordering> {
        if Helpers::<Numer, Denom, RNumer, RDenom>::SAME_BASE {
            // If we are in the same base, comparison in trivial
            Some(Self::_const_cmp(self.raw, other.raw))
        } else {
            let lh = self
                .raw
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::RD_TIMES_LN as $i);
            let rh = other
                .raw
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
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U100>::from_raw(1);")]
    #[doc = concat!("let r2 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_raw(10);")]
    ///
    /// assert!(r1.const_eq(r2));
    /// ```
    #[inline]
    pub const fn const_eq<RNumer: Unsigned, RDenom:Unsigned + NonZero>(
        self,
        other: Rate<$i, RNumer, RDenom>
    ) -> bool {
        if Helpers::<Numer, Denom, RNumer, RDenom>::SAME_BASE {
            // If we are in the same base, comparison in trivial
            self.raw == other.raw
        } else {
            let lh = self
                .raw
                .checked_mul(Helpers::<Numer, Denom, RNumer, RDenom>::RD_TIMES_LN as $i);
            let rh = other
                .raw
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
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U100>::from_raw(1);")]
    #[doc = concat!("let r2 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>::const_try_from(r1);")]
    ///
    /// assert_eq!(r2.unwrap().raw(), 10);
    /// ```
    pub const fn const_try_from<INumer: Unsigned, IDenom:Unsigned + NonZero>(
        rate: Rate<$i, INumer, IDenom>,
    ) -> Option<Self> {
        if Helpers::<INumer, IDenom, Numer, Denom>::SAME_BASE {
            Some(Self::from_raw(rate.raw))
        } else {
            if let Some(lh) = (rate.raw as u64)
                .checked_mul(Helpers::<INumer, IDenom, Numer, Denom>::RD_TIMES_LN)
            {
                let raw = lh / Helpers::<INumer, IDenom, Numer, Denom>::LD_TIMES_RN;

                if raw <= <$i>::MAX as u64 {
                    Some(Self::from_raw(raw as $i))
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
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U100>::from_raw(1);")]
    #[doc = concat!("let r2: Option<Rate::<", stringify!($i), ", typenum::U1, typenum::U1000>> = r1.const_try_into();")]
    ///
    /// assert_eq!(r2.unwrap().raw(), 10);
    /// ```
    #[inline]
    pub const fn const_try_into<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
    ) -> Option<Rate<$i, ONumer, ODenom>> {
        Rate::<$i, ONumer, ODenom>::const_try_from(self)
    }

    /// Const try into duration, checking for divide-by-zero.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1>::from_raw(1);")]
    #[doc = concat!("let d1: Option<Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>> = r1.try_into_duration();")]
    ///
    /// assert_eq!(d1.unwrap().ticks(), 1_000);
    /// ```
    pub const fn try_into_duration<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
    ) -> Option<Duration<$i, ONumer, ODenom>> {
        Duration::<$i, ONumer, ODenom>::try_from_rate(self)
    }

    /// Convert from rate to duration.
    pub const fn into_duration<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
    ) -> Duration<$i, ONumer, ODenom> {
        if let Some(v) = self.try_into_duration() {
            v
        } else {
            panic!("Into duration failed, divide-by-zero!");
        }
    }

    /// Const try from duration, checking for divide-by-zero.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let d1 = Duration::<", stringify!($i), ", typenum::U1, typenum::U1000>::from_ticks(2);")]
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U1>::try_from_duration(d1);")]
    ///
    /// assert_eq!(r1.unwrap().raw(), 500);
    /// ```
    #[inline]
    pub const fn try_from_duration<INumer: Unsigned, IDenom:Unsigned + NonZero>(
        duration: Duration<$i, INumer, IDenom>,
    ) -> Option<Self> {
        if duration.ticks > 0 {
            Some(Self::from_raw(
                Helpers::<INumer, IDenom, Numer, Denom>::RATE_TO_DURATION_NUMERATOR as $i
                / duration.ticks
            ))
        } else {
            None
        }
    }

    /// Convert from duration to rate.
    #[inline]
    pub const fn from_duration<INumer: Unsigned, IDenom:Unsigned + NonZero>(
        duration: Duration<$i, INumer, IDenom>,
    ) -> Self {
        if let Some(v) = Self::try_from_duration(duration) {
            v
        } else {
            panic!("From duration failed, divide-by-zero!");
        }
    }

    /// Convert between bases for a rate.
    ///
    /// Unfortunately not a `From` impl due to collision with the std lib.
    /// UPDATE v0.4.0: use of typenum instead of const generics may allow for this now.
    ///
    /// ```
    /// # use typus_fugit::*;
    #[doc = concat!("let r1 = Rate::<", stringify!($i), ", typenum::U1, typenum::U100>::from_raw(1);")]
    #[doc = concat!("let r2: Rate::<", stringify!($i), ", typenum::U1, typenum::U1000> = r1.convert();")]
    ///
    /// assert_eq!(r2.raw(), 10);
    /// ```
    ///
    /// Can be used in const contexts. Compilation will fail if the conversion causes overflow
    ///
    /// ```compile_fail
    /// # use typus_fugit::*;
    #[doc = concat!("const RAW: ", stringify!($i), "= ", stringify!($i), "::MAX - 10;")]
    #[doc = concat!("const R1: Rate::<", stringify!($i), ", typenum::U1, typenum::U100> = Rate::<", stringify!($i), ", 1, 100>::from_raw(RAW);")]
    /// // Fails conversion due to overflow
    #[doc = concat!("const R2: Rate::<", stringify!($i), ", typenum::U1, typenum::U200> = R1.convert();")]
    /// ```
    pub const fn convert<ONumer: Unsigned, ODenom:Unsigned + NonZero>(
        self,
    ) -> Rate<$i, ONumer, ODenom> {
        if let Some(v) = self.const_try_into() {
            v
        } else {
            panic!("Convert failed!");
        }
    }

    /// Convert the Rate to an interger number of Hz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn to_Hz(&self) -> $i {
            (Helpers::<U1, U1, Numer, Denom>::LD_TIMES_RN as $i * self.raw)
                / Helpers::<U1, U1, Numer, Denom>::RD_TIMES_LN as $i
    }

    /// Convert the Rate to an interger number of kHz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn to_kHz(&self) -> $i {
            (Helpers::<U1000, U1, Numer, Denom>::LD_TIMES_RN as $i * self.raw)
                / Helpers::<U1000, U1, Numer, Denom>::RD_TIMES_LN as $i
    }

    /// Convert the Rate to an interger number of `MHz`.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn to_MHz(&self) -> $i {
            (Helpers::<U1000000, U1, Numer, Denom>::LD_TIMES_RN as $i * self.raw)
                / Helpers::<U1000000, U1, Numer, Denom>::RD_TIMES_LN as $i
    }

    /// Shorthand for creating a rate which represents hertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn Hz(val: $i) -> Self {
        Self::from_raw(
            (Helpers::<U1, U1, Numer, Denom>::RD_TIMES_LN as $i * val)
                / Helpers::<U1, U1, Numer, Denom>::LD_TIMES_RN as $i,
        )
    }

    /// Shorthand for creating a rate which represents kilohertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn kHz(val: $i) -> Self {
        Self::from_raw(
            (Helpers::<U1000, U1, Numer, Denom>::RD_TIMES_LN as $i * val)
                / Helpers::<U1000, U1, Numer, Denom>::LD_TIMES_RN as $i,
        )
    }

    /// Shorthand for creating a rate which represents megahertz.
    #[inline]
    #[allow(non_snake_case)]
    pub const fn MHz(val: $i) -> Self {
        Self::from_raw(
            (Helpers::<U1000000, U1, Numer, Denom>::RD_TIMES_LN as $i * val)
                / Helpers::<U1000000, U1, Numer, Denom>::LD_TIMES_RN as $i,
        )
    }

    /// Shorthand for creating a rate which represents nanoseconds.
    #[inline]
    pub const fn nanos(val: $i) -> Self {
        Self::from_duration(crate::aliases::NanosDuration::<$i>::from_ticks(val))
    }

    /// Shorthand for creating a rate which represents microseconds.
    #[inline]
    pub const fn micros(val: $i) -> Self {
        Self::from_duration(crate::aliases::MicrosDuration::<$i>::from_ticks(val))
    }

    /// Shorthand for creating a rate which represents milliseconds.
    #[inline]
    pub const fn millis(val: $i) -> Self {
        Self::from_duration(crate::aliases::MillisDuration::<$i>::from_ticks(val))
    }
}

impl<LNumer: Unsigned, LDenom:Unsigned + NonZero, RNumer: Unsigned, RDenom:Unsigned + NonZero>
    PartialOrd<Rate<$i, RNumer, RDenom>> for Rate<$i, LNumer, LDenom>
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<$i, RNumer, RDenom>) -> Option<Ordering> {
        self.const_partial_cmp(*other)
    }
}

impl<Numer: Unsigned, Denom:Unsigned + NonZero> Ord for Rate<$i, Numer, Denom> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Self::_const_cmp(self.raw, other.raw)
    }
}

impl<LNumer: Unsigned, LDenom:Unsigned + NonZero, RNumer: Unsigned, RDenom:Unsigned + NonZero>
    PartialEq<Rate<$i, RNumer, RDenom>> for Rate<$i, LNumer, LDenom>
{
    #[inline]
    fn eq(&self, other: &Rate<$i, RNumer, RDenom>) -> bool {
        self.const_eq(*other)
    }
}

impl<Numer: Unsigned, Denom:Unsigned + NonZero> Eq for Rate<$i, Numer, Denom> {}

// Rate - Rate = Rate (only same base until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::Sub<Rate<$i, Numer, Denom>>
    for Rate<$i, Numer, Denom>
{
    type Output = Rate<$i, Numer, Denom>;

    #[inline]
    fn sub(self, other: Rate<$i, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_sub(other) {
            v
        } else {
            panic!("Sub failed!");
        }
    }
}

// Rate + Rate = Rate (only same base until const_generics_defaults is
// stabilized)
// UPDATE v0.4.0: With `typenum`, this should now be implementable
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::Add<Rate<$i, Numer, Denom>>
    for Rate<$i, Numer, Denom>
{
    type Output = Rate<$i, Numer, Denom>;

    #[inline]
    fn add(self, other: Rate<$i, Numer, Denom>) -> Self::Output {
        if let Some(v) = self.checked_add(other) {
            v
        } else {
            panic!("Add failed!");
        }
    }
}

// Rate += Rate
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::AddAssign<Rate<$i, Numer, Denom>>
    for Rate<$i, Numer, Denom>
{
    #[inline]
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

// integer * Rate = Rate
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::Mul<Rate<$i, Numer, Denom>> for u32 {
    type Output = Rate<$i, Numer, Denom>;

    #[inline]
    fn mul(self, mut other: Rate<$i, Numer, Denom>) -> Self::Output {
        other.raw *= self as $i;
        other
    }
}

// Rate * integer = Rate
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::Mul<u32> for Rate<$i, Numer, Denom> {
    type Output = Rate<$i, Numer, Denom>;

    #[inline]
    fn mul(mut self, other: u32) -> Self::Output {
        self.raw *= other as $i;
        self
    }
}

// Rate *= integer
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::MulAssign<u32>
    for Rate<$i, Numer, Denom>
{
    #[inline]
    fn mul_assign(&mut self, other: u32) {
        *self = *self * other;
    }
}

// Rate / integer = Rate
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::Div<u32> for Rate<$i, Numer, Denom> {
    type Output = Rate<$i, Numer, Denom>;

    #[inline]
    fn div(mut self, other: u32) -> Self::Output {
        self.raw /= other as $i;
        self
    }
}

// Rate / Rate = integer
impl<LNumer: Unsigned, LDenom:Unsigned + NonZero, RNumer: Unsigned, RDenom:Unsigned + NonZero> ops::Div<Rate<$i, RNumer, RDenom>>
    for Rate<$i, LNumer, LDenom>
{
    type Output = $i;

    #[inline]
    fn div(self, other: Rate<$i, RNumer, RDenom>) -> Self::Output {
        let conv: Rate<$i, RNumer, RDenom> = self.convert();
        conv.raw / other.raw
    }
}

// Rate /= integer
impl<Numer: Unsigned, Denom:Unsigned + NonZero> ops::DivAssign<u32>
    for Rate<$i, Numer, Denom>
{
    #[inline]
    fn div_assign(&mut self, other: u32) {
        *self = *self / other;
    }
}

#[cfg(feature = "defmt")]
impl<Numer: Unsigned, Denom:Unsigned + NonZero> defmt::Format for Rate<$i, Numer, Denom>
{
    fn format(&self, f: defmt::Formatter) {
        if Numer::U64 == 1 && Denom::U64 == 1 {
            defmt::write!(f, "{} Hz", self.raw)
        } else if Numer::U64 == 1_000 && Denom::U64 == 1 {
            defmt::write!(f, "{} kHz", self.raw)
        } else if Numer::U64 == 1_000_000 && Denom::U64 == 1 {
            defmt::write!(f, "{} MHz", self.raw)
        } else if Numer::U64 == 1_000_000_000 && Denom::U64 == 1 {
            defmt::write!(f, "{} GHz", self.raw)
        } else {
            defmt::write!(f, "{} raw @ ({}/{})", self.raw, Numer::U64, Denom::U64)
        }
    }
}

impl<Numer: Unsigned, Denom:Unsigned + NonZero> core::fmt::Display for Rate<$i, Numer, Denom> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if Numer::U64 == 1 && Denom::U64 == 1 {
            write!(f, "{} Hz", self.raw)
        } else if Numer::U64 == 1_000 && Denom::U64 == 1 {
            write!(f, "{} kHz", self.raw)
        } else if Numer::U64 == 1_000_000 && Denom::U64 == 1 {
            write!(f, "{} MHz", self.raw)
        } else if Numer::U64 == 1_000_000_000 && Denom::U64 == 1 {
            write!(f, "{} GHz", self.raw)
        } else {
            write!(f, "{} raw @ ({}/{})", self.raw, Numer::U64, Denom::U64)
        }
    }
}
    };
}
