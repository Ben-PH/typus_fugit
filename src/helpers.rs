use core::marker::PhantomData;

use typenum::{NonZero, Unsigned};

/// Needed due to not being allowed to call const-fn in `PartialEq` fo some reasion
/// get the error:
///
/// ```console
/// error[E0401]: can't use generic parameters from outer function
///   --> src/main.rs:25:47
///    |
/// 21 | impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
///    |                                                                    ------- const parameter from outer function
/// ...
/// 25 |         const TEST: u32 = gcd_binary_u32(L_DENOM, R_DENOM);
///    |                                                   ^^^^^^^ use of generic parameter from outer function
///
/// For more information about this error, try `rustc --explain E0401`
/// ```
pub struct Helpers<LNumer, LDenom, RNumer, RDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    l_numer: PhantomData<LNumer>,
    r_numer: PhantomData<RNumer>,
    l_denom: PhantomData<LDenom>,
    r_denom: PhantomData<RDenom>,
}

impl<LNumer, LDenom, RNumer, RDenom> Helpers<LNumer, LDenom, RNumer, RDenom>
where
    LNumer: Unsigned,
    LDenom: Unsigned + NonZero,
    RNumer: Unsigned,
    RDenom: Unsigned + NonZero,
{
    /// Helper constants generated at compile time
    pub const DIVISOR: u64 = gcd::binary_u64(LDenom::U64 * RNumer::U64, RDenom::U64 * LNumer::U64);

    /// Helper constants generated at compile time
    pub const DIVISOR_2: u64 =
        gcd::binary_u64(LNumer::U64 * RNumer::U64, RDenom::U64 * LDenom::U64);

    /// Helper constants generated at compile time for Durations
    pub const RD_TIMES_LN: u64 = (RDenom::U64 * LNumer::U64) / Self::DIVISOR;

    /// Helper constants generated at compile time
    pub const LD_TIMES_RN: u64 = (LDenom::U64 * RNumer::U64) / Self::DIVISOR;

    /// Helper constants generated at compile time for Rates
    pub const LN_TIMES_RN: u64 = (LNumer::U64 * RNumer::U64) / Self::DIVISOR_2;

    /// Helper constants generated at compile time for Rates
    pub const RD_TIMES_LD: u64 = (RDenom::U64 * LDenom::U64) / Self::DIVISOR_2;

    /// Helper constants generated at compile time for Rates
    pub const RATE_TO_DURATION_NUMERATOR: u64 = Self::RD_TIMES_LD / Self::LN_TIMES_RN;

    /// Helper constants generated at compile time
    pub const SAME_BASE: bool = Self::LD_TIMES_RN == Self::RD_TIMES_LN;
}

