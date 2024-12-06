use core::marker::PhantomData;

use typenum::NonZero;

/// Period in seconds represented as a ratio.
///
/// ```rust
/// use typus_fugit::typenum::{U1, U60, U1000};
/// use typus_fugit::Period;
/// type Seconds = Period<U1, U1>;
/// type Minutes = Period<U60, U1>;
/// type Ms = Period<U1, U1000>;
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct Period<Numer, Denom: NonZero> {
    pub(crate) _numer: PhantomData<Numer>,
    pub(crate) _denom: PhantomData<Denom>,
}
