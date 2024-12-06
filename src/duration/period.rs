use core::marker::PhantomData;

use typenum::NonZero;

#[derive(Clone, Copy, Debug, Default)]
pub struct Period<Numer, Denom: NonZero> {
    pub(crate) _numer: PhantomData<Numer>,
    pub(crate) _denom: PhantomData<Denom>,
}

