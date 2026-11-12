//! Range-checked integers for proof steps.

use core::ops::Deref;

use ragu_core::{Result, drivers::Driver, maybe::Maybe as _};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _, multipack,
    vec::{ConstLen, FixedVec},
};
use udon::field::Field as _;

use crate::pasta::Fp;

/// An element constrained below $2^N$.
pub(crate) struct Bounded<'dr, D: Driver<'dr>, const N: usize>(Element<'dr, D>);

impl<'dr, D: Driver<'dr, F = Fp>, const N: usize> Bounded<'dr, D, N> {
    /// Decomposes `value` into `N` Boolean bits that pack back to it.
    #[expect(
        clippy::indexing_slicing,
        reason = "multipack packs at most 64 bits into one chunk"
    )]
    pub(crate) fn new(dr: &mut D, value: &Element<'dr, D>) -> Result<Self> {
        const {
            assert!(N > 0 && N <= 64, "a bounded integer has at most 64 bits");
        }
        let bits = FixedVec::<_, ConstLen<N>>::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                value
                    .value()
                    .map(|candidate| candidate.to_le_bits().as_ref()[index]),
            )
        })?;
        multipack(dr, &bits)?[0].enforce_equal(dr, value)?;
        Ok(Self(value.clone()))
    }

    /// Constrains `value` to at most `maximum`, a public bound below $2^N$:
    /// both `value` and `maximum - value` fit `N` bits, so neither wraps.
    pub(crate) fn at_most(dr: &mut D, value: &Element<'dr, D>, maximum: u64) -> Result<Self> {
        let bound = Element::constant(dr, Fp::from(maximum));
        let slack = bound.sub(dr, value);
        let bounded = Self::new(dr, value)?;
        Self::new(dr, &slack)?;
        Ok(bounded)
    }
}

impl<'dr, D: Driver<'dr>, const N: usize> Deref for Bounded<'dr, D, N> {
    type Target = Element<'dr, D>;

    fn deref(&self) -> &Element<'dr, D> {
        &self.0
    }
}
