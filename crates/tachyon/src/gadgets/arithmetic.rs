//! Range-checked integers and epoch indices for proof steps.

use core::ops::Deref;

use ragu_core::{
    PoseidonPermutation as _, Result,
    drivers::{Driver, DriverValue},
    maybe::Maybe as _,
    pasta::PoseidonFp,
};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _, multipack,
    vec::{ConstLen, FixedVec},
};
use udon::field::Field as _;

use crate::{constants::EPOCH_MAX, pasta::Fp, primitives};

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

/// A range-checked epoch index inside a circuit.
pub(crate) struct EpochIndex<'dr, D: Driver<'dr>> {
    element: Element<'dr, D>,
    /// Bits 0 and 1 of the index's constrained decomposition: its position
    /// within its `PoseidonFp::RATE`-element nullifier group.
    position: [Boolean<'dr, D>; 2],
}

impl<'dr, D: Driver<'dr, F = Fp>> EpochIndex<'dr, D> {
    /// Both the index and `EPOCH_MAX - index` must fit 32 bits, preventing
    /// field wraparound.
    #[expect(
        clippy::indexing_slicing,
        clippy::missing_asserts_for_indexing,
        reason = "fixed 32-bit decompositions that multipack packs into one chunk"
    )]
    pub(crate) fn new(dr: &mut D, epoch: &Element<'dr, D>) -> Result<Self> {
        let bits = FixedVec::<_, ConstLen<32>>::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                epoch
                    .value()
                    .map(|candidate| candidate.to_le_bits().as_ref()[index]),
            )
        })?;
        multipack(dr, &bits)?[0].enforce_equal(dr, epoch)?;
        let maximum = Element::constant(dr, Fp::from(u64::from(EPOCH_MAX)));
        let slack = maximum.sub(dr, epoch);
        Bounded::<D, 32>::new(dr, &slack)?;
        Ok(Self {
            element: epoch.clone(),
            position: [bits[0].clone(), bits[1].clone()],
        })
    }

    pub(crate) fn next(&self, dr: &mut D) -> Result<Self> {
        let one = Element::constant(dr, Fp::ONE);
        let next = self.element.add(dr, &one);
        Self::new(dr, &next)
    }

    /// The first index of this index's nullifier group: the index less its
    /// position.
    pub(crate) fn group_start(&self, dr: &mut D) -> Element<'dr, D> {
        let twice_bit1 = self.position[1].element().double(dr);
        self.element
            .sub(dr, &self.position[0].element())
            .sub(dr, &twice_bit1)
    }

    /// This index's entry in its nullifier group, given in order from the
    /// group start.
    pub(crate) fn select_in_group(
        &self,
        dr: &mut D,
        group: [Element<'dr, D>; PoseidonFp::RATE],
    ) -> Result<Element<'dr, D>> {
        let [first, second, third, fourth] = group;
        let lower = self.position[0].conditional_select(dr, &first, &second)?;
        let upper = self.position[0].conditional_select(dr, &third, &fourth)?;
        self.position[1].conditional_select(dr, &lower, &upper)
    }

    /// The native index. Witness generation rejects an out-of-range element,
    /// as the range check rejects it in the circuit.
    pub(crate) fn value(&self) -> Result<DriverValue<D, primitives::EpochIndex>> {
        D::try_just(|| {
            primitives::EpochIndex::try_from(*self.element.value().take())
                .map_err(|_err| ragu_core::Error::InvalidWitness("epoch index out of range".into()))
        })
    }

    pub(crate) fn into_element(self) -> Element<'dr, D> {
        self.element
    }
}

#[cfg(test)]
mod tests;
