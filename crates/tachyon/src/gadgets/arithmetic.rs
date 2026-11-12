//! Range-checked epoch indices for proof steps.

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

/// A range-checked epoch index inside a circuit.
pub(crate) struct EpochIndex<'dr, D: Driver<'dr>> {
    element: Element<'dr, D>,
    /// The index's two low bits, constrained by its decomposition: its
    /// position within a nullifier group.
    low: Boolean<'dr, D>,
    high: Boolean<'dr, D>,
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
        let decompose = |driver: &mut D, value: &Element<'dr, D>| {
            let bits = FixedVec::<_, ConstLen<32>>::try_from_fn(|index| {
                Boolean::alloc(
                    driver,
                    &mut (),
                    value
                        .value()
                        .map(|candidate| candidate.to_le_bits().as_ref()[index]),
                )
            })?;
            multipack(driver, &bits)?[0].enforce_equal(driver, value)?;
            Ok::<_, ragu_core::Error>(bits)
        };
        let bits = decompose(dr, epoch)?;
        let maximum = Element::constant(dr, Fp::from(u64::from(EPOCH_MAX)));
        let slack = maximum.sub(dr, epoch);
        decompose(dr, &slack)?;
        Ok(Self {
            element: epoch.clone(),
            low: bits[0].clone(),
            high: bits[1].clone(),
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
        let twice_high = self.high.element().double(dr);
        self.element
            .sub(dr, &self.low.element())
            .sub(dr, &twice_high)
    }

    /// This index's entry in its nullifier group, given in order from the
    /// group start.
    pub(crate) fn select_in_group(
        &self,
        dr: &mut D,
        group: [Element<'dr, D>; PoseidonFp::RATE],
    ) -> Result<Element<'dr, D>> {
        let [first, second, third, fourth] = group;
        let lower = self.low.conditional_select(dr, &first, &second)?;
        let upper = self.low.conditional_select(dr, &third, &fourth)?;
        self.high.conditional_select(dr, &lower, &upper)
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
