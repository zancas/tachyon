//! Tachyon proofs via Ragu PCD.
//!
//! Registers all PCD step types and provides accumulator helpers for
//! stamp construction and verification.
//!
//! `Step::INDEX` runs from zero without gaps, and [`make_app`] registers the
//! steps in that order; `ApplicationBuilder` rejects any other sequence.
//! `Header::SUFFIX` runs from zero without gaps too.
//!
//! A step is named "noun + verb", where the noun is the header it **emits**,
//! not the one it reads. Most fuse steps read and emit the same header, which
//! leaves the rule invisible until one does not: `EvidenceTreeFuse` emits an
//! `EvidenceTree` and reads two `EvidenceTreePair`s, and `EvidenceTreePairFuse`
//! emits the pair. Three steps whose output is a part of what they read are
//! named for the input instead: `QrIntakeSplit`, `QrSideDescend` and
//! `EvidenceTreeOpen`.

#![allow(missing_debug_implementations, missing_docs, reason = "todo")]

pub mod delegation;
pub mod evidence;
pub mod output;
pub mod pool;
pub mod qr;
pub mod spend;
pub mod spendable;
pub mod stamp;
pub mod summary;

use lazy_static::lazy_static;
use ragu::{Application, ApplicationBuilder, RegistryTags};
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::{
    drivers::{Driver, DriverValue},
    gadgets::Gadget,
    maybe::Maybe as _,
    pasta::Pasta,
};
use ragu_primitives::{Element, allocator::Allocator, io::Write};
use udon::curve::Affine as _;

use crate::{pasta, primitives::TachygramSetBridge, value};

/// The affine coordinates of a value commitment `cv` on a header.
#[derive(Gadget, Write)]
pub struct ValueCommitment<'dr, D: Driver<'dr>> {
    pub coordinates: [Element<'dr, D>; 2],
}

impl<'dr, D: Driver<'dr, F = pasta::Fp>> ValueCommitment<'dr, D> {
    fn alloc<A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        cv: DriverValue<D, value::Commitment>,
    ) -> ragu_core::Result<Self> {
        let coordinates = D::try_just(|| {
            pasta::EpAffine::from(cv.take())
                .coordinates()
                .ok_or_else(|| ragu_core::Error::InvalidWitness("cv is the identity".into()))
        })?;
        Ok(Self {
            coordinates: [
                Element::alloc(dr, allocator, coordinates.as_ref().map(|pair| pair.0))?,
                Element::alloc(dr, allocator, coordinates.as_ref().map(|pair| pair.1))?,
            ],
        })
    }
}

/// Eight payload elements for QR split/selection and bucket headers and one
/// suffix element.
pub const HEADER_SIZE: usize = 9;

fn make_app() -> Result<Application<'static, Pasta, ProductionRank, HEADER_SIZE>, ragu_core::Error>
{
    // Registry tags use the fixed Tachyon beacon and configuration digest.
    let manifest = blake2b_simd::Params::new()
        .hash_length(32)
        .hash(b"Tachyon PCD: Pasta, R13, H9, steps 0..38, ragu a73db816");
    let tags = RegistryTags::<Pasta>::from_beacon(b"Tachyon registry beacon", manifest.as_bytes());
    ApplicationBuilder::<Pasta, ProductionRank, HEADER_SIZE>::new()
        .with_registry_tags(tags, manifest.as_bytes())?
        .register(delegation::NoteSeed)?
        .register(delegation::NullifierDerive)?
        .register(pool::UnspentFuse)?
        .register(pool::UnspentBind)?
        .register(spendable::SpendableInit)?
        .register(spendable::SpendableLift)?
        .register(output::OutputBind)?
        .register(stamp::OutputAction)?
        .register(spend::SpendBind)?
        .register(stamp::SpendAction)?
        .register(stamp::StampMerge)?
        .register(stamp::StampLift)?
        .register(delegation::NullifierFuse)?
        .register(summary::SummarySeed)?
        .register(summary::SummaryAdvance)?
        .register(qr::QrSummaryIntake)?
        .register(qr::QrIntakeMerge)?
        .register(qr::QrIntakeSplit)?
        .register(qr::QrSideDescend)?
        .register(qr::QrUnspentInit)?
        .register(qr::QrBucketSeal)?
        .register(qr::QrStampIntakeSeed)?
        .register(spendable::QrSpendableInit)?
        .register(qr::QrEmptyIntakeSeed)?
        .register(pool::UnspentLift)?
        .register(evidence::EvidenceTreePairFuse)?
        .register(evidence::EvidenceTreeFuse)?
        .register(evidence::EvidenceTreeCap)?
        .register(evidence::EvidenceTreeDescend)?
        .register(evidence::EvidenceTreeOpen)?
        .register(evidence::EvidenceTreeLeafPair)?
        .register(pool::AnchorSpanSeed)?
        .register(pool::AnchorSpanFuse)?
        .register(stamp::FeeFuse)?
        .register(stamp::ActionMerge)?
        .register(stamp::ActionLift)?
        .register(stamp::FeeSeed)?
        .register(stamp::StampUnmerge)?
        .register(qr::QrSideSelect)?
        .finalize(pasta::baked())
}

lazy_static! {
    /// Fixed by the baked parameters and production rank, independently of PCD setup.
    static ref EMPTY_STAMP_BRIDGE_HASH: TachygramSetBridge = {
        #[expect(clippy::expect_used, reason = "the fixed setup has finite bridge generators")]
        TachygramSetBridge::empty().expect("valid constant-one bridge hash")
    };

    /// A static ref to the mock ragu application.
    pub static ref PROOF_SYSTEM: Application<'static, Pasta, ProductionRank, HEADER_SIZE> = {
        #[expect(
            clippy::expect_used,
            reason = "hardcoded step ordering must register cleanly"
        )]
        make_app().expect("registration of fixed step list must succeed")
    };
}

#[cfg(test)]
mod tests;
