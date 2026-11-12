use core::iter;

use corez::io::{self, Read, Write};
use derive_more::{AsRef, Debug, Eq as TotalEq, From, Into, PartialEq};
use ragu_circuits::{
    polynomials::{ProductionRank, sparse::Polynomial},
    staging::wire_degree,
};
use ragu_core::{Cycle as _, FixedGenerators as _, drivers::Driver, pasta::Pasta};
use ragu_primitives::{ENDOSCALAR_BITS, ENDOSCALAR_PRODUCTS, Element};
use udon::curve::{Affine, Projective as _};

use super::{ActionDigest, Anchor, Tachygram};
use crate::{
    collections::multiset,
    pasta,
    pasta::{EpAffine, Eq, Fp},
    serialization,
    stamp::proof::PROOF_SYSTEM,
};

/// Pedersen commitment to a stamp's tachygram set.
#[derive(AsRef, Clone, Copy, Debug, From, Into, PartialEq, TotalEq)]
pub struct TachygramSetCommit(Eq);

/// Bridge hash of a tachygram-set commitment: a Pallas point.
#[derive(Clone, Copy, Debug, From, Into, PartialEq, TotalEq)]
pub struct TachygramSetBridge(EpAffine);

impl TachygramSetCommit {
    /// Hashes this commitment through the application's bridge-hash stage.
    ///
    /// # Errors
    ///
    /// Fails if the commitment is the identity.
    pub fn bridge(self) -> ragu_core::Result<TachygramSetBridge> {
        Ok(TachygramSetBridge(
            PROOF_SYSTEM.bridge_hash(self.0.to_affine())?,
        ))
    }

    /// Read as an affine point from the consensus wire format.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails or the bytes are not a canonical
    /// curve point.
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let commit = serialization::read_eq_affine(&mut reader)?;
        Ok(Self(commit.into()))
    }

    /// Write as an affine point to the consensus wire format.
    ///
    /// # Errors
    ///
    /// Returns an error if writing fails.
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        serialization::write_eq_affine(&mut writer, &self.0.to_affine())?;
        Ok(())
    }
}

impl Default for TachygramSetCommit {
    /// A commitment to an empty set.
    fn default() -> Self {
        iter::empty().collect::<TachygramSetPoly>().commit()
    }
}

impl TachygramSetBridge {
    /// The bridge hash of the empty set's constant-one commitment, computed
    /// from the baked parameters without an application, so steps can use it
    /// while the application registers them.
    ///
    /// # Errors
    ///
    /// Fails if the baked parameters lack a finite constant-one commitment
    /// or bridge generators.
    pub(crate) fn empty() -> ragu_core::Result<Self> {
        let params = pasta::baked();
        let (x, y) = Pasta::host_generators(params)
            .g()
            .first()
            .and_then(Affine::coordinates)
            .ok_or_else(|| {
                ragu_core::Error::Initialization("constant-one commitment is not finite".into())
            })?;
        // The bridge point follows the hoisted endoscalar's bits and products,
        // starting at the next reserved gate (two stage wires per gate).
        let first_wire = (ENDOSCALAR_BITS + ENDOSCALAR_PRODUCTS).next_multiple_of(2);
        let generators = Pasta::nested_generators(params).g();
        let [left, right] = [first_wire, first_wire + 1].map(|wire| {
            generators
                .get(wire_degree::<ProductionRank>(wire))
                .ok_or_else(|| {
                    ragu_core::Error::Initialization("bridge generator is missing".into())
                })
        });
        let commitment = left?.to_projective() * x + right?.to_projective() * y;
        let (bridge_x, bridge_y) = commitment.to_affine().coordinates().ok_or_else(|| {
            ragu_core::Error::Initialization("constant-one bridge hash is not finite".into())
        })?;
        EpAffine::from_xy(bridge_x, bridge_y)
            .map(Self)
            .ok_or_else(|| {
                ragu_core::Error::Initialization(
                    "constant-one bridge hash is not on the curve".into(),
                )
            })
    }

    /// Constrains the in-circuit bridge hash `coordinates` to differ from this
    /// one.
    ///
    /// # Errors
    ///
    /// Fails when the coordinates equal this bridge hash.
    pub(crate) fn enforce_distinct<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        coordinates: &[Element<'dr, D>; 2],
    ) -> ragu_core::Result<()> {
        let (x, y) = self.0.coordinates().ok_or_else(|| {
            ragu_core::Error::Initialization("bridge hash is the identity".into())
        })?;
        let x_element = Element::constant(dr, x);
        let y_element = Element::constant(dr, y);
        let equal_x = coordinates[0].is_equal(dr, &mut (), &x_element)?;
        let equal_y = coordinates[1].is_equal(dr, &mut (), &y_element)?;
        equal_x.and(dr, &equal_y)?.element().enforce_zero(dr)
    }
}

/// Pedersen commitment to a stamp's action-digest set.
#[derive(AsRef, Clone, Copy, Debug, From, Into, PartialEq, TotalEq)]
pub struct ActionSetCommit(Eq);

impl ActionSetCommit {
    /// Read as an affine point from the consensus wire format.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails or the bytes are not a canonical
    /// curve point.
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let commit = serialization::read_eq_affine(&mut reader)?;
        Ok(Self(commit.into()))
    }

    /// Write as an affine point to the consensus wire format.
    ///
    /// # Errors
    ///
    /// Returns an error if writing fails.
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        serialization::write_eq_affine(&mut writer, &self.0.to_affine())?;
        Ok(())
    }
}

impl Default for ActionSetCommit {
    /// A commitment to an empty set.
    fn default() -> Self {
        iter::empty().collect::<ActionSetPoly>().commit()
    }
}

/// Pedersen commitment to an anchor span's member set.
#[derive(AsRef, Clone, Copy, Debug, From, Into, PartialEq, TotalEq)]
pub struct AnchorSetCommit(Eq);

impl AnchorSetCommit {
    /// Commitment to the one-member set $\\{\mathsf{anchor}\\}$, the
    /// polynomial $X - \mathsf{anchor}$, computed from the fixed generators:
    ///
    /// $$
    ///   G_1 - [\mathsf{anchor}]\,G_0
    /// $$
    #[must_use]
    #[expect(
        clippy::indexing_slicing,
        reason = "the generator table spans every coefficient of a production-rank polynomial"
    )]
    pub fn singleton(anchor: Anchor) -> Self {
        let generators = Pasta::host_generators(pasta::baked()).g();
        Self(Eq::from(generators[1]) - generators[0] * Fp::from(anchor))
    }
}

/// Witness polynomial for a stamp's tachygram set (members encoded as roots).
#[derive(AsRef, Clone, Debug, Into)]
pub struct TachygramSetPoly(Polynomial<Fp, ProductionRank>);

/// Witness polynomial for a stamp's action-digest set (members encoded as
/// roots).
#[derive(AsRef, Clone, Debug, Into)]
pub struct ActionSetPoly(Polynomial<Fp, ProductionRank>);

/// Witness polynomial for an anchor span's member set (members encoded as
/// roots).
#[derive(AsRef, Clone, Debug, Into)]
pub struct AnchorSetPoly(Polynomial<Fp, ProductionRank>);

impl AnchorSetPoly {
    /// Deterministic (untrapdoored) commitment to the set polynomial.
    #[must_use]
    pub fn commit(&self) -> AnchorSetCommit {
        AnchorSetCommit(self.0.commit(Pasta::host_generators(pasta::baked())))
    }

    /// Evaluate the set polynomial at a given point.
    #[must_use]
    pub fn eval(&self, x: Fp) -> Fp {
        self.0.eval(x)
    }
}

impl FromIterator<Anchor> for AnchorSetPoly {
    fn from_iter<I: IntoIterator<Item = Anchor>>(iter: I) -> Self {
        Self(multiset::encode(iter.into_iter().map(Fp::from)))
    }
}

impl TachygramSetPoly {
    /// Deterministic (untrapdoored) commitment to the set polynomial.
    #[must_use]
    pub fn commit(&self) -> TachygramSetCommit {
        TachygramSetCommit(self.0.commit(Pasta::host_generators(pasta::baked())))
    }

    /// Evaluate the set polynomial at a given point.
    #[must_use]
    pub fn eval(&self, x: Fp) -> Fp {
        self.0.eval(x)
    }
}

impl ActionSetPoly {
    /// Deterministic (untrapdoored) commitment to the set polynomial.
    #[must_use]
    pub fn commit(&self) -> ActionSetCommit {
        ActionSetCommit(self.0.commit(Pasta::host_generators(pasta::baked())))
    }

    /// Evaluate the set polynomial at a given point.
    #[must_use]
    pub fn eval(&self, x: Fp) -> Fp {
        self.0.eval(x)
    }
}

impl FromIterator<ActionDigest> for ActionSetPoly {
    fn from_iter<I: IntoIterator<Item = ActionDigest>>(iter: I) -> Self {
        Self(multiset::encode(iter.into_iter().map(Fp::from)))
    }
}

impl FromIterator<Tachygram> for TachygramSetPoly {
    fn from_iter<I: IntoIterator<Item = Tachygram>>(iter: I) -> Self {
        Self(multiset::encode(iter.into_iter().map(Fp::from)))
    }
}
