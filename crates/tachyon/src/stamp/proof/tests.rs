#![allow(clippy::min_ident_chars, reason = "test code")]

use ragu_core::drivers::emulator::Emulator;
use udon::field::Field as _;

use super::*;
use crate::primitives::TachygramSetCommit;

#[test]
fn empty_stamp_bridge_hash_matches_application() {
    let prepared = TachygramSetBridge::empty().unwrap();
    let coordinates =
        <[pasta::Fp; 2]>::from(pasta::EpAffine::from(prepared).coordinates().unwrap());
    assert_eq!(*EMPTY_STAMP_BRIDGE_HASH, coordinates);

    // Exercise synthesis without witness values before using the application.
    let mut counter = Emulator::counter();
    let epoch = Element::constant(&mut counter, pasta::Fp::ZERO);
    let [hash_x, hash_y] = coordinates.map(|value| Element::constant(&mut counter, value));
    let [empty_x, empty_y] =
        EMPTY_STAMP_BRIDGE_HASH.map(|coordinate| Element::constant(&mut counter, coordinate));
    let equal_x = hash_x.is_equal(&mut counter, &mut (), &empty_x).unwrap();
    let equal_y = hash_y.is_equal(&mut counter, &mut (), &empty_y).unwrap();
    equal_x
        .and(&mut counter, &equal_y)
        .unwrap()
        .element()
        .enforce_zero(&mut counter)
        .unwrap();
    crate::gadgets::arithmetic::EpochIndex::new(&mut counter, &epoch).unwrap();

    let expected = TachygramSetCommit::default().bridge().unwrap();
    assert_eq!(prepared, expected);
}
