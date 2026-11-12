#![allow(clippy::min_ident_chars, reason = "test code")]

use super::*;
use crate::primitives::TachygramSetCommit;

#[test]
fn empty_stamp_bridge_hash_matches_application() {
    let prepared = TachygramSetBridge::empty().unwrap();
    let coordinates =
        <[pasta::Fp; 2]>::from(pasta::EpAffine::from(prepared).coordinates().unwrap());
    assert_eq!(*EMPTY_STAMP_BRIDGE_HASH, coordinates);

    let expected = TachygramSetCommit::default().bridge().unwrap();
    assert_eq!(prepared, expected);
}
