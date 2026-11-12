use udon::field::Field as _;

use super::*;

#[test]
fn bridge_hash_reads_back_from_its_coordinates() {
    let bridge = TachygramSetCommit::default().bridge().unwrap();
    let coordinates: [Fp; 2] = EpAffine::from(bridge).coordinates().unwrap().into();
    assert_eq!(TachygramSetBridge::try_from(coordinates).unwrap(), bridge);
}

#[test]
fn bridge_hash_rejects_the_identity_encoding() {
    assert_eq!(
        TachygramSetBridge::try_from([Fp::ZERO, Fp::ZERO]).unwrap_err(),
        TachygramSetBridgeError::Identity
    );
}

#[test]
fn bridge_hash_rejects_coordinates_off_the_curve() {
    assert_eq!(
        TachygramSetBridge::try_from([Fp::ZERO, Fp::ONE]).unwrap_err(),
        TachygramSetBridgeError::NotOnCurve
    );
}
