use mercurial_signature::{change_representation, Fr, PublicParams, UniformRand, G1};

/// Test the conversion function for the public key, secret key, and signature.
/// The converted public key, secret key, and signature should be able to verify the message.
#[test]
fn verify_ok_for_original_message_with_converted_keys_and_sigs() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);
    let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let sig = sk.sign(&mut rng, &pp, &message);

    let p = Fr::rand(&mut rng);

    let mut pk2 = pk.clone();
    pk2.convert(p);
    assert!(pk != pk2);

    let mut sk2 = sk.clone();
    sk2.convert(p);
    assert!(sk != sk2);

    let mut sig2 = sig.clone();
    sig2.convert(&mut rng, p);
    assert!(sig != sig2);

    // The converted public key, secret key, and signature should be able to verify the message.
    assert!(pk2.verify(&pp, &message, &sig2));

    // The converted secret key should be able to sign the message.
    let sig3 = sk2.sign(&mut rng, &pp, &message);
    assert!(pk2.verify(&pp, &message, &sig3));
}

/// Test the conversion function for the public key, secret key, and signature.
/// The converted public key and secret key should be able to sign and verify the message.
#[test]
fn verify_ok_with_converted_keys() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);

    let p = Fr::rand(&mut rng);

    let mut pk2 = pk.clone();
    pk2.convert(p);
    assert!(pk != pk2);

    let mut sk2 = sk.clone();
    sk2.convert(p);
    assert!(sk != sk2);

    // verify the converted public key and secret key can sign and verify the message
    let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let sig2 = sk2.sign(&mut rng, &pp, &message);
    assert!(pk2.verify(&pp, &message, &sig2));
}

/// Test the conversion function for the public key and secret key.
/// The converted key should not be able to verify the message with another unconverted key.
#[test]
fn verify_fail_if_key_is_not_converted() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);

    let p = Fr::rand(&mut rng);

    let mut pk2 = pk.clone();
    pk2.convert(p);
    assert!(pk != pk2);

    let mut sk2 = sk.clone();
    sk2.convert(p);
    assert!(sk != sk2);

    let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();

    // use sk to sign and pk2 to verify
    let sig = sk2.sign(&mut rng, &pp, &message);
    assert!(!pk.verify(&pp, &message, &sig));

    // use sk2 to sign and pk to verify
    let sig2 = sk.sign(&mut rng, &pp, &message);
    assert!(!pk2.verify(&pp, &message, &sig2));
}

/// Test the conversion function for the public key, secret key, and signature.
/// The converted public key, secret key should not be able to verify the message
/// with the original signature.
#[test]
fn verify_fail_if_signature_is_not_converted() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);
    let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let sig = sk.sign(&mut rng, &pp, &message);

    let p = Fr::rand(&mut rng);

    let mut pk2 = pk.clone();
    pk2.convert(p);
    assert!(pk != pk2);

    // use the converted keys to verify the original signature
    assert!(!pk2.verify(&pp, &message, &sig));
}

#[test]
fn verify_ok_if_key_length_is_greater_than_message_length() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);

    let message = (0..5).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let sig = sk.sign(&mut rng, &pp, &message);
    assert!(pk.verify(&pp, &message, &sig));
}

/// Test the conversion function works with the change representation function.
#[test]
fn verify_ok_with_conversion_and_then_change_representation() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (mut pk, mut sk) = pp.key_gen(&mut rng, 10);
    let mut message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let mut sig = sk.sign(&mut rng, &pp, &message);

    let p = Fr::rand(&mut rng);
    pk.convert(p);
    sk.convert(p);
    sig.convert(&mut rng, p);

    let u = Fr::rand(&mut rng);
    change_representation(&mut rng, &mut message, &mut sig, u);
    assert!(pk.verify(&pp, &message, &sig));
}

#[test]
fn verify_ok_with_change_representation_and_then_conversion() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (mut pk, mut sk) = pp.key_gen(&mut rng, 10);
    let mut message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let mut sig = sk.sign(&mut rng, &pp, &message);

    let u = Fr::rand(&mut rng);
    change_representation(&mut rng, &mut message, &mut sig, u);

    let p = Fr::rand(&mut rng);
    pk.convert(p);
    sk.convert(p);
    sig.convert(&mut rng, p);

    assert!(pk.verify(&pp, &message, &sig));
}

/// Test the change representation function -
/// 1. The original message and changed signature should not be able to verify.
/// 2. The changed message and original signature should not be able to verify.
#[test]
fn verify_fail_if_representation_has_not_changed() {
    let mut rng = rand::thread_rng();
    let pp = PublicParams::new(&mut rng);
    let (pk, sk) = pp.key_gen(&mut rng, 10);
    let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    let sig = sk.sign(&mut rng, &pp, &message);

    let u = Fr::rand(&mut rng);
    let mut message2 = message.clone();
    let mut sig2 = sig.clone();
    change_representation(&mut rng, &mut message2, &mut sig2, u);

    // verify the original message and changed signature
    assert!(!pk.verify(&pp, &message2, &sig));
    // verify the changed message and original signature
    assert!(!pk.verify(&pp, &message, &sig2));
}
