use ark_bls12_381::{Fr, G1Projective};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use num_bigint::{BigUint, RandBigInt};

use crate::setup::Lambda;

#[derive(Clone)]
pub struct S1Blindings {
    pub d_y1: BigUint,
    pub d_star_y1: G1Projective,
}

#[derive(Clone)]
pub struct S1Responses {
    pub z_y: BigUint,
    pub z_r_y1: BigUint,
    pub z_r_star_y1: BigUint,
}

#[derive(Clone)]
pub struct S1Proof {
    pub blindings: S1Blindings,
    pub responses: S1Responses,
    pub challenge: BigUint,
}

pub struct S1Witness<'a> {
    pub y: &'a BigUint,
    pub r_y1: &'a BigUint,
    pub r_star_y1: &'a BigUint,
}

pub fn prove_s1(
    lambda: &Lambda,
    c_y1: &BigUint,
    c_star_y1: &G1Projective,
    witness: S1Witness<'_>,
) -> Option<S1Proof> {
    let expected_c_y1 = rust::commit_df_with_opening(&lambda.cpar, witness.y, witness.r_y1).ok()?;
    if &expected_c_y1.c != c_y1 {
        return None;
    }

    let expected_c_star_y1 =
        rust::com_pedersen(&lambda.cpar_star, witness.y, witness.r_star_y1).ok()?;
    if &expected_c_star_y1 != c_star_y1 {
        return None;
    }

    let mut rng = ark_std::rand::rngs::OsRng;
    let s_y = rng.gen_biguint(blinding_bits_y(lambda));
    let s_r_y1 = rng.gen_biguint(blinding_bits_r(lambda));
    let s_r_star_y1 = rng.gen_biguint(blinding_bits_r(lambda));

    let d_y1 = rust::commit_df_with_opening(&lambda.cpar, &s_y, &s_r_y1)
        .ok()?
        .c;
    let d_star_y1 = rust::com_pedersen(&lambda.cpar_star, &s_y, &s_r_star_y1).ok()?;
    let blindings = S1Blindings { d_y1, d_star_y1 };

    let challenge = challenge(lambda, c_y1, c_star_y1, &blindings);
    let responses = S1Responses {
        z_y: s_y + &challenge * witness.y,
        z_r_y1: s_r_y1 + &challenge * witness.r_y1,
        z_r_star_y1: s_r_star_y1 + &challenge * witness.r_star_y1,
    };

    Some(S1Proof {
        blindings,
        responses,
        challenge,
    })
}

pub fn verify_s1(
    lambda: &Lambda,
    c_y1: &BigUint,
    c_star_y1: &G1Projective,
    proof: &S1Proof,
) -> bool {
    let expected_challenge = challenge(lambda, c_y1, c_star_y1, &proof.blindings);
    if expected_challenge != proof.challenge {
        return false;
    }

    let Some(inv_c_y1) = rust::math::modinv(c_y1, &lambda.cpar.n2).ok() else {
        return false;
    };
    let Some(response_c_y1) =
        rust::commit_df_with_opening(&lambda.cpar, &proof.responses.z_y, &proof.responses.z_r_y1)
            .ok()
    else {
        return false;
    };
    let df_expected =
        (response_c_y1.c * inv_c_y1.modpow(&proof.challenge, &lambda.cpar.n2)) % &lambda.cpar.n2;
    if df_expected != proof.blindings.d_y1 {
        return false;
    }

    let Some(response_c_star_y1) = rust::com_pedersen(
        &lambda.cpar_star,
        &proof.responses.z_y,
        &proof.responses.z_r_star_y1,
    )
    .ok() else {
        return false;
    };
    let c = fr_from_biguint(&proof.challenge);
    response_c_star_y1 - (*c_star_y1 * c) == proof.blindings.d_star_y1
}

fn fr_from_biguint(value: &BigUint) -> Fr {
    Fr::from_le_bytes_mod_order(&value.to_bytes_le())
}

fn blinding_bits_y(lambda: &Lambda) -> u64 {
    let bits = lambda.cpar.n.bits() + (lambda.lambda_blue.lambda_bits as u64) * 2;
    bits.max(1)
}

fn blinding_bits_r(lambda: &Lambda) -> u64 {
    let bits =
        rust::math::derive_b_bits_from_n2(&lambda.cpar.n2).unwrap_or(lambda.cpar.n.bits() as usize);
    (bits + lambda.lambda_blue.lambda_bits * 2)
        .try_into()
        .unwrap_or(u64::MAX)
}

fn challenge(
    lambda: &Lambda,
    c_y1: &BigUint,
    c_star_y1: &G1Projective,
    blindings: &S1Blindings,
) -> BigUint {
    let mut transcript = Vec::new();
    append_bytes(&mut transcript, b"S1-FS-v1");
    append_biguint(&mut transcript, &lambda.cpar.n);
    append_biguint(&mut transcript, &lambda.cpar.n2);
    append_biguint(&mut transcript, &lambda.cpar.g);
    append_biguint(&mut transcript, &lambda.cpar.h);
    append_biguint(&mut transcript, &BigUint::from(blinding_bits_r(lambda)));
    append_ser(&mut transcript, &lambda.cpar_star.g1);
    append_ser(&mut transcript, &lambda.cpar_star.h1);
    append_biguint(&mut transcript, &fr_order());
    append_biguint(&mut transcript, c_y1);
    append_ser(&mut transcript, c_star_y1);
    append_biguint(&mut transcript, &blindings.d_y1);
    append_ser(&mut transcript, &blindings.d_star_y1);

    let digest = rust::fiat_shamir_challenge(&[&transcript]);
    BigUint::from_bytes_be(&digest)
}

fn fr_order() -> BigUint {
    BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le())
}

fn append_ser<T: CanonicalSerialize>(out: &mut Vec<u8>, value: &T) {
    let mut bytes = Vec::new();
    value
        .serialize_compressed(&mut bytes)
        .expect("canonical serialization should not fail");
    append_bytes(out, &bytes);
}

fn append_biguint(out: &mut Vec<u8>, value: &BigUint) {
    append_bytes(out, &value.to_bytes_be());
}

fn append_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    let len = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_lambda() -> Lambda {
        let cpar_star = rust::setup_pedersen(64).expect("setup_pedersen should succeed");
        crate::setup::setup(64, 3, cpar_star)
    }

    #[test]
    fn test_s1_accepts_valid_openings() {
        let lambda = test_lambda();
        let y = BigUint::from(11u32);
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let c_y1 = rust::commit_df_with_opening(&lambda.cpar, &y, &r_y1)
            .expect("DF commitment should succeed")
            .c;
        let c_star_y1 =
            rust::com_pedersen(&lambda.cpar_star, &y, &r_star_y1).expect("Pedersen should succeed");

        let proof = prove_s1(
            &lambda,
            &c_y1,
            &c_star_y1,
            S1Witness {
                y: &y,
                r_y1: &r_y1,
                r_star_y1: &r_star_y1,
            },
        )
        .expect("S1 proof should be created");

        assert!(verify_s1(&lambda, &c_y1, &c_star_y1, &proof));
    }

    #[test]
    fn test_s1_rejects_tampered_c_star() {
        let lambda = test_lambda();
        let y = BigUint::from(11u32);
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let c_y1 = rust::commit_df_with_opening(&lambda.cpar, &y, &r_y1)
            .expect("DF commitment should succeed")
            .c;
        let c_star_y1 =
            rust::com_pedersen(&lambda.cpar_star, &y, &r_star_y1).expect("Pedersen should succeed");
        let proof = prove_s1(
            &lambda,
            &c_y1,
            &c_star_y1,
            S1Witness {
                y: &y,
                r_y1: &r_y1,
                r_star_y1: &r_star_y1,
            },
        )
        .expect("S1 proof should be created");

        let tampered_c_star_y1 = c_star_y1 + lambda.cpar_star.g1;
        assert!(!verify_s1(&lambda, &c_y1, &tampered_c_star_y1, &proof));
    }

    #[test]
    fn test_s1_prove_rejects_wrong_witness() {
        let lambda = test_lambda();
        let y = BigUint::from(11u32);
        let wrong_y = BigUint::from(12u32);
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let c_y1 = rust::commit_df_with_opening(&lambda.cpar, &y, &r_y1)
            .expect("DF commitment should succeed")
            .c;
        let c_star_y1 =
            rust::com_pedersen(&lambda.cpar_star, &y, &r_star_y1).expect("Pedersen should succeed");

        let proof = prove_s1(
            &lambda,
            &c_y1,
            &c_star_y1,
            S1Witness {
                y: &wrong_y,
                r_y1: &r_y1,
                r_star_y1: &r_star_y1,
            },
        );

        assert!(proof.is_none());
    }
}
