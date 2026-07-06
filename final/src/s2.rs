use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use num_bigint::{BigUint, RandBigInt};

use mercurial_signature::{PublicKey as MsPublicKey, Signature as MsSignature};

use crate::setup::{Crs2, Lambda};

type Gt = PairingOutput<Bls12_381>;

#[derive(Clone)]
pub struct S2Commitments {
    pub c_cy_1: G1Projective,
    pub c_cy_2: G1Projective,
    pub c_sigma1_1: G1Projective,
    pub c_sigma1_2: G1Projective,
    pub c_sigma2_1: G1Projective,
    pub c_sigma2_2: G1Projective,
    pub c_sigma3_1: G2Projective,
    pub c_sigma3_2: G2Projective,
}

#[derive(Clone)]
pub struct S2Blindings {
    pub d_m: G1Projective,
    pub d_inv: G1Projective,
    pub d_y2: BigUint,
    pub d_y1: G1Projective,
    pub d_cy_1: Gt,
    pub d_cy_2: G1Projective,
    pub d_cy_3: G1Projective,
    pub d_sigma1_1: Gt,
    pub d_sigma1_2: G1Projective,
    pub d_sigma1_3: G1Projective,
    pub d_sigma1_4: Gt,
    pub d_sigma1_5: G1Projective,
    pub d_sigma2_1: Gt,
    pub d_sigma2_2: G1Projective,
    pub d_sigma2_3: G1Projective,
    pub d_sigma3_1: Gt,
    pub d_sigma3_2: G2Projective,
    pub d_sigma3_3: G2Projective,
}

#[derive(Clone)]
pub struct S2Responses {
    pub z_m: Fr,
    pub z_rho: Fr,
    pub z_mu: Fr,
    pub z_r: Fr,
    pub z_y: BigUint,
    pub z_r_star_y1: BigUint,
    pub z_ry2: BigUint,
    pub z_ry: Fr,
    pub z_sigma_1: Fr,
    pub z_sigma_2: Fr,
    pub z_sigma_3: Fr,
    pub z_y_mu: Fr,
    pub z_sigma1_m: Fr,
    pub z_sigma1_mu: Fr,
    pub z_sigma2_rho: Fr,
    pub z_sigma3_rho: Fr,
}

#[derive(Clone)]
pub struct S2Proof {
    pub commitments: S2Commitments,
    pub blindings: S2Blindings,
    pub responses: S2Responses,
    pub challenge: BigUint,
}

pub struct S2Witness<'a> {
    pub c_star_y1: &'a G1Projective,
    pub sigma_y: &'a MsSignature,
    pub mu: Fr,
    pub rep_randomness: Fr,
    pub y: &'a BigUint,
    pub r_star_y1: &'a BigUint,
    pub r_y2: &'a BigUint,
}

pub fn prove_s2(
    lambda: &Lambda,
    pk_sps: &MsPublicKey,
    msg_prime: &[G1Projective],
    sigma_prime: &MsSignature,
    c_y2: &BigUint,
    witness: S2Witness<'_>,
) -> Option<S2Proof> {
    if msg_prime.len() != 2 || witness.rep_randomness.is_zero() {
        return None;
    }

    let expected_c_star = rust::com_pedersen(&lambda.cpar_star, witness.y, witness.r_star_y1).ok()?;
    if &expected_c_star != witness.c_star_y1 {
        return None;
    }
    let expected_cy2 = rust::commit_df_with_opening(&lambda.cpar, witness.y, witness.r_y2).ok()?;
    if &expected_cy2.c != c_y2 {
        return None;
    }

    let rho = witness.rep_randomness.inverse()?;
    let m = witness.rep_randomness * witness.mu;

    let (sigma1, sigma2, sigma3) = witness.sigma_y.components();
    let (sigma1_prime, sigma2_prime, sigma3_prime) = sigma_prime.components();
    let crs = &lambda.crs2;
    let mut rng = ark_std::rand::rngs::OsRng;

    let s_m = Fr::rand(&mut rng);
    let s_rho = Fr::rand(&mut rng);
    let s_mu = Fr::rand(&mut rng);
    let s_r = Fr::rand(&mut rng);
    let s_y = rng.gen_biguint(blinding_bits_y(lambda));
    let s_r_star_y1 = rng.gen_biguint(blinding_bits_ry(lambda));
    let s_ry2 = rng.gen_biguint(blinding_bits_ry(lambda));

    let r_y = Fr::rand(&mut rng);
    let r_sigma_1 = Fr::rand(&mut rng);
    let r_sigma_2 = Fr::rand(&mut rng);
    let r_sigma_3 = Fr::rand(&mut rng);

    let r_y_mu = r_y * witness.mu;
    let r_sigma1_m = r_sigma_1 * m;
    let r_sigma1_mu = r_sigma_1 * witness.mu;
    let r_sigma2_rho = r_sigma_2 * rho;
    let r_sigma3_rho = r_sigma_3 * rho;

    let s_ry = Fr::rand(&mut rng);
    let s_sigma_1 = Fr::rand(&mut rng);
    let s_sigma_2 = Fr::rand(&mut rng);
    let s_sigma_3 = Fr::rand(&mut rng);
    let s_y_mu = Fr::rand(&mut rng);
    let s_sigma1_m = Fr::rand(&mut rng);
    let s_sigma1_mu = Fr::rand(&mut rng);
    let s_sigma2_rho = Fr::rand(&mut rng);
    let s_sigma3_rho = Fr::rand(&mut rng);

    let commitments = S2Commitments {
        c_cy_1: *witness.c_star_y1 + crs.h2 * r_y,
        c_cy_2: crs.h3 * r_y,
        c_sigma1_1: sigma1 + crs.h2 * r_sigma_1,
        c_sigma1_2: crs.h3 * r_sigma_1,
        c_sigma2_1: sigma2 + crs.h2 * r_sigma_2,
        c_sigma2_2: crs.h3 * r_sigma_2,
        c_sigma3_1: sigma3 + crs.h2_hat * r_sigma_3,
        c_sigma3_2: crs.h3_hat * r_sigma_3,
    };

    let blindings = S2Blindings {
        d_m: msg_prime[1] * s_r - lambda.inv * s_m,
        d_inv: lambda.inv * s_mu,
        d_y2: df_commit_parts(&lambda.cpar, &s_y, &s_ry2),
        d_y1: lambda.cpar_star.g1 * fr_from_biguint(&s_y)
            + lambda.cpar_star.h1 * fr_from_biguint(&s_r_star_y1)
            + crs.h2 * s_ry,
        d_cy_1: pair(commitments.c_cy_1 * s_mu, crs.p_hat) - pair(crs.h2 * s_y_mu, crs.p_hat),
        d_cy_2: crs.h3 * s_ry,
        d_cy_3: commitments.c_cy_2 * s_mu - crs.h3 * s_y_mu,
        d_sigma1_1: pair(commitments.c_sigma1_1 * s_m, crs.p_hat)
            - pair(crs.h2 * s_sigma1_m, crs.p_hat),
        d_sigma1_2: crs.h3 * s_sigma_1,
        d_sigma1_3: commitments.c_sigma1_2 * s_m - crs.h3 * s_sigma1_m,
        d_sigma1_4: pair(sigma1_prime * s_rho, crs.p_hat)
            + pair(crs.h2 * s_sigma1_mu, crs.p_hat)
            - pair(commitments.c_sigma1_1 * s_mu, crs.p_hat),
        d_sigma1_5: commitments.c_sigma1_2 * s_mu - crs.h3 * s_sigma1_mu,
        d_sigma2_1: pair(commitments.c_sigma2_1 * s_rho, crs.p_hat)
            - pair(crs.h2 * s_sigma2_rho, crs.p_hat),
        d_sigma2_2: crs.h3 * s_sigma_2,
        d_sigma2_3: commitments.c_sigma2_2 * s_rho - crs.h3 * s_sigma2_rho,
        d_sigma3_1: pair(crs.p, commitments.c_sigma3_1 * s_rho)
            - pair(crs.p, crs.h2_hat * s_sigma3_rho),
        d_sigma3_2: crs.h3_hat * s_sigma_3,
        d_sigma3_3: commitments.c_sigma3_2 * s_rho - crs.h3_hat * s_sigma3_rho,
    };

    let challenge = challenge(
        lambda,
        pk_sps,
        msg_prime,
        sigma_prime,
        c_y2,
        &commitments,
        &blindings,
    );
    let c_fr = fr_from_biguint(&challenge);

    let responses = S2Responses {
        z_m: s_m + c_fr * m,
        z_rho: s_rho + c_fr * rho,
        z_mu: s_mu + c_fr * witness.mu,
        z_r: s_r + c_fr * witness.rep_randomness,
        z_y: s_y + &challenge * witness.y,
        z_r_star_y1: s_r_star_y1 + &challenge * witness.r_star_y1,
        z_ry2: s_ry2 + &challenge * witness.r_y2,
        z_ry: s_ry + c_fr * r_y,
        z_sigma_1: s_sigma_1 + c_fr * r_sigma_1,
        z_sigma_2: s_sigma_2 + c_fr * r_sigma_2,
        z_sigma_3: s_sigma_3 + c_fr * r_sigma_3,
        z_y_mu: s_y_mu + c_fr * r_y_mu,
        z_sigma1_m: s_sigma1_m + c_fr * r_sigma1_m,
        z_sigma1_mu: s_sigma1_mu + c_fr * r_sigma1_mu,
        z_sigma2_rho: s_sigma2_rho + c_fr * r_sigma2_rho,
        z_sigma3_rho: s_sigma3_rho + c_fr * r_sigma3_rho,
    };

    Some(S2Proof {
        commitments,
        blindings,
        responses,
        challenge,
    })
}

pub fn verify_s2(
    lambda: &Lambda,
    pk_sps: &MsPublicKey,
    msg_prime: &[G1Projective],
    sigma_prime: &MsSignature,
    c_y2: &BigUint,
    proof: &S2Proof,
) -> bool {
    if msg_prime.len() != 2 {
        return false;
    }
    let expected_challenge = challenge(
        lambda,
        pk_sps,
        msg_prime,
        sigma_prime,
        c_y2,
        &proof.commitments,
        &proof.blindings,
    );
    if expected_challenge != proof.challenge {
        return false;
    }

    let crs = &lambda.crs2;
    let c = fr_from_biguint(&proof.challenge);
    let z = &proof.responses;
    let cc = &proof.commitments;
    let d = &proof.blindings;
    let (sigma1_prime, sigma2_prime, sigma3_prime) = sigma_prime.components();

    if d.d_m != msg_prime[1] * z.z_r - lambda.inv * z.z_m {
        return false;
    }
    if d.d_inv != lambda.inv * z.z_mu - msg_prime[1] * c {
        return false;
    }
    if !verify_df_y2(&lambda.cpar, &d.d_y2, c_y2, &z.z_y, &z.z_ry2, &proof.challenge) {
        return false;
    }
    if d.d_y1
        != lambda.cpar_star.g1 * fr_from_biguint(&z.z_y)
            + lambda.cpar_star.h1 * fr_from_biguint(&z.z_r_star_y1)
            + crs.h2 * z.z_ry
            - cc.c_cy_1 * c
    {
        return false;
    }
    if d.d_cy_1
        != -pair(msg_prime[0] * c, crs.p_hat)
            + pair(cc.c_cy_1 * z.z_mu, crs.p_hat)
            - pair(crs.h2 * z.z_y_mu, crs.p_hat)
    {
        return false;
    }
    if d.d_cy_2 != crs.h3 * z.z_ry - cc.c_cy_2 * c {
        return false;
    }
    if d.d_cy_3 != cc.c_cy_2 * z.z_mu - crs.h3 * z.z_y_mu {
        return false;
    }
    if d.d_sigma1_1
        != pair(cc.c_sigma1_1 * z.z_m, crs.p_hat)
            - pair(crs.h2 * z.z_sigma1_m, crs.p_hat)
            - pair(sigma1_prime * c, crs.p_hat)
    {
        return false;
    }
    if d.d_sigma1_2 != crs.h3 * z.z_sigma_1 - cc.c_sigma1_2 * c {
        return false;
    }
    if d.d_sigma1_3 != cc.c_sigma1_2 * z.z_m - crs.h3 * z.z_sigma1_m {
        return false;
    }
    if d.d_sigma1_4
        != pair(sigma1_prime * z.z_rho, crs.p_hat)
            + pair(crs.h2 * z.z_sigma1_mu, crs.p_hat)
            - pair(cc.c_sigma1_1 * z.z_mu, crs.p_hat)
    {
        return false;
    }
    if d.d_sigma1_5 != cc.c_sigma1_2 * z.z_mu - crs.h3 * z.z_sigma1_mu {
        return false;
    }
    if d.d_sigma2_1
        != pair(cc.c_sigma2_1 * z.z_rho, crs.p_hat)
            - pair(crs.h2 * z.z_sigma2_rho, crs.p_hat)
            - pair(sigma2_prime * c, crs.p_hat)
    {
        return false;
    }
    if d.d_sigma2_2 != crs.h3 * z.z_sigma_2 - cc.c_sigma2_2 * c {
        return false;
    }
    if d.d_sigma2_3 != cc.c_sigma2_2 * z.z_rho - crs.h3 * z.z_sigma2_rho {
        return false;
    }
    if d.d_sigma3_1
        != pair(crs.p, cc.c_sigma3_1 * z.z_rho)
            - pair(crs.p, crs.h2_hat * z.z_sigma3_rho)
            - pair(crs.p, sigma3_prime * c)
    {
        return false;
    }
    if d.d_sigma3_2 != crs.h3_hat * z.z_sigma_3 - cc.c_sigma3_2 * c {
        return false;
    }
    if d.d_sigma3_3 != cc.c_sigma3_2 * z.z_rho - crs.h3_hat * z.z_sigma3_rho {
        return false;
    }

    true
}

pub fn map_eval_input_to_scalar(y: &rust::HecEvalInput, n: &BigUint) -> BigUint {
    ((&y.y_id % n) + (&y.y_at % n)) % n
}

fn pair(g1: G1Projective, g2: G2Projective) -> Gt {
    Bls12_381::pairing(g1, g2)
}

fn fr_from_biguint(value: &BigUint) -> Fr {
    Fr::from_le_bytes_mod_order(&value.to_bytes_le())
}

fn df_commit_parts(cpar: &rust::DfParams, y: &BigUint, r: &BigUint) -> BigUint {
    (&cpar.g.modpow(y, &cpar.n2) * &cpar.h.modpow(r, &cpar.n2)) % &cpar.n2
}

fn verify_df_y2(
    cpar: &rust::DfParams,
    lhs: &BigUint,
    c_y2: &BigUint,
    z_y: &BigUint,
    z_ry2: &BigUint,
    challenge: &BigUint,
) -> bool {
    let Some(inv_cy2) = rust::math::modinv(c_y2, &cpar.n2).ok() else {
        return false;
    };
    let rhs = (&df_commit_parts(cpar, z_y, z_ry2) * &inv_cy2.modpow(challenge, &cpar.n2)) % &cpar.n2;
    lhs == &rhs
}

fn blinding_bits_y(lambda: &Lambda) -> u64 {
    let bits = lambda.cpar.n.bits() + (lambda.lambda_blue.lambda_bits as u64) * 2;
    bits.max(1)
}

fn blinding_bits_ry(lambda: &Lambda) -> u64 {
    let b = rust::math::derive_b_bits_from_n2(&lambda.cpar.n2).unwrap_or(lambda.cpar.n.bits() as usize);
    (b + lambda.lambda_blue.lambda_bits * 2).try_into().unwrap_or(u64::MAX)
}

fn challenge(
    lambda: &Lambda,
    pk_sps: &MsPublicKey,
    msg_prime: &[G1Projective],
    sigma_prime: &MsSignature,
    c_y2: &BigUint,
    commitments: &S2Commitments,
    blindings: &S2Blindings,
) -> BigUint {
    let mut transcript = Vec::new();
    append_bytes(&mut transcript, b"S2-FS-v1");
    append_crs2(&mut transcript, &lambda.crs2, lambda);
    append_ser(&mut transcript, pk_sps);
    append_g1_slice(&mut transcript, msg_prime);
    let (sig1, sig2, sig3) = sigma_prime.components();
    append_ser(&mut transcript, &sig1);
    append_ser(&mut transcript, &sig2);
    append_ser(&mut transcript, &sig3);
    append_biguint(&mut transcript, c_y2);
    append_ser(&mut transcript, &lambda.inv);
    append_commitments(&mut transcript, commitments);
    append_blindings(&mut transcript, blindings);

    let digest = rust::fiat_shamir_challenge(&[&transcript]);
    BigUint::from_bytes_be(&digest)
}

fn append_crs2(out: &mut Vec<u8>, crs2: &Crs2, lambda: &Lambda) {
    append_ser(out, &lambda.pp.p1);
    append_ser(out, &lambda.pp.p2);
    append_biguint(out, &lambda.cpar.n);
    append_biguint(out, &lambda.cpar.n2);
    append_biguint(out, &lambda.cpar.g);
    append_biguint(out, &lambda.cpar.h);
    append_ser(out, &lambda.cpar_star.g1);
    append_ser(out, &lambda.cpar_star.h1);
    append_ser(out, &crs2.h2);
    append_ser(out, &crs2.h3);
    append_ser(out, &crs2.h2_hat);
    append_ser(out, &crs2.h3_hat);
    append_ser(out, &crs2.p);
    append_ser(out, &crs2.p_hat);
}

fn append_commitments(out: &mut Vec<u8>, c: &S2Commitments) {
    append_ser(out, &c.c_cy_1);
    append_ser(out, &c.c_cy_2);
    append_ser(out, &c.c_sigma1_1);
    append_ser(out, &c.c_sigma1_2);
    append_ser(out, &c.c_sigma2_1);
    append_ser(out, &c.c_sigma2_2);
    append_ser(out, &c.c_sigma3_1);
    append_ser(out, &c.c_sigma3_2);
}

fn append_blindings(out: &mut Vec<u8>, d: &S2Blindings) {
    append_ser(out, &d.d_m);
    append_ser(out, &d.d_inv);
    append_biguint(out, &d.d_y2);
    append_ser(out, &d.d_y1);
    append_ser(out, &d.d_cy_1);
    append_ser(out, &d.d_cy_2);
    append_ser(out, &d.d_cy_3);
    append_ser(out, &d.d_sigma1_1);
    append_ser(out, &d.d_sigma1_2);
    append_ser(out, &d.d_sigma1_3);
    append_ser(out, &d.d_sigma1_4);
    append_ser(out, &d.d_sigma1_5);
    append_ser(out, &d.d_sigma2_1);
    append_ser(out, &d.d_sigma2_2);
    append_ser(out, &d.d_sigma2_3);
    append_ser(out, &d.d_sigma3_1);
    append_ser(out, &d.d_sigma3_2);
    append_ser(out, &d.d_sigma3_3);
}

fn append_g1_slice(out: &mut Vec<u8>, values: &[G1Projective]) {
    append_bytes(out, &(values.len() as u64).to_be_bytes());
    for value in values {
        append_ser(out, value);
    }
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
