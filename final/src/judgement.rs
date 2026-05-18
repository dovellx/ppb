//! Algorithm 12: Judgement
//!
//! The final verification algorithm that checks the entire audit chain.
//! It verifies three conditions simultaneously:
//! 1. VerPK(Λ, pkΛ, Cx) = 1 (public key is consistent with commitments)
//! 2. VerEscrow(Λ, pkΛ, Cy2, Z) = 1 (escrow output is valid)
//! 3. BLUE.Judge(ΛBLUE, pkΛ2, Cx2, Z2, z, πz) = 1 (decryption proof is valid)
//!
//! All three must pass for the judgement to return 1 (true).
//!
//! Input: Λ, pkΛ, Cx, Cy2, Z, z, πz
//! Output: {0, 1}

use num_bigint::BigUint;

use rust::PpbDecProof;

use crate::commit::PolyCommitment;
use crate::escrow2::Escrow2Output;
use crate::escrow_verify::escrow_verify;
use crate::keygen::PublicKey;
use crate::setup::Lambda;
use crate::verpk::ver_pk;

/// Algorithm 12: Judgement(Λ, pkΛ, Cx, Cy2, Z, z, πz) -> {0, 1}
///
/// The final verification algorithm that validates the entire audit chain
/// by checking three independent conditions.
///
/// Input:
/// 1. `lambda`: global parameters Λ = (pp, cpar*, cpar, inv, ΛBLUE, t, crs1, crs2)
/// 2. `pk`: public key pkΛ = (pkΛ1, pkΛ2, pkSPS)
/// 3. `cx`: commitments Cx = (Cx1, Cx2), where each is a polynomial commitment
/// 4. `cy2`: DF commitment Cy2 = Com(cpar, y; r_y2) ∈ Z_{n^2}
/// 5. `z`: Escrow2 output Z = (Z'1, Z2, πy)
/// 6. `z_dec`: decrypted result z from Dec algorithm (Some(y_id, y_at) or None)
/// 7. `pi_z`: proof πz from Dec algorithm (PoKS3 proof of decryption correctness)
///
/// Output: true (1) if all three checks pass, false (0) otherwise.
pub fn judgement(
    lambda: &Lambda,
    pk: &PublicKey,
    cx: &[Option<PolyCommitment>],
    cy2: &BigUint,
    z: &Escrow2Output,
    z_dec: &Option<rust::HecEvalInput>,
    pi_z: &PpbDecProof,
) -> bool {
    // ============================================================
    // Step 1: (pp, cpar∗, cpar, inv, ΛBLUE, t, crs1, crs2) = Λ
    // ============================================================
    // Global parameters are accessed via the `lambda` struct fields.
    // - pp: lambda.pp (Mercurial Signature public parameters)
    // - cpar*: lambda.cpar_star (Pedersen commitment params)
    // - cpar: lambda.cpar (DF commitment params)
    // - inv: lambda.inv (random G1 element)
    // - ΛBLUE: lambda.lambda_blue (PPB protocol params)
    // - t: lambda.t (threshold)

    // ============================================================
    // Step 2: (pkΛ1, pkΛ2, pkSPS) = pkΛ
    // ============================================================
    // Public key components are accessed via the `pk` struct fields.
    // - pkΛ1: pk.pk1 (first half PPB public key, None when ℓ ≤ t)
    // - pkΛ2: pk.pk2 (second half PPB public key)
    // - pkSPS: pk.pk_sps (Mercurial Signature public key, None when ℓ ≤ t)

    // ============================================================
    // Step 3: (Cx1, Cx2) = Cx
    // ============================================================
    // Commitments are accessed via the `cx` slice.
    // - Cx1: cx[0] (commitment to first half, None when ℓ ≤ t)
    // - Cx2: cx[1] (commitment to second half, always exists)

    // ============================================================
    // Step 4: (Z′1, Z2, πy) = Z
    // ============================================================
    // Escrow2 output components are accessed via the `z` struct fields.
    // - Z'1: z.z1_prime (SPS signature pair, None when pkΛ1 = ⊥)
    // - Z2: z.z2 (BLUE.Escrow output for second half)
    // - πy: z.z2.pi_u (user proof, part of Z2)

    // ============================================================
    // Step 5: if VerPK(Λ, pkΛ, Cx) = 1
    //         and VerEscrow(Λ, pkΛ, Cy2, Z) = 1
    //         and BLUE.Judge(ΛBLUE, pkΛ2, Cx2, Z2, z, πz) = 1
    //         then return 1
    // ============================================================

    // ---- Check 1: VerPK(Λ, pkΛ, Cx) = 1 ----
    // VerPK verifies that the public key is consistent with the commitments.
    // It checks:
    //   - If pkΛ1 ≠ ⊥: BLUE.VerPK(ΛBLUE, pkΛ1, Cx1) = 1
    //   - BLUE.VerPK(ΛBLUE, pkΛ2, Cx2) = 1
    if !ver_pk(lambda, pk, cx) {
        // VerPK failed, return 0
        return false;
    }

    // ---- Check 2: VerEscrow(Λ, pkΛ, Cy2, Z) = 1 ----
    // VerEscrow verifies that the escrow output Z is valid.
    // It internally checks:
    //   - If pkΛ1 ≠ ⊥ and Z'1 ≠ ⊥: SPS.Verify(pkSPS, M', σ') = 1
    //   - BLUE.VerEscrow(ΛBLUE, pkΛ2, Cy2, Z2) = 1
    if !escrow_verify(lambda, pk, cy2, z) {
        // VerEscrow failed, return 0
        return false;
    }

    // ---- Check 3: BLUE.Judge(ΛBLUE, pkΛ2, Cx2, Z2, z, πz) = 1 ----
    // BLUE.Judge verifies the decryption proof and consistency.
    // It internally checks:
    //   - VS3: verify_poks3(ΛBLUE, C_d, πz) = 1 (PoKS3 proof validity)
    //   - VerPK(ΛBLUE, pkΛ2, Cx2) = 1 (public key consistency)
    //   - VerEscrow(ΛBLUE, pkΛ2, Cy2, Z2) = 1 (escrow consistency)
    //
    // Note: BLUE.Judge uses pkΛ2 (the second half public key) and Cx2
    // (the second half commitment), which corresponds to the decryption
    // path where skΛ2 is used to decrypt.

    // Extract Cx2 from the commitment array.
    // Cx2 must exist for the judgement to proceed (it's always generated).
    let cx2 = match cx[1].as_ref() {
        Some(c) => &c.c,
        None => {
            // Cx2 doesn't exist, this is an invalid input
            return false;
        }
    };

    // Call judge_ppb which implements BLUE.Judge.
    // Parameters mapping:
    // - ΛBLUE → lambda.lambda_blue (PPB global parameters)
    // - pkΛ2 → pk.pk2 (second half PPB public key)
    // - Cx2 → cx2 (commitment to x2)
    // - Cy2 → cy2 (commitment to y, from escrow)
    // - Z2 → z.z2 (escrow output for second half)
    // - z → z_dec (decrypted result from Dec)
    // - πz → pi_z (PoKS3 proof from Dec)
    match rust::judge_ppb(
        &lambda.lambda_blue,
        &pk.pk2,
        cx2,
        cy2,
        &z.z2,
        z_dec,
        pi_z,
    ) {
        Ok(true) => {
            // ============================================================
            // Step 6: return 1
            // ============================================================
            // All three checks passed, judgement succeeds.
            true
        }
        _ => {
            // ============================================================
            // Step 7: return 0
            // ============================================================
            // At least one check failed, judgement fails.
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::UniformRand;
    use num_bigint::BigUint;

    use crate::dec;
    use crate::keygen;

    /// Construct test Lambda parameters with fixed security parameter.
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits)
            .expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // Test 1: Valid judgement for ℓ > t case (all checks should pass)
    // ================================================================

    /// When |x| = 4 > t = 3, the full protocol flow should produce
    /// a valid judgement. This tests the happy path where:
    /// - VerPK passes (pk is consistent with Cx)
    /// - VerEscrow passes (escrow output is valid)
    /// - BLUE.Judge passes (decryption proof is valid)
    #[test]
    fn test_judgement_large_list_returns_true() {
        let lambda = test_lambda();

        // KeyGen: |x| = 4 > t = 3 → pkΛ1 and pkSPS exist
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // Escrow1 + Endorse (y_id=3 ∈ x1=[1,2,3])
        // This generates the SPS signature that binds (C*_y1, inv)
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();
        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // Escrow2 (y_id=4 ∈ x2=[4])
        // This generates Z2 and Cy2 for the second half
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);
        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y,
        )
        .expect("Escrow2 should succeed");

        // Dec: decrypt and generate PoKS3 proof
        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed");

        // Judgement: all three checks should pass
        assert!(
            judgement(&lambda, &pk, &c_x, &z.c_y2, &z, &dec_out.ft, &dec_out.pi_z),
            "Judgement should return true for valid ℓ > t inputs"
        );
    }

    // ================================================================
    // Test 2: Valid judgement for ℓ ≤ t case (all checks should pass)
    // ================================================================

    /// When |x| = 1 ≤ t = 3, pkΛ1 = ⊥ and pkSPS = ⊥.
    /// The judgement should still pass because:
    /// - VerPK only checks pkΛ2 with Cx2
    /// - VerEscrow only checks BLUE.VerEscrow for Z2
    /// - BLUE.Judge uses pkΛ2 for decryption verification
    #[test]
    fn test_judgement_small_list_returns_true() {
        let lambda = test_lambda();

        // KeyGen: |x| = 1 ≤ t = 3 → pkΛ1 = None, pkSPS = None
        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(42u32), // must be in x for ℓ ≤ t (full list is x2)
            y_at: BigUint::from(10u32),
        };
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        // ℓ ≤ t: escrow2 uses placeholder signature (pkΛ1 = ⊥ branch)
        let c_star_y1_placeholder = rust::com_pedersen(
            &lambda.cpar_star,
            &BigUint::from(0u32),
            &r_star_y1,
        )
        .expect("Pedersen commitment failed");

        let fake_sig = {
            let mut rng = ark_std::rand::rngs::OsRng;
            let fake_msg: Vec<ark_bls12_381::G1Projective> =
                vec![ark_bls12_381::G1Projective::rand(&mut rng); 2];
            let (_, sk_sps_fake) = lambda.pp.key_gen(&mut rng, 2);
            sk_sps_fake.sign(&mut rng, &lambda.pp, &fake_msg)
        };

        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y, &r_star_y1, &r_y2,
            &c_star_y1_placeholder, &fake_sig,
        )
        .expect("Escrow2 should succeed for small list");

        // Dec
        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed for small list");

        // Judgement should return true
        assert!(
            judgement(&lambda, &pk, &c_x, &z.c_y2, &z, &dec_out.ft, &dec_out.pi_z),
            "Judgement should return true for valid ℓ ≤ t inputs"
        );
    }

    // ================================================================
    // Test 3: Tampered Cx2 should cause VerPK to fail
    // ================================================================

    /// If Cx2 is tampered, VerPK should fail because pkΛ2
    /// is no longer consistent with the modified commitment.
    #[test]
    fn test_judgement_tampered_cx2_fails() {
        let lambda = test_lambda();

        // Full protocol flow
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), mut c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // Escrow1 + Endorse
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();
        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // Escrow2
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);
        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y,
        )
        .expect("Escrow2 should succeed");

        // Dec
        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed");

        // Tamper Cx2: modify the commitment value
        let cx2 = c_x[1].as_mut().unwrap();
        cx2.c = (&cx2.c + BigUint::from(1u32)) % &lambda.cpar.n2;

        // Judgement should fail because VerPK will detect the tampered Cx2
        assert!(
            !judgement(&lambda, &pk, &c_x, &z.c_y2, &z, &dec_out.ft, &dec_out.pi_z),
            "Judgement should return false when Cx2 is tampered"
        );
    }

    // ================================================================
    // Test 4: Tampered Cy2 should cause VerEscrow to fail
    // ================================================================

    /// If Cy2 is tampered, VerEscrow should fail because the
    /// escrow output Z is no longer consistent with the commitment.
    #[test]
    fn test_judgement_tampered_cy2_fails() {
        let lambda = test_lambda();

        // Full protocol flow
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // Escrow1 + Endorse
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();
        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // Escrow2
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);
        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y,
        )
        .expect("Escrow2 should succeed");

        // Dec
        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed");

        // Tamper Cy2: modify the commitment value
        let tampered_cy2 = (&z.c_y2 + BigUint::from(1u32)) % &lambda.cpar.n2;

        // Judgement should fail because VerEscrow will detect the tampered Cy2
        assert!(
            !judgement(&lambda, &pk, &c_x, &tampered_cy2, &z, &dec_out.ft, &dec_out.pi_z),
            "Judgement should return false when Cy2 is tampered"
        );
    }

    // ================================================================
    // Test 5: Tampered πz should cause BLUE.Judge to fail
    // ================================================================

    /// If the PoKS3 proof πz is tampered, BLUE.Judge should fail
    /// because the decryption proof is no longer valid.
    #[test]
    fn test_judgement_tampered_pi_z_fails() {
        let lambda = test_lambda();

        // Full protocol flow
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // Escrow1 + Endorse
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();
        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // Escrow2
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);
        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y,
        )
        .expect("Escrow2 should succeed");

        // Dec
        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed");

        // Tamper πz: modify the PoKS3 proof response
        let mut tampered_pi_z = dec_out.pi_z.clone();
        tampered_pi_z.z_md += num_bigint::BigInt::from(1u32);

        // Judgement should fail because BLUE.Judge will detect the tampered proof
        assert!(
            !judgement(&lambda, &pk, &c_x, &z.c_y2, &z, &dec_out.ft, &tampered_pi_z),
            "Judgement should return false when πz is tampered"
        );
    }

    // ================================================================
    // Test 6: Wrong public key should cause VerPK to fail
    // ================================================================

    /// If a different public key (for a different list) is used,
    /// VerPK should fail because the key is not consistent with Cx.
    #[test]
    fn test_judgement_wrong_pk_fails() {
        let lambda = test_lambda();

        // Original key generation
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // Generate escrow with original key
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();
        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);
        let z = crate::escrow2::escrow2(
            &lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y,
        )
        .expect("Escrow2 should succeed");

        let dec_out = dec::dec(&lambda, &pk, &sk, &z.c_y2, &z)
            .expect("Dec should succeed");

        // Generate a different key pair (for a different list)
        let x_wrong: Vec<BigUint> = (1..=8).map(|i| BigUint::from(i as u32)).collect();
        let ((pk_wrong, _), _) = keygen::keygen(&lambda, &x_wrong, &r_x, &s);

        // Judgement should fail because pk_wrong is not consistent with c_x
        assert!(
            !judgement(&lambda, &pk_wrong, &c_x, &z.c_y2, &z, &dec_out.ft, &dec_out.pi_z),
            "Judgement should return false when using wrong public key"
        );
    }
}
