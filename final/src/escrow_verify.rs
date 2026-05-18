//! Algorithm 10: Escrow Verification
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、DF 承诺 C_y2、Escrow2 输出 Z。
//! 输出：{0, 1}（验证通过返回 true，失败返回 false）。
//!
//! 算法流程（忽略 ZK 证明 π_y 部分）：
//! 1. 解析 Λ 和 pk_Λ；
//! 2. 解析 Z = (Z'_1, Z_2)；
//! 3. 若 pk_Λ1 ≠ ⊥ 且 Z'_1 ≠ ⊥：
//!    a. 验证 SPS.Verify(pk_SPS, M', σ'_y) = 1；
//!    b. 验证 BLUE.VerEscrow(Λ_BLUE, pk_Λ2, C_y2, Z_2) = 1；
//!    c. 两者均通过则返回 true；
//! 4. 若 pk_Λ1 = ⊥：
//!    a. 验证 BLUE.VerEscrow(Λ_BLUE, pk_Λ2, C_y2, Z_2) = 1；
//!    b. 通过则返回 true；
//! 5. 其余情况返回 false。

use num_bigint::BigUint;

use crate::escrow2::Escrow2Output;
use crate::keygen::PublicKey;
use crate::setup::Lambda;

/// Algorithm 10: EscrowVerify(Λ, pk_Λ, C_y2, Z) -> {0, 1}
///
/// 验证 Escrow2 输出 Z 的正确性。
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)；
/// 3. `c_y2`：DF 承诺 C_y2 = Com(cpar, y; r_y2)；
/// 4. `z`：Escrow2 输出 Z = (Z'_1, Z_2)。
///
/// 输出：true 表示验证通过，false 表示验证失败。
pub fn escrow_verify(
    lambda: &Lambda,
    pk: &PublicKey,
    c_y2: &BigUint,
    z: &Escrow2Output,
) -> bool {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    // ============================================================
    // 通过 lambda 直接访问各参数分量。

    // ============================================================
    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // ============================================================
    // 通过 pk 直接访问各公钥分量。

    // ============================================================
    // Step 3: (Z'_1, Z_2, π_y) = Z
    // ============================================================
    // 通过 z 直接访问各分量。

    match (&pk.pk1, &z.z1_prime) {
        // ============================================================
        // Step 4: pk_Λ1 ≠ ⊥ 且 Z'_1 = (M', σ'_y) ≠ ⊥
        // ============================================================
        (Some(_pk1), Some(z1_prime)) => {
            // ============================================================
            // Step 4a: SPS.Verify(pk_SPS, M', σ'_y) = 1
            // ============================================================
            let pk_sps = match pk.pk_sps.as_ref() {
                Some(pk_sps) => pk_sps,
                None => return false,
            };
            if !pk_sps.verify(&lambda.pp, &z1_prime.msg, &z1_prime.sig) {
                return false;
            }

            // ============================================================
            // Step 4b: BLUE.VerEscrow(Λ_BLUE, pk_Λ2, C_y2, Z_2) = 1
            // ============================================================
            // （忽略 ZKVerifyS2 验证）
            rust::ppb::verify_escrow(&lambda.lambda_blue, &pk.pk2, c_y2, &z.z2)
                .unwrap_or(false)
        }
        // ============================================================
        // Step 7: pk_Λ1 = ⊥（ℓ ≤ t 的情况）
        // ============================================================
        (None, _) => {
            // ============================================================
            // Step 7: BLUE.VerEscrow(Λ_BLUE, pk_Λ2, C_y2, Z_2) = 1
            // ============================================================
            rust::ppb::verify_escrow(&lambda.lambda_blue, &pk.pk2, c_y2, &z.z2)
                .unwrap_or(false)
        }
        // ============================================================
        // Step 9: 其余情况返回 0
        // ============================================================
        // pk_Λ1 ≠ ⊥ 但 Z'_1 = ⊥（不一致状态），验证失败。
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use ark_ff::UniformRand;

    use crate::keygen;

    /// 构造测试用的 Lambda。
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits)
            .expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: ℓ > t 时，合法 Escrow 应验证通过
    // ================================================================

    #[test]
    fn test_escrow_verify_large_list_passes() {
        let lambda = test_lambda();

        // |x| = 4 > t = 3 → pk_Λ1 存在
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 生成完整的 Escrow 流程
        let y = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let z = crate::escrow2::escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should succeed");

        // 验证应通过
        assert!(escrow_verify(&lambda, &pk, &z.c_y2, &z), "Escrow verify should pass for valid escrow");
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时，合法 Escrow 应验证通过
    // ================================================================

    #[test]
    fn test_escrow_verify_small_list_passes() {
        let lambda = test_lambda();

        // |x| = 1 ≤ t = 3 → pk_Λ1 = None
        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(10u32),
        };
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        // ℓ ≤ t 时 escrow2 不需要真实签名
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

        assert!(escrow_verify(&lambda, &pk, &z.c_y2, &z), "Escrow verify should pass for small list");
    }

    // ================================================================
    // 测试 3: 篡改 C_y2 后验证应失败
    // ================================================================
    // 注意：verify_poks2 当前为 stub（直接返回 true），
    // 等 ppb 实现完整验证逻辑后取消 ignore。
    #[test]
    #[ignore]
    fn test_escrow_verify_tampered_cy2_fails() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let z = crate::escrow2::escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should succeed");

        // 篡改 C_y2
        let tampered_c_y2 = &z.c_y2 + BigUint::from(1u32);
        assert!(!escrow_verify(&lambda, &pk, &tampered_c_y2, &z), "Escrow verify should fail for tampered C_y2");
    }

    // ================================================================
    // 测试 4: Escrow Update 后验证应通过（分支 1：完全更新）
    // ================================================================

    #[test]
    fn test_escrow_verify_after_full_update() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_old = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1_old = escrow1_old.c_y1.as_ref().unwrap();
        let c_star_y1_old = escrow1_old.c_star_y1.as_ref().unwrap();
        let z1_old = escrow1_old.z1.as_ref().unwrap();

        let endorse_old = crate::endorse::endorse(&lambda, &pk, &sk, c_y1_old, c_star_y1_old, z1_old);
        let sigma_y_old = endorse_old.sigma_sps.as_ref().unwrap();

        let z_old = crate::escrow2::escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1_old, sigma_y_old)
            .expect("Old Escrow2 should succeed");

        // KeyUpdate: 完全重生成
        let x_prime: Vec<BigUint> = (1..=16).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(5u32)];

        let ((pk_prime, sk_prime), _c_x_prime) = crate::keyupdate::key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // Escrow Update
        let r_y1_prime = BigUint::from(101u32);
        let r_y2_prime = BigUint::from(103u32);
        let r_star_y1_prime = BigUint::from(107u32);

        let update_out = crate::escrow_update::escrow_update(
            &lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1_old, &z_old,
            &pk_prime, &r_y1_prime, &r_y2_prime, &r_star_y1_prime,
            &sk_prime, &x_prime,
        )
        .expect("Escrow update should succeed");

        // 更新后的 Escrow 应通过验证
        assert!(
            escrow_verify(&lambda, &pk_prime, &update_out.c_y2_prime, &update_out.z_prime),
            "Escrow verify should pass after full key update"
        );
    }

    // ================================================================
    // 测试 5: Escrow Update 后验证应通过（分支 2：部分更新）
    // ================================================================

    #[test]
    fn test_escrow_verify_after_partial_update() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_old = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1_old = escrow1_old.c_y1.as_ref().unwrap();
        let c_star_y1_old = escrow1_old.c_star_y1.as_ref().unwrap();
        let z1_old = escrow1_old.z1.as_ref().unwrap();

        let endorse_old = crate::endorse::endorse(&lambda, &pk, &sk, c_y1_old, c_star_y1_old, z1_old);
        let sigma_y_old = endorse_old.sigma_sps.as_ref().unwrap();

        let z_old = crate::escrow2::escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1_old, sigma_y_old)
            .expect("Old Escrow2 should succeed");

        // KeyUpdate: 部分更新
        let x_prime: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_prime, sk_prime), _c_x_prime) = crate::keyupdate::key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // Escrow Update: 分支 2
        let r_y2_prime = BigUint::from(103u32);

        let update_out = crate::escrow_update::escrow_update(
            &lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1_old, &z_old,
            &pk_prime, &BigUint::from(0u32), &r_y2_prime, &BigUint::from(0u32),
            &sk_prime, &x_prime,
        )
        .expect("Escrow update should succeed");

        // 更新后的 Escrow 应通过验证
        assert!(
            escrow_verify(&lambda, &pk_prime, &update_out.c_y2_prime, &update_out.z_prime),
            "Escrow verify should pass after partial key update"
        );
    }
}
