//! Algorithm 11: Decryption
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、私钥 sk_Λ、DF 承诺 C_y2、Escrow2 输出 Z。
//! 输出：(f_t(x, y), π_z) 或 ⊥。
//!
//! 算法流程（忽略 Z 证明 π_y 部分）：
//! 1. 解析 Λ、pk_Λ、sk_Λ、Z；
//! 2. 调用 VerEscrow(Λ, pk_Λ, C_y2, Z) 验证 Escrow 正确性；
//! 3. 若验证通过，调用 BLUE.Dec(Λ_BLUE, sk_Λ2, C_y2, Z_2) 解密；
//! 4. f_t(x, y) = f(x_2, y)；
//! 5. 返回 (f_t(x, y), π_z)。

use num_bigint::BigUint;

use crate::escrow2::Escrow2Output;
use crate::escrow_verify::escrow_verify;
use crate::keygen::{PublicKey, SecretKey};
use crate::setup::Lambda;

/// Algorithm 11 解密输出。
pub struct DecOutput {
    /// 解密结果 f_t(x, y)。
    pub ft: Option<rust::HecEvalInput>,
    /// 解密正确性证明 π_z。
    pub pi_z: rust::PpbDecProof,
}

/// Algorithm 11: Dec(Λ, pk_Λ, sk_Λ, C_y2, Z) -> (f_t(x, y), π_z) 或 ⊥
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ；
/// 3. `sk`：私钥 sk_Λ；
/// 4. `c_y2`：DF 承诺 C_y2；
/// 5. `z`：Escrow2 输出 Z。
///
/// 输出：Some(DecOutput) 或 None（验证失败时）。
pub fn dec(
    lambda: &Lambda,
    pk: &PublicKey,
    sk: &SecretKey,
    c_y2: &BigUint,
    z: &Escrow2Output,
) -> Option<DecOutput> {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    // ============================================================
    // 通过 lambda 直接访问各参数分量。

    // ============================================================
    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // ============================================================
    // 通过 pk 直接访问各公钥分量。

    // ============================================================
    // Step 3: (sk_Λ1, sk_Λ2, sk_SPS) = sk_Λ
    // ============================================================
    // 通过 sk 直接访问各私钥分量。

    // ============================================================
    // Step 4: (Z'_1, Z_2, π_y) = Z
    // ============================================================
    // 通过 z 直接访问各分量。

    // ============================================================
    // Step 5: if VerEscrow(Λ, pk_Λ, C_y2, Z) = 1
    // ============================================================
    if !escrow_verify(lambda, pk, c_y2, z) {
        return None;
    }

    // ============================================================
    // Step 6: (f(x_2, y), π_z) ← BLUE.Dec(Λ_BLUE, sk_Λ2, C_y2, Z_2)
    // ============================================================
    // dec_ppb 内部会：
    //   1. 再次验证 VerEscrow；
    //   2. 调用 HECdec 解密得到 f(x_2, y)；
    //   3. 构造 PoKS3 证明 π_z。
    let dec_result = rust::dec_ppb(
        &lambda.lambda_blue,
        &sk.sk2,
        c_y2,
        &z.z2,
    )
    .ok()?;

    let dec_out = dec_result?;

    // ============================================================
    // Step 7: f_t(x, y) = f(x_2, y)
    // ============================================================
    // BLUE.Dec 输出即为 f_t(x, y)。

    // ============================================================
    // Step 8: return (f_t(x, y), π_z)
    // ============================================================
    Some(DecOutput {
        ft: dec_out.z,
        pi_z: dec_out.pi_z,
    })
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
    // 测试 1: ℓ > t 时，解密应返回有效结果
    // ================================================================
    // x = [1,2,3,4], split: x1=[1,2,3], x2=[4]。
    // Endorse 需要 y_id ∈ x1（sk1 解密），Dec 需要 y_id ∈ x2（sk2 解密）。
    // 由于 x1 ∩ x2 = ∅，分两阶段使用不同 y_id：
    //   - Escrow1 + Endorse 用 y_id=3 ∈ x1，得到有效 SPS 签名 σ_y；
    //   - Escrow2 + Dec 用 y_id=4 ∈ x2，σ_y 只绑定 (C*_y1, inv) 不绑定 y。
    #[test]
    fn test_dec_large_list_returns_result() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 阶段 1：Escrow1 + Endorse（y_id=3 ∈ x1=[1,2,3]）
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

        // 阶段 2：Escrow2 + Dec（y_id=4 ∈ x2=[4]）
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y2 = BigUint::from(67u32);

        let z = crate::escrow2::escrow2(&lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should succeed");

        let result = dec(&lambda, &pk, &sk, &z.c_y2, &z);
        assert!(result.is_some(), "Dec should succeed for valid escrow");
        let dec_out = result.unwrap();
        assert!(dec_out.ft.is_some(), "f_t(x, y) should be Some");
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时，解密应返回有效结果
    // ================================================================

    #[test]
    fn test_dec_small_list_returns_result() {
        let lambda = test_lambda();

        // |x| = 1 ≤ t = 3 → pk_Λ1 = None
        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(42u32),
            y_at: BigUint::from(10u32),
        };
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

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

        let result = dec(&lambda, &pk, &sk, &z.c_y2, &z);
        assert!(result.is_some(), "Dec should succeed for small list");
    }

    // ================================================================
    // 测试 3: VerEscrow 失败时解密应返回 None
    // ================================================================

    #[test]
    fn test_dec_ver_escrow_fails_returns_none() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 阶段 1：Escrow1 + Endorse（y_id=3 ∈ x1）
        let y_endorse = rust::HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y_endorse, &r_y1, &r_star_y1);
        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let endorse_out = crate::endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // 阶段 2：Escrow2（y_id=4 ∈ x2）
        let y_dec = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };

        let z = crate::escrow2::escrow2(&lambda, &pk, &y_dec, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should succeed");

        // 使用错误的公钥解密 → escrow_verify 中 SPS 验证应失败
        let x_wrong: Vec<BigUint> = (1..=8).map(|i| BigUint::from(i as u32)).collect();
        let ((pk_wrong, _), _) = keygen::keygen(&lambda, &x_wrong, &r_x, &s);

        let result = dec(&lambda, &pk_wrong, &sk, &z.c_y2, &z);
        assert!(result.is_none(), "Dec should fail when VerEscrow fails");
    }
}
