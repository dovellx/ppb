//! Algorithm 7: Endorsement
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、私钥 sk_Λ、
//!       列表 X、DF 承诺 C_y1、Pedersen 承诺 C*_y1、
//!       Escrow 输出 Z_1。
//!
//! 输出：σ_SPS（Mercurial Signature）、y*（解密结果，可选）。
//!
//! 算法流程：
//! 1. 解析 Λ 和密钥；
//! 2. 调用 ppb 的 VerEscrow 检验 Z_1 的正确性；
//! 3. 若验证失败，返回 ⊥；
//! 4. 调用 ppb 的 Dec 解密得到 y*；
//! 5. 若 ℓ > t 且 y* = ⊥，构造消息 M = (C*_y1, inv) 并用 Mercurial Signature 签名。

use num_bigint::BigUint;

use ark_bls12_381::G1Projective;

use rust::{HecEvalInput, PpbEscrowOutput};

use mercurial_signature::Signature as MsSignature;

use crate::keygen::{PublicKey, SecretKey};
use crate::setup::Lambda;

/// Algorithm 7: Endorse 的输出结果。
///
/// 字段语义：
/// 1. `sigma_sps`：对消息 M = (C*_y1, inv) 的 Mercurial Signature；
/// 2. `y_star`：Dec 解密输出 y*（前半名单命中时为 Some(y_id, y_at)，否则为 None）。
pub struct EndorseOutput {
    /// σ_SPS = SPS.Sign(sk_SPS, M)，Mercurial Signature 签名。
    pub sigma_sps: Option<MsSignature>,
    /// y* = Dec(Λ, sk_A1, C_y1, Z_1)，解密结果。
    pub y_star: Option<HecEvalInput>,
}

/// Algorithm 7: Endorse(Λ, pk_Λ, sk_Λ, X, C_y1, C*_y1, Z_1) -> (σ_SPS, y*)
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ；
/// 3. `sk`：私钥 sk_Λ；
/// 4. `c_y1`：DF 承诺 C_y1；
/// 5. `c_star_y1`：Pedersen 承诺 C*_y1；
/// 6. `z1`：Escrow1 输出 Z_1。
///
/// 输出：(σ_SPS, y*)。
pub fn endorse(
    lambda: &Lambda,
    pk: &PublicKey,
    sk: &SecretKey,
    c_y1: &BigUint,
    c_star_y1: &G1Projective,
    z1: &PpbEscrowOutput,
) -> EndorseOutput {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t) = Λ
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
    // Step 4: 若 VerEscrow(Λ, pk_Λ1, C_y1, Z_1) = 0，返回 ⊥
    // ============================================================
    // 调用 ppb 的 verify_escrow 检验 Escrow 输出的正确性。
    // verify_escrow 内部会：
    //   1. 调用 verify_pk 验证公钥结构和 PoKS1 证明；
    //   2. 调用 verify_poks2 验证 PoKS2 证明。
    //
    // 注意：verify_escrow 接受 C_y（DF 承诺）而非 y（HecEvalInput）。
    let pk1 = match pk.pk1.as_ref() {
        Some(pk1) => pk1,
        None => {
            return EndorseOutput {
                sigma_sps: None,
                y_star: None,
            };
        }
    };

    let escrow_valid = rust::ppb::verify_escrow(&lambda.lambda_blue, pk1, c_y1, z1)
        .expect("VerEscrow computation failed");

    if !escrow_valid {
        return EndorseOutput {
            sigma_sps: None,
            y_star: None,
        };
    }

    // ============================================================
    // Step 5: y* ← Dec(Λ, sk_Λ1, C_y1, Z_1)
    // ============================================================
    // 调用 ppb 的 dec_ppb 解密 Escrow 输出中的 Ẑ。
    // dec_ppb 内部会：
    //   1. 再次验证 VerEscrow；
    //   2. 调用 HECdec 解密得到 y*；
    //   3. 构造 PoKS3 证明。
    //
    // 注意：dec_ppb 接受 C_y（DF 承诺）而非 y（HecEvalInput）。
    let sk1 = match sk.sk1.as_ref() {
        Some(sk1) => sk1,
        None => {
            return EndorseOutput {
                sigma_sps: None,
                y_star: None,
            };
        }
    };

    let dec_result = rust::dec_ppb(&lambda.lambda_blue, sk1, c_y1, z1)
        .expect("Dec computation failed");

    if let Some(dec_out) = dec_result {
        EndorseOutput {
            sigma_sps: None,
            y_star: dec_out.z,
        }
    } else if let (Some(_pk_sps), Some(sk_sps)) = (&pk.pk_sps, &sk.sk_sps) {
        // ============================================================
        // Step 6: ℓ > t 且 y* = ⊥ 时，构造并签名 M
        // ============================================================
        let msg: Vec<G1Projective> = vec![c_star_y1.clone(), lambda.inv];

        // ============================================================
        // Step 7: σ_SPS ← SPS.Sign(sk_SPS, M)
        // ============================================================
        let mut rng = ark_std::rand::rngs::OsRng;
        let sigma_sps = sk_sps.sign(&mut rng, &lambda.pp, &msg);

        EndorseOutput {
            sigma_sps: Some(sigma_sps),
            y_star: None,
        }
    } else {
        EndorseOutput {
            sigma_sps: None,
            y_star: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

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
    // 测试 1: ℓ > t 且 y 不在前半名单时，Endorse 应返回签名
    // ================================================================

    #[test]
    fn test_endorse_large_list_returns_output() {
        let lambda = test_lambda();

        // |x| = 5 > t = 3 → pk_Λ1 和 pk_SPS 存在
        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 先生成 Escrow1 输出
        let y = HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let output = endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);

        assert!(output.sigma_sps.is_some(), "σ_SPS should exist when y* = ⊥");
        assert!(output.y_star.is_none(), "y* should be None when y is not in the prefix");
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时，Endorse 应返回无签名
    // ================================================================

    #[test]
    fn test_endorse_small_list_no_signature() {
        let lambda = test_lambda();

        // |x| = 2 ≤ t = 3 → pk_Λ1 和 pk_SPS 为 None
        let x = vec![BigUint::from(42u32), BigUint::from(99u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // ℓ ≤ t 时，pk_Λ1 为 None，escrow1 输出全部为 None
        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(10u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        // ℓ ≤ t 时，所有输出应为 None
        assert!(escrow1_out.c_y1.is_none());
        assert!(escrow1_out.c_star_y1.is_none());
        assert!(escrow1_out.z1.is_none());
    }

    // ================================================================
    // 测试 3: σ_SPS 验证通过
    // ================================================================

    #[test]
    fn test_endorse_signature_verifies() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let output = endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);

        // 用 pk_SPS 验证签名
        let pk_sps = pk.pk_sps.as_ref().unwrap();
        let sigma = output.sigma_sps.as_ref().unwrap();
        let msg: Vec<G1Projective> = vec![c_star_y1.clone(), lambda.inv];
        assert!(pk_sps.verify(&lambda.pp, &msg, sigma), "σ_SPS should verify correctly");
    }

    // ================================================================
    // 测试 4: y 在前半名单中时，y* 匹配原始输入且不签名
    // ================================================================

    #[test]
    fn test_endorse_y_star_matches_input() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);
        let escrow1_out = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        let c_y1 = escrow1_out.c_y1.as_ref().unwrap();
        let c_star_y1 = escrow1_out.c_star_y1.as_ref().unwrap();
        let z1 = escrow1_out.z1.as_ref().unwrap();

        let output = endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);

        assert!(output.sigma_sps.is_none(), "σ_SPS should not exist when y* is recovered");
        let y_star = output.y_star.as_ref().unwrap();
        let n = &lambda.cpar.n;
        assert_eq!(y_star.y_id, y.y_id % n, "y*_id should match y_id mod n");
        assert_eq!(y_star.y_at, y.y_at % n, "y*_at should match y_at mod n");
    }
}
