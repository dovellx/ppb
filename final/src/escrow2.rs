//! Algorithm 8: Escrow2
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、评估输入 y、
//!       Pedersen 承诺随机数 r*_y1、DF 承诺随机数 r_y2、
//!       Pedersen 承诺 C*_y1、签名 σ_y。
//!
//! 输出：Z（包含 Z'_1, Z_2）、C_y2（DF 承诺）。
//!
//! 算法流程：
//! 1. 解析 Λ 和 pk_Λ；
//! 2. 调用 BLUE.Escrow 生成 Z_2；
//! 3. 使用 DF 承诺方案计算 C_y2 = Com(cpar, y; r_y2)；
//! 4. 若 pk_Λ1 = ⊥，返回 Z = ((⊥,⊥), Z_2), C_y2；
//! 5. 若 pk_Λ1 ≠ ⊥ 且 SPS.Verify(pk_SPS, M, σ_y) = 1，
//!    采样 µ 并调用 ChangeRep 得到 M', σ'_y，
//!    返回 Z = ((M', σ'_y), Z_2), C_y2；
//! 6. 否则返回 ⊥。

use num_bigint::BigUint;
use ark_ff::UniformRand;

use ark_bls12_381::G1Projective;

use rust::{escrow_ppb, HecEvalInput, PpbEscrowOutput};

use mercurial_signature::Signature as MsSignature;

use crate::keygen::PublicKey;
use crate::setup::Lambda;

/// SPS.ChangeRep 后的消息-签名对 (M', σ'_y)。
///
/// 字段语义：
/// 1. `msg`：变换后的消息 M' = µ · M（每个 G1 点乘以标量 µ）；
/// 2. `sig`：变换后的签名 σ'_y。
pub struct EscrowZ1Prime {
    /// M' = (µ · C*_y1, µ · inv)。
    pub msg: Vec<G1Projective>,
    /// σ'_y = SPS.ChangeRep(σ_y, µ; r)。
    pub sig: MsSignature,
}

/// Algorithm 8: Escrow2 的输出结果。
///
/// 字段语义：
/// 1. `z1_prime`：Z'_1 = (M', σ'_y)，
///    当 pk_Λ1 = ⊥ 时为 Some(EscrowZ1Prime { msg: vec![], sig: ... })（空消息），
///    当 pk_Λ1 ≠ ⊥ 且验证通过时为 Some(...)（非空），
///    当验证失败时整个函数返回 None；
/// 2. `z2`：BLUE.Escrow(Λ_BLUE, pk_Λ2, y; r_y2)；
/// 3. `c_y2`：DF 承诺值 C_y2 = Com(cpar, y; r_y2) ∈ Z_{n^2}。
pub struct Escrow2Output {
    /// Z'_1 = (M', σ'_y)，pk_Λ1 = ⊥ 时 msg 为空。
    pub z1_prime: Option<EscrowZ1Prime>,
    /// Z_2 = BLUE.Escrow(Λ_BLUE, pk_Λ2, y; r_y2)。
    pub z2: PpbEscrowOutput,
    /// C_y2 = Com(cpar, y; r_y2)，DF 承诺值。
    pub c_y2: BigUint,
}

/// Algorithm 8: Escrow2(Λ, pk_Λ, y, r*_y1, r_y2, C*_y1, σ_y) -> (Z, C_y2)
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)；
/// 3. `y`：评估输入，包含 y_id 和 y_at 两个分量；
/// 4. `r_star_y1`：Pedersen 承诺随机数（用于 C*_y1 的生成，当前仅传递）；
/// 5. `r_y2`：DF 承诺随机数；
/// 6. `c_star_y1`：Pedersen 承诺 C*_y1（来自 Escrow1）；
/// 7. `sigma_y`：签名 σ_y（来自 Endorse）。
///
/// 输出：Some((Z, C_y2)) 或 None（验证失败时）。
pub fn escrow2(
    lambda: &Lambda,
    pk: &PublicKey,
    y: &HecEvalInput,
    _r_star_y1: &BigUint,
    r_y2: &BigUint,
    c_star_y1: &G1Projective,
    sigma_y: &MsSignature,
) -> Option<Escrow2Output> {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    // ============================================================
    // 通过 lambda 直接访问各参数分量。

    // ============================================================
    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // ============================================================
    // 通过 pk 直接访问各公钥分量。

    // ============================================================
    // Step 3: Z_2 ← BLUE.Escrow(Λ_BLUE, pk_Λ2, y; r_y2)
    // ============================================================
    // 调用 ppb 的 escrow_ppb 函数生成 Z_2。
    // 该函数内部会：
    //   1. 验证 VerPK(Λ_BLUE, pk_Λ2, C_x2)；
    //   2. 采样 r^Z 并计算 Z_hat = HECeval(hecpar, f, X, y; r^Z)；
    //   3. 计算 C_y = Com_cpar(y; r_y)；
    //   4. 构造 PoKS2 证明 π_U。
    let z2 = escrow_ppb(
        &lambda.lambda_blue,
        &pk.pk2,
        y,
        r_y2,
    )
    .expect("BLUE.Escrow for pk_Λ2 failed")
    .expect("BLUE.Escrow for pk_Λ2 returned ⊥ (VerPK failed)");

    // ============================================================
    // Step 4: C_y2 ← COM.Com(cpar, y; r_y2)
    // ============================================================
    // 将 y 映射为标量消息 m_y = (y_id + y_at) mod n，
    // 然后使用 DF 承诺方案计算 C_y2 = g^{m_y} * h^{r_y2} mod n^2。
    let n = &lambda.cpar.n;
    let m_y = {
        let y_id = &y.y_id % n;
        let y_at = &y.y_at % n;
        (y_id + y_at) % n
    };
    let c_y2 = rust::commit_df_with_opening(&lambda.cpar, &m_y, r_y2)
        .expect("DF commitment computation failed");

    // ============================================================
    // Step 5: if pk_Λ1 = ⊥ then ...
    // ============================================================
    match pk.pk1.as_ref() {
        None => {
            // pk_Λ1 = ⊥ 的情况（ℓ ≤ t）。
            // Z'_1 = (⊥, ⊥)，即空消息。
            Some(Escrow2Output {
                z1_prime: None,
                z2,
                c_y2: c_y2.c,
            })
        }
        Some(_pk1) => {
            // ============================================================
            // Step 6: SPS.Verify(pk_SPS, M = (C*_y1, inv), σ_y)
            // ============================================================
            // 构造消息 M = (C*_y1, inv) 并验证签名 σ_y。
            let msg: Vec<G1Projective> = vec![c_star_y1.clone(), lambda.inv];
            let pk_sps = pk.pk_sps.as_ref().unwrap();
            let sig_valid = pk_sps.verify(&lambda.pp, &msg, sigma_y);

            if !sig_valid {
                // 签名验证失败，返回 ⊥。
                return None;
            }

            // ============================================================
            // Step 7: µ ∈$ MSC; r ∈$ MSR
            // ============================================================
            // 采样随机标量 µ ∈ Fr（BLS12-381 标量域）。
            // r 由 change_representation 内部采样。
            let mut rng = ark_std::rand::rngs::OsRng;
            let mu = ark_bls12_381::Fr::rand(&mut rng);

            // ============================================================
            // Step 8: M', σ'_y ← SPS.ChangeRep(pk_SPS, M, σ_y, µ; r)
            // ============================================================
            // 调用 mercurial-signature 的 change_representation 函数。
            // 该函数会：
            //   1. 内部采样随机标量 f（对应算法中的 r）；
            //   2. 对签名执行 σ'.z = σ.z * (µ * f), σ'.y1 = σ.y1 / f, σ'.y2 = σ.y2 / f；
            //   3. 对消息执行 M'[i] = M[i] * µ。
            // 变换后的 (M', σ'_y) 仍然满足验证等式。
            let mut msg_mut = msg.clone();
            let mut sig_mut = sigma_y.clone();
            mercurial_signature::change_representation(&mut rng, &mut msg_mut, &mut sig_mut, mu);

            // ============================================================
            // Step 9: Z'_1 = (M', σ'_y)
            // ============================================================
            let z1_prime = Some(EscrowZ1Prime {
                msg: msg_mut,
                sig: sig_mut,
            });

            // ============================================================
            // Step 10: return Z = (Z'_1, Z_2), C_y2
            // ============================================================
            Some(Escrow2Output {
                z1_prime,
                z2,
                c_y2: c_y2.c,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    use crate::keygen;
    use crate::endorse;

    /// 构造测试用的 Lambda。
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits)
            .expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: ℓ > t 时，Escrow2 应返回有效输出且 Z'_1 非空
    // ================================================================

    #[test]
    fn test_escrow2_large_list_returns_output() {
        let lambda = test_lambda();

        // |x| = 4 > t = 3 → pk_Λ1 和 pk_SPS 存在
        // split: x1 = [1,2,3] (fk1.n=3, 4 coeffs), x2 = [4] (fk2.n=1, 2 coeffs)
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 生成 Escrow1 输出
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

        // Endorse 生成签名
        let endorse_out = endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        // Escrow2
        let r_y2 = BigUint::from(67u32);
        let output = escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should return Some");

        // pk_Λ1 存在时，Z'_1 应为 Some 且消息非空
        assert!(output.z1_prime.is_some(), "Z'_1 should exist when pk_Λ1 ≠ ⊥");
        let z1p = output.z1_prime.as_ref().unwrap();
        assert_eq!(z1p.msg.len(), 2, "M' should have 2 G1 points");
        assert!(output.c_y2 > BigUint::from(0u32), "C_y2 must be non-zero");
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时，Escrow2 应返回 Z'_1 = None
    // ================================================================

    #[test]
    fn test_escrow2_small_list_z1_prime_none() {
        let lambda = test_lambda();

        // |x| = 1 ≤ t = 3 → pk_Λ1 和 pk_SPS 为 None
        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // ℓ ≤ t 时无法生成 endorse 签名，构造一个占位签名
        // 这里直接测试 escrow2 在 pk_Λ1 = ⊥ 时的行为
        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(10u32),
        };
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        // 由于 ℓ ≤ t 时 endorse 不生成签名，我们需要构造一个假的 σ_y
        // 但 escrow2 在 pk_Λ1 = ⊥ 时不会验证签名（直接走 None 分支）
        // 所以这里用 escrow1 的 c_star_y1 作为占位
        let c_star_y1_placeholder = rust::com_pedersen(
            &lambda.cpar_star,
            &BigUint::from(0u32),
            &r_star_y1,
        ).expect("Pedersen commitment failed");

        // 构造一个假签名（不被使用，因为 pk_Λ1 = ⊥）
        let fake_sig = {
            let mut rng = ark_std::rand::rngs::OsRng;
            let fake_msg: Vec<G1Projective> = vec![G1Projective::rand(&mut rng); 2];
            let sk_sps_fake = {
                let (_, sk_tmp) = lambda.pp.key_gen(&mut rng, 2);
                sk_tmp
            };
            sk_sps_fake.sign(&mut rng, &lambda.pp, &fake_msg)
        };

        let output = escrow2(
            &lambda, &pk, &y, &r_star_y1, &r_y2,
            &c_star_y1_placeholder, &fake_sig,
        )
        .expect("Escrow2 should return Some even when pk_Λ1 = ⊥");

        // pk_Λ1 = ⊥ 时，Z'_1 应为 None
        assert!(output.z1_prime.is_none(), "Z'_1 should be None when pk_Λ1 = ⊥");
        assert!(output.c_y2 > BigUint::from(0u32), "C_y2 must be non-zero");
    }

    // ================================================================
    // 测试 3: ChangeRep 后的签名仍然可验证
    // ================================================================

    #[test]
    fn test_escrow2_change_rep_signature_verifies() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
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

        let endorse_out = endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let r_y2 = BigUint::from(67u32);
        let output = escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should return Some");

        // 验证 ChangeRep 后的 (M', σ'_y) 满足 SPS.Verify(pk_SPS, M', σ'_y) = 1
        let z1p = output.z1_prime.as_ref().unwrap();
        let pk_sps = pk.pk_sps.as_ref().unwrap();
        assert!(
            pk_sps.verify(&lambda.pp, &z1p.msg, &z1p.sig),
            "SPS.Verify(pk_SPS, M', σ'_y) should pass after ChangeRep"
        );
    }

    // ================================================================
    // 测试 4: C_y2 与手动计算一致
    // ================================================================

    #[test]
    fn test_escrow2_cy2_matches_manual_computation() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;
        let n2 = &lambda.cpar.n2;

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
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

        let endorse_out = endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let r_y2 = BigUint::from(67u32);
        let output = escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2, c_star_y1, sigma_y)
            .expect("Escrow2 should return Some");

        // 手动计算：m_y = (3 + 7) mod n = 10
        // C_y2 = g^{10} * h^{67} mod n^2
        let m_y = (BigUint::from(3u32) + BigUint::from(7u32)) % n;
        let expected = (&lambda.cpar.g.modpow(&m_y, n2)
            * &lambda.cpar.h.modpow(&r_y2, n2))
            % n2;

        assert_eq!(output.c_y2, expected);
    }

    // ================================================================
    // 测试 5: 不同的 r_y2 产生不同的 C_y2
    // ================================================================

    #[test]
    fn test_escrow2_different_ry2_different_cy2() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
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

        let endorse_out = endorse::endorse(&lambda, &pk, &sk, c_y1, c_star_y1, z1);
        let sigma_y = endorse_out.sigma_sps.as_ref().unwrap();

        let r_y2_a = BigUint::from(67u32);
        let r_y2_b = BigUint::from(89u32);

        let out_a = escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2_a, c_star_y1, sigma_y)
            .expect("Escrow2 should return Some");
        let out_b = escrow2(&lambda, &pk, &y, &r_star_y1, &r_y2_b, c_star_y1, sigma_y)
            .expect("Escrow2 should return Some");

        assert_ne!(out_a.c_y2, out_b.c_y2, "different r_y2 should yield different C_y2");
    }
}
