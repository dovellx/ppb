//! Algorithm 6: Escrow1
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、评估输入 y、
//!       DF 承诺随机数 r_y1、Pedersen 承诺随机数 r*_y1。
//!
//! 输出：Z_1（BLUE.Escrow 的输出）、C_y1（DF 承诺）、
//!       C*_y1（Pedersen 承诺）、π_1（ZK 证明，暂未实现）。
//!
//! 算法流程：
//! 1. 解析全局参数 Λ 和公钥 pk_Λ；
//! 2. 若 pk_Λ1 ≠ ⊥，调用 BLUE.Escrow 生成 Z_1；
//! 3. 使用 DF 承诺方案计算 C_y1 = Com(cpar, y; r_y1)；
//! 4. 使用 Pedersen 承诺方案计算 C*_y1 = Com*(cpar*, y; r*_y1)；
//! 5. （暂未实现）生成 ZK 证明 π_1。

use num_bigint::BigUint;

use ark_bls12_381::G1Projective;

use rust::{escrow_ppb, HecEvalInput, PpbEscrowOutput};

use crate::keygen::PublicKey;
use crate::setup::Lambda;

/// Algorithm 6: Escrow1 的输出结果。
///
/// 字段语义：
/// 1. `z1`：BLUE.Escrow 的输出（包含 Z_hat、C_y、π_U），
///    当 pk_Λ1 = ⊥ 时为 None；
/// 2. `c_y1`：DF 承诺值 C_y1 = Com(cpar, y; r_y1) ∈ Z_{n^2}，
///    当 pk_Λ1 = ⊥ 时为 None；
/// 3. `c_star_y1`：Pedersen 承诺值 C*_y1 = Com*(cpar*, y; r*_y1) ∈ G1，
///    当 pk_Λ1 = ⊥ 时为 None；
/// 4. `pi1`：ZK 证明 π_1（暂未实现，保留占位）。
pub struct Escrow1Output {
    /// Z_1 = BLUE.Escrow(Λ_BLUE, pk_Λ1, y; r_y1)。
    pub z1: Option<PpbEscrowOutput>,
    /// C_y1 = Com(cpar, y; r_y1)，DF 承诺值。
    pub c_y1: Option<BigUint>,
    /// C*_y1 = Com*(cpar*, y; r*_y1)，Pedersen 承诺椭圆曲线点。
    pub c_star_y1: Option<G1Projective>,
    // TODO: π_1 ← ZKProveS1(...)
    // 当前暂未实现 ZK 证明，后续接入时扩展此字段。
}

/// 将 HecEvalInput 类型的 y 映射为可被承诺方案使用的标量消息。
///
/// 映射方式与 ppb 模块中 map_y_to_df_message 保持一致：
///   m_y = (y_id + y_at) mod n
///
/// 这样设计的原因：
/// 1. DF 承诺方案的消息类型为单个 BigUint；
/// 2. HecEvalInput 包含两个分量 (y_id, y_at)，需要合并为一个标量；
/// 3. 后续配合 r_y = r_id + r_at (mod n)，可保证
///    C_y = C_id * C_at mod n^2 的同态性质。
fn map_y_to_scalar(y: &HecEvalInput, n: &BigUint) -> BigUint {
    let y_id = &y.y_id % n;
    let y_at = &y.y_at % n;
    (y_id + y_at) % n
}

/// Algorithm 6: Escrow1(Λ, pk_Λ, y, r_y1, r*_y1) -> (Z_1, C_y1, C*_y1, π_1)
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)；
/// 3. `y`：评估输入，包含 y_id 和 y_at 两个分量；
/// 4. `r_y1`：DF 承诺的随机数；
/// 5. `r_star_y1`：Pedersen 承诺的随机数。
///
/// 输出：(Z_1, C_y1, C*_y1, π_1)。
pub fn escrow1(
    lambda: &Lambda,
    pk: &PublicKey,
    y: &HecEvalInput,
    r_y1: &BigUint,
    r_star_y1: &BigUint,
) -> Escrow1Output {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    // ============================================================
    // 通过 lambda 直接访问各参数分量。

    // ============================================================
    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // ============================================================
    // 通过 pk 直接访问各公钥分量。

    // ============================================================
    // Step 4: if pk_Λ1 ≠ ⊥ then ...
    // ============================================================
    if let Some(ref pk1) = pk.pk1 {
        // ============================================================
        // Step 5: Z_1 ← BLUE.Escrow(Λ_BLUE, pk_Λ1, y; r_y1)
        // ============================================================
        // 调用 ppb 的 escrow_ppb 函数。
        // 该函数内部会：
        //   1. 验证 VerPK(Λ_BLUE, pk_Λ1, C_x)；
        //   2. 采样 r^Z 并计算 Z_hat = HECeval(hecpar, f, X, y; r^Z)；
        //   3. 计算 C_y = Com_cpar(y; r_y)；
        //   4. 构造 PoKS2 证明 π_U。
        let z1 = escrow_ppb(
            &lambda.lambda_blue,
            pk1,
            y,
            r_y1,
        )
        .expect("BLUE.Escrow failed")
        .expect("BLUE.Escrow returned ⊥ (VerPK failed)");

        // ============================================================
        // Step 6: C_y1 ← COM.Com(cpar, y; r_y1)
        // ============================================================
        // 将 y 映射为标量消息 m_y = (y_id + y_at) mod n，
        // 然后使用 DF 承诺方案计算 C_y1 = g^{m_y} * h^{r_y1} mod n^2。
        let n = &lambda.cpar.n;
        let m_y = map_y_to_scalar(y, n);
        // 调用 df.rs 中的 commit_df_with_opening 计算 C_y1 = g^{m_y} * h^{r_y1} mod n^2
        let c_y1 = rust::commit_df_with_opening(&lambda.cpar, &m_y, r_y1)
            .expect("DF commitment computation failed");

        // ============================================================
        // Step 7: C*_y1 ← COM*.Com(cpar*, y; r*_y1)
        // ============================================================
        // 使用椭圆曲线 Pedersen 承诺方案计算 C*_y1 = g1 * m_y + h1 * r*_y1。
        // 其中 g1, h1 为 cpar* 中的 BLS12-381 G1 群元素，
        // m_y 为标量消息，r*_y1 为 Pedersen 承诺的随机数。
        let c_star_y1 = rust::com_pedersen(
            &lambda.cpar_star,
            &m_y,
            r_star_y1,
        )
        .expect("Pedersen commitment computation failed");

        // ============================================================
        // Step 8: π_1 ← ZKProveS1(...) —— 暂未实现
        // ============================================================
        // TODO: 生成 ZK 证明 π_1，证明：
        //   C_y1 = COM.Com(cpar, y; r_y1) ∧
        //   C*_y1 = COM*.Com(cpar*, y; r*_y1)
        // 需要后续接入 ZK 证明系统。

        // ============================================================
        // Step 9: return Z_1, C_y1, C*_y1, π_1
        // ============================================================
        Escrow1Output {
            z1: Some(z1),
            c_y1: Some(c_y1.c),
            c_star_y1: Some(c_star_y1),
        }
    } else {
        // ============================================================
        // Step 3: Z_1 = ⊥, π_1 = ⊥（pk_Λ1 = ⊥ 的情况）
        // ============================================================
        // 当 ℓ ≤ t 时，pk_Λ1 为 None，无需执行 Escrow。
        Escrow1Output {
            z1: None,
            c_y1: None,
            c_star_y1: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::Zero;

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
    // 测试 1: ℓ > t 时，Escrow1 应返回有效输出
    // ================================================================

    #[test]
    fn test_escrow1_large_list_returns_output() {
        let lambda = test_lambda();

        // |x| = 5 > t = 3 → pk_Λ1 存在
        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let output = escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        // pk_Λ1 存在时，所有输出应为 Some
        assert!(output.z1.is_some(), "Z_1 should exist when pk_Λ1 ≠ ⊥");
        assert!(output.c_y1.is_some(), "C_y1 should exist when pk_Λ1 ≠ ⊥");
        assert!(output.c_star_y1.is_some(), "C*_y1 should exist when pk_Λ1 ≠ ⊥");
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时，Escrow1 应返回 None
    // ================================================================

    #[test]
    fn test_escrow1_small_list_returns_none() {
        let lambda = test_lambda();

        // |x| = 2 ≤ t = 3 → pk_Λ1 为 None
        let x = vec![BigUint::from(42u32), BigUint::from(99u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(10u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let output = escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        // pk_Λ1 为 None 时，所有输出应为 None
        assert!(output.z1.is_none(), "Z_1 should be ⊥ when pk_Λ1 = ⊥");
        assert!(output.c_y1.is_none(), "C_y1 should be ⊥ when pk_Λ1 = ⊥");
        assert!(output.c_star_y1.is_none(), "C*_y1 should be ⊥ when pk_Λ1 = ⊥");
    }

    // ================================================================
    // 测试 3: C_y1 在有效范围内
    // ================================================================

    #[test]
    fn test_escrow1_cy1_in_valid_range() {
        let lambda = test_lambda();
        let n2 = &lambda.cpar.n2;

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let output = escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        let c_y1 = output.c_y1.unwrap();
        assert!(c_y1 > BigUint::from(0u32), "C_y1 must be non-zero");
        assert!(c_y1 < *n2, "C_y1 must be in range (0, n^2)");
    }

    // ================================================================
    // 测试 4: C_y1 与手动计算一致
    // ================================================================

    #[test]
    fn test_escrow1_cy1_matches_manual_computation() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;
        let n2 = &lambda.cpar.n2;

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let output = escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        // 手动计算：m_y = (3 + 7) mod n = 10
        // C_y1 = g^{10} * h^{41} mod n^2
        let m_y = (BigUint::from(3u32) + BigUint::from(7u32)) % n;
        let expected = (&lambda.cpar.g.modpow(&m_y, n2)
            * &lambda.cpar.h.modpow(&r_y1, n2))
            % n2;

        assert_eq!(output.c_y1.unwrap(), expected);
    }

    // ================================================================
    // 测试 5: 不同的 y 产生不同的承诺
    // ================================================================

    #[test]
    fn test_escrow1_different_y_different_commitments() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let y1 = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let y2 = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(11u32),
        };

        let out1 = escrow1(&lambda, &pk, &y1, &r_y1, &r_star_y1);
        let out2 = escrow1(&lambda, &pk, &y2, &r_y1, &r_star_y1);

        assert_ne!(
            out1.c_y1.unwrap(),
            out2.c_y1.unwrap(),
            "different y should yield different C_y1"
        );
    }

    // ================================================================
    // 测试 6: C*_y1 非零（椭圆曲线点不是无穷远点）
    // ================================================================

    #[test]
    fn test_escrow1_c_star_y1_not_identity() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, _sk), _c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_star_y1 = BigUint::from(53u32);

        let output = escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);

        let c_star = output.c_star_y1.unwrap();
        assert!(!c_star.is_zero(), "C*_y1 should not be the identity element");
    }
}