//! Algorithm 1: Commit(Λ, x, r_x; s) -> C_x
//!
//! 对输入列表 x = (x_1, ..., x_{|x|}) 和随机掩码 s，
//! 计算多项式 P = s * ∏(x - x_i) 的系数展开，
//! 然后对系数向量 (a_0, a_1, ..., a_{|x|}) 计算承诺值 C_x。
//!
//! 承诺使用 DF/S1 兼容的确定性多基：
//!   C = H^{r_x} * Π_i G_i^{a_i} mod n^2。
//! 这些 G_i 由公共参数和下标派生，因此 VerPK 可以重算同一组基。

use num_bigint::BigUint;

use crate::setup::Lambda;

/// 多项式承诺结果。
///
/// 字段语义：
/// 1. `c`：承诺值 C_x（在 Z_{n^2} 中的群元素）；
/// 2. `coeffs`：多项式 P 的系数向量 (a_0, a_1, ..., a_{|x|})；
/// 3. `r_x`：承诺的开口随机数。
#[derive(Debug, Clone)]
pub struct PolyCommitment {
    pub c: BigUint,
    pub coeffs: Vec<BigUint>,
    pub r_x: BigUint,
}

/// Algorithm 1: Commit(Λ, x, r_x; s) -> C_x
///
/// 输入：
/// 1. `lambda`：全局参数 Λ（由 Setup 生成）；
/// 2. `x`：标量列表 x = (x_1, ..., x_{|x|})，对应算法中的名单/根；
/// 3. `r_x`：承诺的开口随机数；
/// 4. `s`：随机掩码标量，用于盲化多项式 P = s * ∏(x - x_i)。
///
/// 输出：多项式承诺 C_x。
///
/// 过程（对应算法步骤编号）：
///
/// Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
///   - 从全局参数中提取 DF 承诺所需的参数 cpar = (n, n^2, g, h)。
///
/// Step 2: P <- s * ∏_{i=1}^{|x|} (x - x_i) = a_0 + ∑ a_i * x_i
///   - 调用 expand_roots_to_coefficients_mod_n，以 x 为根、s 为掩码、
///     n 为模数，在 Z_n 上展开多项式并返回系数向量。
///
/// Step 3: C_x <- COM.Com(cpar, (a_0, ..., a_{|x|}); r_x)
///   - 使用确定性多基计算承诺：
///     C = H^{r_x} * Π_i G_i^{a_i} mod n^2。
///
/// Step 4: 返回承诺值 C_x。
pub fn commit(
    lambda: &Lambda,
    x: &[BigUint],
    r_x: &BigUint,
    s: &BigUint,
) -> PolyCommitment {
    let cpar = &lambda.cpar;

    let (commitment, coeffs) =
        rust::commit_df_multibase(cpar, x, r_x, s).expect("commit_df_multibase failed");

    PolyCommitment {
        c: commitment.c,
        coeffs,
        r_x: commitment.r,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::Zero;

    /// 构造测试用的 Lambda（使用固定安全参数）。
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits)
            .expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: 多项式系数的数学正确性
    // ================================================================

    /// 验证 expand_roots_to_coefficients_mod_n 对简单根列表的展开结果。
    /// P = s * (x - 2)(x - 3) = s * (x^2 - 5x + 6)
    /// 当 s=1 时，系数应为 [6, -5, 1]（mod n）。
    #[test]
    fn test_polynomial_coefficients_two_roots() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x = vec![BigUint::from(2u32), BigUint::from(3u32)];
        let s = BigUint::from(1u32);
        let r_x = BigUint::from(0u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        // 系数数量 = |x| + 1 = 3
        assert_eq!(pc.coeffs.len(), 3, "coeffs length should be |x|+1");

        // a_2 (最高次项) = s * 1 = 1
        assert_eq!(pc.coeffs[2], BigUint::from(1u32));

        // a_1 = s * (-5) mod n = n - 5
        let expected_a1 = n - BigUint::from(5u32);
        assert_eq!(pc.coeffs[1], expected_a1);

        // a_0 = s * 6 = 6
        assert_eq!(pc.coeffs[0], BigUint::from(6u32));
    }

    /// 验证 P = 7 * (x - 5)(x - 11)(x - 13) 的系数展开。
    /// 展开后：7x^3 - 203x^2 + 1841x - 5005。
    #[test]
    fn test_polynomial_coefficients_three_roots_with_scalar() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let s = BigUint::from(7u32);
        let r_x = BigUint::from(0u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        assert_eq!(pc.coeffs.len(), 4, "coeffs length should be |x|+1 = 4");

        // a_3 = s = 7
        assert_eq!(pc.coeffs[3], BigUint::from(7u32));

        // a_1 = 1841（正数，不会 wrap）
        assert_eq!(pc.coeffs[1], BigUint::from(1841u32));

        // a_0 = -5005 mod n = n - 5005
        let expected_a0 = n - BigUint::from(5005u32);
        assert_eq!(pc.coeffs[0], expected_a0);

        // a_2 = -203 mod n = n - 203
        let expected_a2 = n - BigUint::from(203u32);
        assert_eq!(pc.coeffs[2], expected_a2);
    }

    // ================================================================
    // 测试 2: 单根情况
    // ================================================================

    /// P = s * (x - 42) = s*x - 42*s
    #[test]
    fn test_single_root() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x = vec![BigUint::from(42u32)];
        let s = BigUint::from(3u32);
        let r_x = BigUint::from(10u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        assert_eq!(pc.coeffs.len(), 2);

        // a_1 = s = 3
        assert_eq!(pc.coeffs[1], BigUint::from(3u32));

        // a_0 = -42 * 3 = -126 mod n = n - 126
        let expected_a0 = n - BigUint::from(126u32);
        assert_eq!(pc.coeffs[0], expected_a0);
    }

    // ================================================================
    // 测试 3: s=1 时系数与 ∏(x-x_i) 一致
    // ================================================================

    #[test]
    fn test_s_equals_one_identity() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x = vec![BigUint::from(1u32), BigUint::from(2u32), BigUint::from(3u32)];
        let s = BigUint::from(1u32);
        let r_x = BigUint::from(0u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        // (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
        assert_eq!(pc.coeffs[3], BigUint::from(1u32));
        assert_eq!(pc.coeffs[1], BigUint::from(11u32));
        assert_eq!(pc.coeffs[0], n - BigUint::from(6u32));
        let expected_a2 = n - BigUint::from(6u32);
        assert_eq!(pc.coeffs[2], expected_a2);
    }

    // ================================================================
    // 测试 4: 承诺值结构正确性
    // ================================================================

    /// 承诺值 C_x 必须在 (0, n^2) 范围内。
    #[test]
    fn test_commitment_in_valid_range() {
        let lambda = test_lambda();
        let n2 = &lambda.cpar.n2;

        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let r_x = BigUint::from(37u32);
        let s = BigUint::from(7u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        assert!(pc.c > BigUint::zero(), "commitment must be non-zero");
        assert!(pc.c < *n2, "commitment must be in range (0, n^2)");
    }

    /// 不同的 x 产生不同的承诺值。
    #[test]
    fn test_different_roots_different_commitments() {
        let lambda = test_lambda();

        let r_x = BigUint::from(37u32);
        let s = BigUint::from(1u32);

        let pc1 = commit(&lambda, &[BigUint::from(5u32)], &r_x, &s);
        let pc2 = commit(&lambda, &[BigUint::from(6u32)], &r_x, &s);

        assert_ne!(pc1.c, pc2.c, "different roots should yield different commitments");
    }

    /// 不同的 r_x 产生不同的承诺值（h^{r_x} 分量不同）。
    #[test]
    fn test_different_openings_different_commitments() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let s = BigUint::from(1u32);

        let pc1 = commit(&lambda, &x, &BigUint::from(10u32), &s);
        let pc2 = commit(&lambda, &x, &BigUint::from(20u32), &s);

        assert_ne!(pc1.c, pc2.c, "different r_x should yield different commitments");
    }

    // ================================================================
    // 测试 5: 多基向量承诺公式
    // ================================================================

    /// final 层的 Commit 应直接匹配 ppb 基础库中的多基承诺。
    #[test]
    fn test_commitment_matches_core_multibase() {
        let lambda = test_lambda();
        let cpar = &lambda.cpar;

        let x = vec![BigUint::from(2u32), BigUint::from(3u32)];
        let s = BigUint::from(1u32);
        let r_x = BigUint::from(7u32);

        let pc = commit(&lambda, &x, &r_x, &s);
        let (expected, expected_coeffs) =
            rust::commit_df_multibase(cpar, &x, &r_x, &s).expect("multibase commit should succeed");

        assert_eq!(pc.coeffs, expected_coeffs);
        assert_eq!(pc.c, expected.c, "commitment should match core multibase computation");
    }

    /// 旧的 g^{sum(a_i)} 方案会让这两个不同系数向量在相同 r 下碰撞。
    #[test]
    fn test_same_coefficient_sum_does_not_collide() {
        let lambda = test_lambda();
        let s = BigUint::from(1u32);
        let r_x = BigUint::from(9u32);

        let pc1 = commit(&lambda, &[BigUint::from(2u32)], &r_x, &s);
        let pc2 = commit(
            &lambda,
            &[BigUint::from(0u32), BigUint::from(2u32)],
            &r_x,
            &s,
        );

        let sum1: BigUint = pc1.coeffs.iter().fold(BigUint::from(0u32), |acc, a| acc + a);
        let sum2: BigUint = pc2.coeffs.iter().fold(BigUint::from(0u32), |acc, a| acc + a);

        assert_eq!(sum1, sum2, "test inputs should collide under the old sum-based formula");
        assert_ne!(pc1.coeffs, pc2.coeffs);
        assert_ne!(pc1.c, pc2.c, "multibase commitment must bind coefficient positions");
    }

    // ================================================================
    // 测试 6: r_x 存储正确性
    // ================================================================

    #[test]
    fn test_stored_rx_matches_input() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(7u32)];
        let r_x = BigUint::from(12345u32);
        let s = BigUint::from(1u32);

        let pc = commit(&lambda, &x, &r_x, &s);

        assert_eq!(pc.r_x, r_x, "stored r_x should match input");
    }

    // ================================================================
    // 测试 7: 系数数量 = |x| + 1
    // ================================================================

    #[test]
    fn test_coefficient_count_matches_roots_plus_one() {
        let lambda = test_lambda();

        for len in 1..=5 {
            let x: Vec<BigUint> = (1..=len).map(|i| BigUint::from(i as u32)).collect();
            let s = BigUint::from(1u32);
            let r_x = BigUint::from(0u32);

            let pc = commit(&lambda, &x, &r_x, &s);
            assert_eq!(
                pc.coeffs.len(),
                len + 1,
                "for |x|={}, coeffs length should be {}",
                len,
                len + 1
            );
        }
    }

    // ================================================================
    // 测试 8: 最高次项系数恒等于 s
    // ================================================================

    /// ∏(x - x_i) 的最高次项系数恒为 1，乘以 s 后为 s。
    #[test]
    fn test_leading_coefficient_equals_s() {
        let lambda = test_lambda();

        for s_val in [1u32, 5u32, 100u32, 999u32] {
            let s = BigUint::from(s_val);
            let x = vec![BigUint::from(10u32), BigUint::from(20u32), BigUint::from(30u32)];
            let r_x = BigUint::from(0u32);

            let pc = commit(&lambda, &x, &r_x, &s);
            assert_eq!(
                *pc.coeffs.last().unwrap(),
                s,
                "leading coefficient should equal s={}",
                s_val
            );
        }
    }
}
