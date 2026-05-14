//! Algorithm 3: Key Generation
//!
//! 输入：全局参数 Λ、标量列表 x = (x_1, ..., x_ℓ)、
//!       随机数 r_x = (r_x1, r_x2)、掩码 s = (s1, s2)。
//!
//! 输出：公私钥对 (pk_Λ, sk_Λ)，以及承诺 C_x = (C_x1, C_x2)。
//!
//! 当 ℓ > t 时，将 x 分为两部分，分别生成 ppb 密钥对和承诺，
//! 并生成一对 Mercurial Signature 密钥对；
//! 当 0 < ℓ ≤ t 时，前半部分全部置为 ⊥，仅生成后半部分的密钥对和承诺。

use num_bigint::BigUint;

use rust::{keygen_ppb, HecFunctionKey};
use mercurial_signature::PublicKey as MsPublicKey;
use mercurial_signature::SecretKey as MsSecretKey;

use crate::commit::{self, PolyCommitment};
use crate::setup::Lambda;

/// 公钥 pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)。
///
/// 当 ℓ ≤ t 时，`pk1` 和 `pk_sps` 为 `None`。
#[derive(Clone)]
pub struct PublicKey {
    /// 前半部分的 ppb 公钥（ℓ ≤ t 时为 None）。
    pub pk1: Option<rust::PpbPublicKey>,
    /// 后半部分的 ppb 公钥。
    pub pk2: rust::PpbPublicKey,
    /// Mercurial Signature 公钥（ℓ ≤ t 时为 None）。
    pub pk_sps: Option<MsPublicKey>,
}

/// 私钥 sk_Λ = (sk_Λ1, sk_Λ2, sk_SPS)。
///
/// 当 ℓ ≤ t 时，`sk1` 和 `sk_sps` 为 `None`。
#[derive(Clone)]
pub struct SecretKey {
    /// 前半部分的 ppb 私钥（ℓ ≤ t 时为 None）。
    pub sk1: Option<rust::PpbSecretKey>,
    /// 后半部分的 ppb 私钥。
    pub sk2: rust::PpbSecretKey,
    /// Mercurial Signature 私钥（ℓ ≤ t 时为 None）。
    pub sk_sps: Option<MsSecretKey>,
}

/// Algorithm 3: KeyGen(Λ, x, r_x, s) -> (pk_Λ, sk_Λ), C_x
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `x`：标量列表 (x_1, ..., x_ℓ)；
/// 3. `r_x`：随机数对 (r_x1, r_x2)，长度必须为 2；
/// 4. `s`：掩码对 (s1, s2)，长度必须为 2。
///
/// 输出：(pk_Λ, sk_Λ), C_x。
pub fn keygen(
    lambda: &Lambda,
    x: &[BigUint],
    r_x: &[BigUint],
    s: &[BigUint],
) -> ((PublicKey, SecretKey), Vec<Option<PolyCommitment>>) {
    assert!(r_x.len() == 2, "r_x must have exactly 2 elements");
    assert!(s.len() == 2, "s must have exactly 2 elements");

    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    let t = lambda.t;

    // Step 2: (r_x1, r_x2) = r_x; (s1, s2) = s
    let r_x1 = &r_x[0];
    let r_x2 = &r_x[1];
    let s1 = &s[0];
    let s2 = &s[1];

    // Step 3: ℓ = |x|, α = ℓ mod t
    let l = x.len();
    let alpha = l % t;

    if l > t {
        // ============================================================
        // Step 4-10: ℓ > t 的情况 —— 将 x 分为两部分
        // ============================================================

        // Step 5-10: 确定分割点，将 x 分为 x1 和 x2
        let split = if alpha != 0 {
            // Step 5-7: α ≠ 0 时，x1 = (x_1,...,x_{ℓ-α}), x2 = (x_{ℓ-α+1},...,x_ℓ)
            l - alpha
        } else {
            // Step 8-10: α = 0 时，x1 = (x_1,...,x_{ℓ-t}), x2 = (x_{ℓ-t+1},...,x_ℓ)
            l - t
        };
        let x1 = &x[..split];
        let x2 = &x[split..];

        // ============================================================
        // Step 11: (pk_Λ1, sk_Λ1) ← BLUE.KeyGen(Λ_BLUE, x1, r_x1; s1)
        // ============================================================
        let fk1 = HecFunctionKey { n: x1.len(), k: 1 };
        let (pk1, sk1) = keygen_ppb(&lambda.lambda_blue, &fk1, x1, r_x1)
            .expect("BLUE.KeyGen for x1 failed");

        // ============================================================
        // Step 12: (pk_Λ2, sk_Λ2) ← BLUE.KeyGen(Λ_BLUE, x2, r_x2; s2)
        // ============================================================
        let fk2 = HecFunctionKey { n: x2.len(), k: 1 };
        let (pk2, sk2) = keygen_ppb(&lambda.lambda_blue, &fk2, x2, r_x2)
            .expect("BLUE.KeyGen for x2 failed");

        // ============================================================
        // Step 13: pk_SPS, sk_SPS ← SPS.KGen(pp)
        // ============================================================
        let mut rng = ark_std::rand::rngs::OsRng;
        let (pk_sps, sk_sps) = lambda.pp.key_gen(&mut rng, l as u32);

        // ============================================================
        // Step 14: C_x1 = Commit(Λ, x1, r_x1; s1)
        // ============================================================
        let cx1 = commit::commit(lambda, x1, r_x1, s1);

        // ============================================================
        // Step 15: C_x2 = Commit(Λ, x2, r_x2; s2)
        // ============================================================
        let cx2 = commit::commit(lambda, x2, r_x2, s2);

        // Step 22: C_x = (C_x1, C_x2)
        let c_x = vec![Some(cx1), Some(cx2)];

        // Step 23: pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)
        let pk = PublicKey {
            pk1: Some(pk1),
            pk2,
            pk_sps: Some(pk_sps),
        };

        // Step 24: sk_Λ = (sk_Λ1, sk_Λ2, sk_SPS)
        let sk = SecretKey {
            sk1: Some(sk1),
            sk2,
            sk_sps: Some(sk_sps),
        };

        // Step 25: return (pk_Λ, sk_Λ), C_x
        ((pk, sk), c_x)
    } else {
        // ============================================================
        // Step 16-21: 0 < ℓ ≤ t 的情况 —— 前半部分置为 ⊥
        // ============================================================

        // Step 17: (pk_Λ1, sk_Λ1) = ⊥, ⊥
        // Step 18: pk_SPS, sk_SPS = ⊥, ⊥
        // Step 19: C_x1 = ⊥
        // （通过 Option::None 表示 ⊥）

        // ============================================================
        // Step 20: (pk_Λ2, sk_Λ2) ← BLUE.KeyGen(Λ_BLUE, x, r_x2; s2)
        // ============================================================
        let fk2 = HecFunctionKey { n: l, k: 1 };
        let (pk2, sk2) = keygen_ppb(&lambda.lambda_blue, &fk2, x, r_x2)
            .expect("BLUE.KeyGen for x failed");

        // ============================================================
        // Step 21: C_x2 = Commit(Λ, x, r_x2; s2)
        //   注意：算法中写的是 x2，但此处 x2 = x（整个列表），
        //   因为当 ℓ ≤ t 时不分割列表。
        // ============================================================
        let cx2 = commit::commit(lambda, x, r_x2, s2);

        // Step 22: C_x = (C_x1, C_x2) = (⊥, C_x2)
        let c_x = vec![None, Some(cx2)];

        // Step 23: pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)
        let pk = PublicKey {
            pk1: None,
            pk2,
            pk_sps: None,
        };

        // Step 24: sk_Λ = (sk_Λ1, sk_Λ2, sk_SPS)
        let sk = SecretKey {
            sk1: None,
            sk2,
            sk_sps: None,
        };

        // Step 25: return (pk_Λ, sk_Λ), C_x
        ((pk, sk), c_x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::Zero;

    /// 构造测试用的 Lambda。
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits)
            .expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: ℓ ≤ t 的情况 —— 前半部分全部为 ⊥
    // ================================================================

    /// 当 |x| = 1 ≤ t = 3 时，pk1, sk1, pk_sps, sk_sps 均为 None，C_x1 为 None。
    #[test]
    fn test_small_list_all_none_for_first_half() {
        let lambda = test_lambda();
        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        // 前半部分应全部为 ⊥ (None)
        assert!(pk.pk1.is_none(), "pk1 should be None when ℓ ≤ t");
        assert!(sk.sk1.is_none(), "sk1 should be None when ℓ ≤ t");
        assert!(pk.pk_sps.is_none(), "pk_sps should be None when ℓ ≤ t");
        assert!(sk.sk_sps.is_none(), "sk_sps should be None when ℓ ≤ t");
        assert!(c_x[0].is_none(), "C_x1 should be None when ℓ ≤ t");

        // 后半部分应存在
        assert!(c_x[1].is_some(), "C_x2 should exist");
    }

    /// 当 |x| = t = 3 时，仍属于 ℓ ≤ t 的情况。
    #[test]
    fn test_list_equal_to_t_uses_small_branch() {
        let lambda = test_lambda();
        let x = vec![BigUint::from(1u32), BigUint::from(2u32), BigUint::from(3u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        assert!(pk.pk1.is_none(), "pk1 should be None when ℓ = t");
        assert!(sk.sk1.is_none(), "sk1 should be None when ℓ = t");
        assert!(pk.pk_sps.is_none(), "pk_sps should be None when ℓ = t");
        assert!(sk.sk_sps.is_none(), "sk_sps should be None when ℓ = t");
        assert!(c_x[0].is_none(), "C_x1 should be None when ℓ = t");
        assert!(c_x[1].is_some(), "C_x2 should exist");
    }

    // ================================================================
    // 测试 2: ℓ > t 且 α ≠ 0 的情况
    // ================================================================

    /// |x| = 4, t = 3, α = 4%3 = 1 ≠ 0。
    /// split = ℓ - α = 3，x1 = (x1,x2,x3), x2 = (x4)。
    #[test]
    fn test_large_list_alpha_nonzero() {
        let lambda = test_lambda();
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
            BigUint::from(17u32),
        ];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        // 所有字段应存在
        assert!(pk.pk1.is_some(), "pk1 should exist when ℓ > t");
        assert!(sk.sk1.is_some(), "sk1 should exist when ℓ > t");
        assert!(pk.pk_sps.is_some(), "pk_sps should exist when ℓ > t");
        assert!(sk.sk_sps.is_some(), "sk_sps should exist when ℓ > t");
        assert!(c_x[0].is_some(), "C_x1 should exist when ℓ > t");
        assert!(c_x[1].is_some(), "C_x2 should exist when ℓ > t");

        // 验证分割：x1 有 3 个元素，x2 有 1 个元素
        let cx1 = c_x[0].as_ref().unwrap();
        let cx2 = c_x[1].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 4, "x1 has 3 roots → 4 coefficients");
        assert_eq!(cx2.coeffs.len(), 2, "x2 has 1 root → 2 coefficients");
    }

    // ================================================================
    // 测试 3: ℓ > t 且 α = 0 的情况
    // ================================================================

    /// |x| = 6, t = 3, α = 6%3 = 0。
    /// split = ℓ - t = 3，x1 = (x1,x2,x3), x2 = (x4,x5,x6)。
    #[test]
    fn test_large_list_alpha_zero() {
        let lambda = test_lambda();
        let x: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        assert!(pk.pk1.is_some(), "pk1 should exist when ℓ > t");
        assert!(sk.sk1.is_some(), "sk1 should exist when ℓ > t");
        assert!(pk.pk_sps.is_some(), "pk_sps should exist when ℓ > t");
        assert!(sk.sk_sps.is_some(), "sk_sps should exist when ℓ > t");
        assert!(c_x[0].is_some(), "C_x1 should exist when ℓ > t");
        assert!(c_x[1].is_some(), "C_x2 should exist when ℓ > t");

        // 验证分割：x1 有 3 个元素，x2 有 3 个元素
        let cx1 = c_x[0].as_ref().unwrap();
        let cx2 = c_x[1].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 4, "x1 has 3 roots → 4 coefficients");
        assert_eq!(cx2.coeffs.len(), 4, "x2 has 3 roots → 4 coefficients");
    }

    // ================================================================
    // 测试 4: C_x 的承诺值在有效范围内
    // ================================================================

    #[test]
    fn test_commitments_in_valid_range() {
        let lambda = test_lambda();
        let n2 = &lambda.cpar.n2;

        let x: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((_pk, _sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        for (i, cx_opt) in c_x.iter().enumerate() {
            if let Some(cx) = cx_opt {
                assert!(cx.c > BigUint::zero(), "C_x[{}] must be non-zero", i);
                assert!(cx.c < *n2, "C_x[{}] must be in range (0, n^2)", i);
            }
        }
    }

    // ================================================================
    // 测试 5: 承诺的多项式系数正确性
    // ================================================================

    /// ℓ ≤ t 时，C_x2 应基于整个 x 列表计算。
    #[test]
    fn test_small_list_commitment_uses_full_x() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x = vec![BigUint::from(2u32), BigUint::from(3u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s_val = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let ((_pk, _sk), c_x) = keygen(&lambda, &x, &r_x, &s_val);

        let cx2 = c_x[1].as_ref().unwrap();

        // x = [2,3], s2 = 1 → P = (x-2)(x-3) = x^2 - 5x + 6
        assert_eq!(cx2.coeffs.len(), 3);
        assert_eq!(cx2.coeffs[0], BigUint::from(6u32));
        assert_eq!(cx2.coeffs[1], n - BigUint::from(5u32));
        assert_eq!(cx2.coeffs[2], BigUint::from(1u32));
    }

    /// ℓ > t 时，C_x1 和 C_x2 应分别基于 x1 和 x2 计算。
    #[test]
    fn test_large_list_commitments_match_split() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        // |x| = 4, t = 3, α = 1, split = 3
        // x1 = [2,3,5], x2 = [7]
        let x = vec![
            BigUint::from(2u32),
            BigUint::from(3u32),
            BigUint::from(5u32),
            BigUint::from(7u32),
        ];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s_val = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let ((_pk, _sk), c_x) = keygen(&lambda, &x, &r_x, &s_val);

        // C_x1: (x-2)(x-3)(x-5) = x^3 - 10x^2 + 31x - 30
        let cx1 = c_x[0].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 4);
        assert_eq!(cx1.coeffs[3], BigUint::from(1u32));
        assert_eq!(cx1.coeffs[2], n - BigUint::from(10u32));
        assert_eq!(cx1.coeffs[1], BigUint::from(31u32));
        assert_eq!(cx1.coeffs[0], n - BigUint::from(30u32));

        // C_x2: (x-7) = x - 7
        let cx2 = c_x[1].as_ref().unwrap();
        assert_eq!(cx2.coeffs.len(), 2);
        assert_eq!(cx2.coeffs[1], BigUint::from(1u32));
        assert_eq!(cx2.coeffs[0], n - BigUint::from(7u32));
    }

    // ================================================================
    // 测试 6: Mercurial Signature 密钥对长度正确
    // ================================================================

    #[test]
    fn test_sps_key_length_matches_list_size() {
        let lambda = test_lambda();

        // ℓ > t → SPS 密钥应存在
        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), _) = keygen(&lambda, &x, &r_x, &s);

        let pk_sps = pk.pk_sps.as_ref().unwrap();
        let sk_sps = sk.sk_sps.as_ref().unwrap();
        assert_eq!(pk_sps.length(), 5, "pk_SPS length should equal ℓ");
        assert_eq!(sk_sps.length(), 5, "sk_SPS length should equal ℓ");

        // ℓ ≤ t → SPS 密钥应为 None
        let x_small = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk2, sk2), _) = keygen(&lambda, &x_small, &r_x, &s);
        assert!(pk2.pk_sps.is_none());
        assert!(sk2.sk_sps.is_none());
    }

    // ================================================================
    // 测试 7: 不同的 x 产生不同的承诺
    // ================================================================

    #[test]
    fn test_different_x_different_commitments() {
        let lambda = test_lambda();

        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let x1 = vec![BigUint::from(2u32)];
        let x2 = vec![BigUint::from(3u32)];

        let (_, c_a) = keygen(&lambda, &x1, &r_x, &s);
        let (_, c_b) = keygen(&lambda, &x2, &r_x, &s);

        let ca = c_a[1].as_ref().unwrap();
        let cb = c_b[1].as_ref().unwrap();
        assert_ne!(ca.c, cb.c, "different x should yield different commitments");
    }

    // ================================================================
    // 测试 8: r_x 的随机性影响承诺值
    // ================================================================

    #[test]
    fn test_different_rx_different_commitments() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(5u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let r_x_a = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let r_x_b = vec![BigUint::from(10u32), BigUint::from(30u32)];

        let (_, c_a) = keygen(&lambda, &x, &r_x_a, &s);
        let (_, c_b) = keygen(&lambda, &x, &r_x_b, &s);

        let ca = c_a[1].as_ref().unwrap();
        let cb = c_b[1].as_ref().unwrap();
        assert_ne!(ca.c, cb.c, "different r_x2 should yield different C_x2");
    }

    // ================================================================
    // 测试 9: ℓ > t 大列表 (ℓ = 8, t = 3, α = 2)
    // ================================================================

    /// |x| = 8, t = 3, α = 8%3 = 2 ≠ 0。
    /// split = ℓ - α = 6，x1 有 6 个元素，x2 有 2 个元素。
    #[test]
    fn test_large_list_eight_elements() {
        let lambda = test_lambda();
        let x: Vec<BigUint> = (1..=8).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(100u32), BigUint::from(200u32)];
        let s = vec![BigUint::from(3u32), BigUint::from(5u32)];

        let ((pk, sk), c_x) = keygen(&lambda, &x, &r_x, &s);

        assert!(pk.pk1.is_some());
        assert!(pk.pk_sps.is_some());
        assert!(sk.sk1.is_some());
        assert!(sk.sk_sps.is_some());

        let cx1 = c_x[0].as_ref().unwrap();
        let cx2 = c_x[1].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 7, "x1 has 6 roots → 7 coefficients");
        assert_eq!(cx2.coeffs.len(), 3, "x2 has 2 roots → 3 coefficients");

        // 最高次项系数应分别等于 s1 和 s2
        assert_eq!(*cx1.coeffs.last().unwrap(), BigUint::from(3u32));
        assert_eq!(*cx2.coeffs.last().unwrap(), BigUint::from(5u32));
    }

    // ================================================================
    // 测试 10: C_x 列表长度始终为 2
    // ================================================================

    #[test]
    fn test_cx_always_has_two_elements() {
        let lambda = test_lambda();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        // ℓ ≤ t
        let x_small = vec![BigUint::from(1u32)];
        let (_, c_x) = keygen(&lambda, &x_small, &r_x, &s);
        assert_eq!(c_x.len(), 2, "C_x should always have 2 elements");

        // ℓ > t
        let x_large: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let (_, c_x) = keygen(&lambda, &x_large, &r_x, &s);
        assert_eq!(c_x.len(), 2, "C_x should always have 2 elements");
    }
}
