//! Algorithm 4: Key Update
//!
//! 输入：全局参数 Λ、旧名单 x、旧随机数 r_x、旧掩码 s、
//!       旧公私钥 (pk_Λ, sk_Λ)、旧承诺 C_x、
//!       新名单 x'、新随机数 r'_x、新掩码 s'。
//!
//! 输出：新公私钥 (pk'_Λ, sk'_Λ)，以及新承诺 C'_x。
//!
//! 核心逻辑：
//! - 当 Δ + α > t 时，完全重新生成（与 KeyGen 相同逻辑）；
//! - 当 Δ + α ≤ t 时，部分更新——复用旧的前半部分密钥和承诺，
//!   仅对 x' 的后 α 个元素重新生成密钥对和承诺。

use num_bigint::BigUint;

use rust::{keygen_ppb, HecFunctionKey};

use crate::commit::{self, PolyCommitment};
use crate::keygen::{PublicKey, SecretKey};
use crate::setup::Lambda;

/// Algorithm 4: KeyUpdate(Λ, x, r_x, s, pk_Λ, sk_Λ, C_x, x', r'_x, s')
///            -> (pk'_Λ, sk'_Λ), C'_x
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `x`：旧标量列表 (x_1, ..., x_ℓ)；
/// 3. `r_x`：旧随机数对 (r_x1, r_x2)；
/// 4. `s`：旧掩码对 (s1, s2)；
/// 5. `pk`：旧公钥 pk_Λ；
/// 6. `sk`：旧私钥 sk_Λ；
/// 7. `c_x`：旧承诺 C_x = (C_x1, C_x2)；
/// 8. `x_prime`：新标量列表 (x'_1, ..., x'_ℓ')；
/// 9. `r_x_prime`：新随机数对 (r'_x1, r'_x2)；
/// 10. `s_prime`：新掩码对 (s'_1, s'_2)。
///
/// 输出：(pk'_Λ, sk'_Λ), C'_x。
#[allow(clippy::too_many_arguments)]
pub fn key_update(
    lambda: &Lambda,
    x: &[BigUint],
    r_x: &[BigUint],
    s: &[BigUint],
    pk: &PublicKey,
    sk: &SecretKey,
    c_x: &[Option<PolyCommitment>],
    x_prime: &[BigUint],
    r_x_prime: &[BigUint],
    s_prime: &[BigUint],
) -> ((PublicKey, SecretKey), Vec<Option<PolyCommitment>>) {
    assert!(r_x.len() == 2, "r_x must have exactly 2 elements");
    assert!(s.len() == 2, "s must have exactly 2 elements");
    assert!(r_x_prime.len() == 2, "r'_x must have exactly 2 elements");
    assert!(s_prime.len() == 2, "s' must have exactly 2 elements");
    assert!(c_x.len() == 2, "C_x must have exactly 2 elements");

    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    let t = lambda.t;

    // Step 2: (r_x1, r_x2) = r_x; (s1, s2) = s
    // Step 3: (r'_x1, r'_x2) = r'_x; (s'_1, s'_2) = s'
    let r_x2 = &r_x[1];
    let s2 = &s[1];
    let r_x1_prime = &r_x_prime[0];
    let r_x2_prime = &r_x_prime[1];
    let s1_prime = &s_prime[0];
    let s2_prime = &s_prime[1];

    // Step 4: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // Step 5: (sk_Λ1, sk_Λ2, sk_SPS) = sk_Λ
    // （通过参数 pk, sk 直接访问）

    // Step 6: ℓ' = |x'|, ℓ = |x|, Δ = |x'| - |x|
    let l_prime = x_prime.len();
    let l = x.len();
    let delta = l_prime as isize - l as isize;

    // Step 7: α = ℓ mod t, α' = ℓ' mod t
    let mut alpha = l % t;
    let alpha_prime = l_prime % t;

    // Step 8-9: if ℓ > t and α = 0 then α = t
    if l > t && alpha == 0 {
        alpha = t;
    }

    // Step 10: 判断走完全重新生成还是部分更新
    if (delta as usize) + alpha > t {
        // ============================================================
        // Step 10-21: Δ + α > t —— 完全重新生成
        // ============================================================

        // Step 11-16: 确定分割点，将 x' 分为 x'_1 和 x'_2
        let split = if alpha_prime != 0 {
            // Step 11-13: α' ≠ 0
            l_prime - alpha_prime
        } else {
            // Step 14-16: α' = 0
            l_prime - t
        };
        let x1_prime = &x_prime[..split];
        let x2_prime = &x_prime[split..];

        // Step 17: (pk'_Λ1, sk'_Λ1) ← BLUE.KeyGen(Λ_BLUE, x'_1, r'_x1; s'_1)
        let fk1 = HecFunctionKey { n: x1_prime.len(), k: 1 };
        let (pk1_prime, sk1_prime) = keygen_ppb(&lambda.lambda_blue, &fk1, x1_prime, r_x1_prime, s1_prime)
            .expect("BLUE.KeyGen for x'_1 failed");

        // Step 18: (pk'_Λ2, sk'_Λ2) ← BLUE.KeyGen(Λ_BLUE, x'_2, r'_x2; s'_2)
        let fk2 = HecFunctionKey { n: x2_prime.len(), k: 1 };
        let (pk2_prime, sk2_prime) = keygen_ppb(&lambda.lambda_blue, &fk2, x2_prime, r_x2_prime, s2_prime)
            .expect("BLUE.KeyGen for x'_2 failed");

        // Step 19: pk'_SPS, sk'_SPS ← SPS.KGen(pp)
        let mut rng = ark_std::rand::rngs::OsRng;
        let (pk_sps_prime, sk_sps_prime) = lambda.pp.key_gen(&mut rng, l_prime as u32);

        // Step 20: C'_x1 = Commit(Λ, x'_1, r'_x1; s'_1)
        let cx1_prime = commit::commit(lambda, x1_prime, r_x1_prime, s1_prime);

        // Step 21: C'_x2 = Commit(Λ, x'_2, r'_x2; s'_2)
        let cx2_prime = commit::commit(lambda, x2_prime, r_x2_prime, s2_prime);

        // Step 30: C'_x = (C'_x1, C'_x2)
        let c_x_prime = vec![Some(cx1_prime), Some(cx2_prime)];

        // Step 31: pk'_Λ = (pk'_Λ1, pk'_Λ2, pk'_SPS)
        let new_pk = PublicKey {
            pk1: Some(pk1_prime),
            pk2: pk2_prime,
            pk_sps: Some(pk_sps_prime),
        };

        // Step 31: sk'_Λ = (sk'_Λ1, sk'_Λ2, sk'_SPS)
        let new_sk = SecretKey {
            sk1: Some(sk1_prime),
            sk2: sk2_prime,
            sk_sps: Some(sk_sps_prime),
        };

        // Step 32: return (pk'_Λ, sk'_Λ), C'_x
        ((new_pk, new_sk), c_x_prime)
    } else {
        // ============================================================
        // Step 22-29: Δ + α ≤ t —— 部分更新，复用旧的前半部分
        // ============================================================

        // Step 23: r'_x1 = r_x1; s'_1 = s1（保留旧值，仅用于语义说明）
        // Step 24: (pk'_Λ1, sk'_Λ1) = (pk_Λ1, sk_Λ1)
        // Step 25: (pk'_SPS, sk'_SPS) = (pk_SPS, sk_SPS)
        // （直接从旧密钥中 clone）

        // Step 26: x'_2 = (x'_{ℓ'-α+1}, ..., x'_{ℓ'})
        let x2_prime = &x_prime[l_prime - alpha..];

        // Step 27: (pk'_Λ2, sk'_Λ2) ← BLUE.KeyGen(Λ_BLUE, x'_2, r'_x2; s'_2)
        let fk2 = HecFunctionKey { n: x2_prime.len(), k: 1 };
        let (pk2_prime, sk2_prime) = keygen_ppb(&lambda.lambda_blue, &fk2, x2_prime, r_x2_prime, s2_prime)
            .expect("BLUE.KeyGen for x'_2 failed");

        // Step 28: C'_x1 = C_x1（复用旧承诺）
        let cx1_prime = c_x[0].clone();

        // Step 29: C'_x2 = Commit(Λ, x'_2, r'_x2; s'_2)
        let cx2_prime = commit::commit(lambda, x2_prime, r_x2_prime, s2_prime);

        // Step 30: C'_x = (C'_x1, C'_x2)
        let c_x_prime = vec![cx1_prime, Some(cx2_prime)];

        // Step 31: pk'_Λ = (pk'_Λ1, pk'_Λ2, pk'_SPS)
        let new_pk = PublicKey {
            pk1: pk.pk1.clone(),
            pk2: pk2_prime,
            pk_sps: pk.pk_sps.clone(),
        };

        // Step 31: sk'_Λ = (sk'_Λ1, sk'_Λ2, sk'_SPS)
        let new_sk = SecretKey {
            sk1: sk.sk1.clone(),
            sk2: sk2_prime,
            sk_sps: sk.sk_sps.clone(),
        };

        // Step 32: return (pk'_Λ, sk'_Λ), C'_x
        ((new_pk, new_sk), c_x_prime)
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
    // 测试 1: 完全重新生成（Δ + α > t）
    // ================================================================

    /// ℓ=1, t=3, α=1; ℓ'=5, α'=2; Δ=4, Δ+α=5 > 3 → 完全重新生成。
    #[test]
    fn test_full_regeneration() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(1u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // 完全重新生成：所有字段应存在
        assert!(pk_new.pk1.is_some(), "pk'1 should exist after full regen");
        assert!(pk_new.pk_sps.is_some(), "pk'_SPS should exist after full regen");
        assert!(sk_new.sk1.is_some(), "sk'1 should exist after full regen");
        assert!(sk_new.sk_sps.is_some(), "sk'_SPS should exist after full regen");
        assert!(c_x_new[0].is_some(), "C'_x1 should exist after full regen");
        assert!(c_x_new[1].is_some(), "C'_x2 should exist after full regen");
    }

    /// ℓ=4, t=3, α=1; ℓ'=8, α'=2; Δ=4, Δ+α=5 > 3 → 完全重新生成。
    #[test]
    fn test_full_regeneration_alpha_zero_case() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=8).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        assert!(pk_new.pk1.is_some());
        assert!(pk_new.pk_sps.is_some());
        assert!(sk_new.sk1.is_some());
        assert!(sk_new.sk_sps.is_some());
        assert!(c_x_new[0].is_some());
        assert!(c_x_new[1].is_some());

        // 验证分割：α'=2, split=8-2=6, x'_1 有 6 个元素, x'_2 有 2 个元素
        let cx1 = c_x_new[0].as_ref().unwrap();
        let cx2 = c_x_new[1].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 7, "x'_1 has 6 roots → 7 coefficients");
        assert_eq!(cx2.coeffs.len(), 3, "x'_2 has 2 roots → 3 coefficients");
    }

    // ================================================================
    // 测试 2: 部分更新（Δ + α ≤ t）
    // ================================================================

    /// ℓ=4, t=3, α=1; ℓ'=5, Δ=1, Δ+α=2 ≤ 3 → 部分更新。
    #[test]
    fn test_partial_update_reuses_first_half() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // ℓ'=5, Δ=1, α=1, Δ+α=2 ≤ 3
        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // 部分更新：前半部分应复用旧值
        assert!(pk_new.pk1.is_some(), "pk'1 should exist (reused from old)");
        assert!(pk_new.pk_sps.is_some(), "pk'_SPS should exist (reused from old)");
        assert!(sk_new.sk1.is_some(), "sk'1 should exist (reused from old)");
        assert!(sk_new.sk_sps.is_some(), "sk'_SPS should exist (reused from old)");
        assert!(c_x_new[0].is_some(), "C'_x1 should exist (reused from old)");
        assert!(c_x_new[1].is_some(), "C'_x2 should be regenerated");
    }

    /// 部分更新时，C'_x1 应与旧 C_x1 相同。
    #[test]
    fn test_partial_update_cx1_unchanged() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // C'_x1 应与旧 C_x1 完全相同
        let old_cx1 = c_x[0].as_ref().unwrap();
        let new_cx1 = c_x_new[0].as_ref().unwrap();
        assert_eq!(old_cx1.c, new_cx1.c, "C'_x1 should equal old C_x1");
        assert_eq!(old_cx1.coeffs, new_cx1.coeffs, "C'_x1 coeffs should equal old C_x1");
    }

    /// 部分更新时，C'_x2 应与旧 C_x2 不同（因为 x'_2 不同）。
    #[test]
    fn test_partial_update_cx2_changed() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        let old_cx2 = c_x[1].as_ref().unwrap();
        let new_cx2 = c_x_new[1].as_ref().unwrap();
        assert_ne!(old_cx2.c, new_cx2.c, "C'_x2 should differ from old C_x2");
    }

    // ================================================================
    // 测试 3: ℓ ≤ t 时的更新
    // ================================================================

    /// ℓ=1 ≤ t=3, α=1; ℓ'=2, Δ=1, Δ+α=2 ≤ 3 → 部分更新。
    /// 旧 pk1 = None，新 pk'1 也应为 None。
    #[test]
    fn test_small_list_partial_update() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime = vec![BigUint::from(42u32), BigUint::from(99u32)];
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // 旧 pk1 = None，部分更新复用 → 新 pk'1 也为 None
        assert!(pk_new.pk1.is_none(), "pk'1 should be None (reused None from old)");
        assert!(pk_new.pk_sps.is_none(), "pk'_SPS should be None (reused None from old)");
        assert!(sk_new.sk1.is_none(), "sk'1 should be None");
        assert!(sk_new.sk_sps.is_none(), "sk'_SPS should be None");
        assert!(c_x_new[0].is_none(), "C'_x1 should be None (reused None from old)");
        assert!(c_x_new[1].is_some(), "C'_x2 should be regenerated");
    }

    /// ℓ=1 ≤ t=3, α=1; ℓ'=5, Δ=4, Δ+α=5 > 3 → 完全重新生成。
    #[test]
    fn test_small_list_full_regeneration() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // 完全重新生成：所有字段应存在
        assert!(pk_new.pk1.is_some());
        assert!(pk_new.pk_sps.is_some());
        assert!(sk_new.sk1.is_some());
        assert!(sk_new.sk_sps.is_some());
        assert!(c_x_new[0].is_some());
        assert!(c_x_new[1].is_some());
    }

    // ================================================================
    // 测试 4: α = 0 时 α 被重置为 t 的情况
    // ================================================================

    /// ℓ=6, t=3, α=6%3=0 → α=t=3; ℓ'=7, Δ=1, Δ+α=4 > 3 → 完全重新生成。
    #[test]
    fn test_alpha_zero_reset_to_t() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=7).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // α 被重置为 t=3, Δ=1, Δ+α=4 > 3 → 完全重新生成
        assert!(pk_new.pk1.is_some());
        assert!(pk_new.pk_sps.is_some());
        assert!(c_x_new[0].is_some());
        assert!(c_x_new[1].is_some());
    }

    /// ℓ=6, t=3, α=0→t=3; ℓ'=7, Δ=1, Δ+α=4 > 3 → 完全重新生成。
    /// α'=7%3=1 ≠ 0, split=7-1=6。
    #[test]
    fn test_full_regen_split_correctness() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=7).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // α'=1, split=6, x'_1=[1,2,3,4,5,6], x'_2=[7]
        let cx1 = c_x_new[0].as_ref().unwrap();
        let cx2 = c_x_new[1].as_ref().unwrap();
        assert_eq!(cx1.coeffs.len(), 7, "x'_1 has 6 roots → 7 coefficients");
        assert_eq!(cx2.coeffs.len(), 2, "x'_2 has 1 root → 2 coefficients");

        // x'_2=[7], s'_2=1 → P = (x-7), coeffs = [n-7, 1]
        assert_eq!(cx2.coeffs[1], BigUint::from(1u32));
        assert_eq!(cx2.coeffs[0], n - BigUint::from(7u32));
    }

    // ================================================================
    // 测试 5: 承诺值在有效范围内
    // ================================================================

    #[test]
    fn test_commitments_in_valid_range() {
        let lambda = test_lambda();
        let n2 = &lambda.cpar.n2;

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        for (i, cx_opt) in c_x_new.iter().enumerate() {
            if let Some(cx) = cx_opt {
                assert!(cx.c > BigUint::zero(), "C'_x[{}] must be non-zero", i);
                assert!(cx.c < *n2, "C'_x[{}] must be in range (0, n^2)", i);
            }
        }
    }

    // ================================================================
    // 测试 6: 部分更新时 x'_2 系数正确性
    // ================================================================

    /// ℓ=4, t=3, α=1; ℓ'=5, Δ=1, Δ+α=2 ≤ 3 → 部分更新。
    /// x' = [1,2,3,4,5], x'_2 = last α=1 element = [5]。
    #[test]
    fn test_partial_update_x2_prime_coefficients() {
        let lambda = test_lambda();
        let n = &lambda.cpar.n;

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(1u32), BigUint::from(1u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // x'_2 = [5], s'_2 = 1 → P = (x-5), coeffs = [n-5, 1]
        let cx2 = c_x_new[1].as_ref().unwrap();
        assert_eq!(cx2.coeffs.len(), 2);
        assert_eq!(cx2.coeffs[1], BigUint::from(1u32));
        assert_eq!(cx2.coeffs[0], n - BigUint::from(5u32));
    }

    // ================================================================
    // 测试 7: 更新前后承诺值不同
    // ================================================================

    #[test]
    fn test_updated_commitment_differs_from_original() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        // C'_x2 应与旧 C_x2 不同
        let old_cx2 = c_x[1].as_ref().unwrap();
        let new_cx2 = c_x_new[1].as_ref().unwrap();
        assert_ne!(old_cx2.c, new_cx2.c, "C'_x2 should differ from old C_x2");
    }

    // ================================================================
    // 测试 8: C'_x 列表长度始终为 2
    // ================================================================

    #[test]
    fn test_cx_prime_always_two_elements() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(1u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 部分更新
        let x_prime = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];
        let (_, c_x_new) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );
        assert_eq!(c_x_new.len(), 2);

        // 完全重新生成
        let x_prime2: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let (_, c_x_new2) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime2, &r_x_prime, &s_prime,
        );
        assert_eq!(c_x_new2.len(), 2);
    }

    // ================================================================
    // 测试 9: SPS 密钥长度在完全重新生成时等于 ℓ'
    // ================================================================

    #[test]
    fn test_sps_key_length_after_full_regen() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(1u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, sk_new), _) = key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x,
            &x_prime, &r_x_prime, &s_prime,
        );

        let pk_sps = pk_new.pk_sps.as_ref().unwrap();
        let sk_sps = sk_new.sk_sps.as_ref().unwrap();
        assert_eq!(pk_sps.length(), 5, "pk'_SPS length should equal ℓ'");
        assert_eq!(sk_sps.length(), 5, "sk'_SPS length should equal ℓ'");
    }
}
