//! Algorithm 5: Public Key Verification
//!
//! 输入：全局参数 Λ、公钥 pk_Λ、承诺 C_x。
//! 输出：1（有效）或 0（无效）。
//!
//! 验证逻辑：
//! 1. 若 pk_Λ1 ≠ ⊥，则用 ppb 的 verify_pk 验证 pk_Λ1 与 C_x1 的一致性；
//! 2. 若 pk_Λ1 = ⊥ 或验证通过，再验证 pk_Λ2 与 C_x2 的一致性；
//! 3. 两步均通过返回 1，否则返回 0。

use rust::verify_pk;

use crate::commit::PolyCommitment;
use crate::keygen::PublicKey;
use crate::setup::Lambda;

/// Algorithm 5: VerPK(Λ, pk_Λ, C_x) -> {0, 1}
///
/// 输入：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：公钥 pk_Λ = (pk_Λ1, pk_Λ2, pk_SPS)；
/// 3. `c_x`：承诺 C_x = (C_x1, C_x2)。
///
/// 输出：1（有效）或 0（无效）。
pub fn ver_pk(lambda: &Lambda, pk: &PublicKey, c_x: &[Option<PolyCommitment>]) -> bool {
    assert!(c_x.len() == 2, "C_x must have exactly 2 elements");

    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    let params = &lambda.lambda_blue;

    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // Step 3: C_x1, C_x2 = C_x

    // Step 4: 若 pk_Λ1 ≠ ⊥，验证 BLUE.VerPK(Λ_BLUE, pk_Λ1, C_x1)
    if let Some(ref pk1) = pk.pk1 {
        let cx1 = c_x[0]
            .as_ref()
            .expect("C_x1 must exist when pk_Λ1 is not ⊥");
        if !verify_pk(params, pk1, &cx1.c) {
            return false;
        }
    }

    // Step 5: BLUE.VerPK(Λ_BLUE, pk_Λ2, C_x2)
    let cx2 = c_x[1].as_ref().expect("C_x2 must always exist");
    if !verify_pk(params, &pk.pk2, &cx2.c) {
        return false;
    }

    // Step 6: return 1
    true
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
        let cpar_star = rust::setup_pedersen(lambda_bits).expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: ℓ > t 时有效公钥应通过验证
    // ================================================================

    #[test]
    fn test_valid_pk_large_list() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, _sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        assert!(
            ver_pk(&lambda, &pk, &c_x),
            "valid pk should pass verification"
        );
    }

    // ================================================================
    // 测试 2: ℓ ≤ t 时有效公钥应通过验证
    // ================================================================

    #[test]
    fn test_valid_pk_small_list() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, _sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        assert!(
            ver_pk(&lambda, &pk, &c_x),
            "valid small-list pk should pass verification"
        );
    }

    // ================================================================
    // 测试 3: 篡改 C_x2 应导致验证失败
    // ================================================================

    #[test]
    fn test_tampered_cx2_fails() {
        let lambda = test_lambda();

        let x = vec![BigUint::from(42u32)];
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, _sk), mut c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 篡改 C_x2
        let cx2 = c_x[1].as_mut().unwrap();
        cx2.c = (&cx2.c + BigUint::from(1u32)) % &lambda.cpar.n2;

        assert!(
            !ver_pk(&lambda, &pk, &c_x),
            "tampered C_x2 should fail verification"
        );
    }

    // ================================================================
    // 测试 4: ℓ > t 时篡改 C_x1 应导致验证失败
    // ================================================================

    #[test]
    fn test_tampered_cx1_fails() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

        let ((pk, _sk), mut c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 篡改 C_x1
        let cx1 = c_x[0].as_mut().unwrap();
        cx1.c = (&cx1.c + BigUint::from(1u32)) % &lambda.cpar.n2;

        assert!(
            !ver_pk(&lambda, &pk, &c_x),
            "tampered C_x1 should fail verification"
        );
    }

    // ================================================================
    // 测试 5: KeyUpdate 后的公钥也应通过验证
    // ================================================================

    #[test]
    fn test_pk_after_key_update_passes() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // 部分更新
        let x_prime: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_new, _sk_new), c_x_new) = crate::keyupdate::key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x, &x_prime, &r_x_prime, &s_prime,
        );

        assert!(
            ver_pk(&lambda, &pk_new, &c_x_new),
            "pk after key update should pass verification"
        );
    }

    // ================================================================
    // 测试 6: 不同列表大小的公钥均应通过验证
    // ================================================================

    #[test]
    fn test_various_list_sizes_pass() {
        let lambda = test_lambda();

        for len in 1..=6 {
            let x: Vec<BigUint> = (1..=len).map(|i| BigUint::from(i as u32)).collect();
            let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
            let s = vec![BigUint::from(1u32), BigUint::from(2u32)];

            let ((pk, _sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

            assert!(
                ver_pk(&lambda, &pk, &c_x),
                "valid pk should pass for list size {}",
                len
            );
        }
    }
}
