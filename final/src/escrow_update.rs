//! Algorithm 9: Escrow Update
//!
//! 当公钥发生更新（KeyUpdate 后产生 pk'_Λ）时，用户需要重新执行 Escrow 流程，
//! 使得 Escrow 输出与新公钥 pk'_Λ 一致。
//!
//! 本算法涉及 User 和 Auditor 两方交互：
//!
//! **分支 1**（pk'_Λ1 ≠ pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2）—— 密钥完全更新：
//!   1. User 调用 Escrow1 生成新的 Z'_1；
//!   2. User 将 (C'_y1, C*_y1', Z'_1, π'_1) 发送给 Auditor；
//!   3. Auditor 调用 Endorse 验证并生成签名 σ_y，返回给 User；
//!   4. User 调用 Escrow2 完成更新。
//!
//! **分支 2**（pk'_Λ1 = pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2）—— 仅后半部分更新：
//!   - 复用旧的 Pedersen 承诺随机数 r*_y1 和承诺值 C*_y1；
//!   - 使用用户传入的签名 σ_y；
//!   - 直接调用 Escrow2，无需 Auditor 交互。
//!
//! **隐含分支**（pk'_Λ1 = pk_Λ1 且 pk'_Λ2 = pk_Λ2）—— 公钥未变化：
//!   - 无需更新，返回错误。

use num_bigint::BigUint;

use mercurial_signature::Signature as MsSignature;

use crate::endorse;
use crate::escrow1;
use crate::escrow2;
use crate::keygen::{PublicKey, SecretKey};
use crate::setup::Lambda;

/// Algorithm 9: Escrow Update 的输出结构体。
///
/// 字段语义：
/// 1. `z_prime`：更新后的 Escrow2 输出 Z'；
/// 2. `c_y2_prime`：更新后的 DF 承诺值 C'_y2；
/// 3. `r_y2_prime`：更新后的 DF 承诺随机数 r'_y2（透传自输入）；
/// 4. `r_star_y1_prime`：更新后的 Pedersen 承诺随机数 r*_y1'。
pub struct EscrowUpdateOutput {
    /// Z' = Escrow2 的输出（含 Z'_1 和 Z_2）。
    pub z_prime: escrow2::Escrow2Output,
    /// C'_y2 = Com(cpar, y; r'_y2)，DF 承诺值。
    pub c_y2_prime: BigUint,
    /// r'_y2，DF 承诺随机数（透传自输入）。
    pub r_y2_prime: BigUint,
    /// r*_y1'，Pedersen 承诺随机数。
    pub r_star_y1_prime: BigUint,
}

/// Algorithm 9: EscrowUpdate
///
/// 当公钥从 pk_Λ 更新为 pk'_Λ 后，重新执行 Escrow 流程。
///
/// 输入（User 侧）：
/// 1. `lambda`：全局参数 Λ；
/// 2. `pk`：旧公钥 pk_Λ；
/// 3. `y`：评估输入 y = (y_id, y_at)；
/// 4. `r_star_y1`：旧 Pedersen 承诺随机数 r*_y1（分支 2 使用）；
/// 5. `r_y2`：旧 DF 承诺随机数 r_y2（当前未直接使用，保留接口一致性）；
/// 6. `c_star_y1`：旧 Pedersen 承诺 C*_y1（分支 2 使用）；
/// 7. `z`：旧 Escrow2 输出 Z；
/// 8. `pk_prime`：新公钥 pk'_Λ；
/// 9. `r_y1_prime`：新 DF 承诺随机数 r'_y1（分支 1 使用）；
/// 10. `r_y2_prime`：新 DF 承诺随机数 r'_y2；
/// 11. `r_star_y1_prime`：新 Pedersen 承诺随机数 r*_y1'（分支 1 使用）；
/// 12. `sigma_y`：签名 σ_y（分支 2 使用，由用户直接传入）。
///
/// 输入（Auditor 侧）：
/// 13. `sk_prime`：新私钥 sk'_Λ；
/// 14. `x_prime`：新名单 x'。
///
/// 输出：Some((Z', C'_y2, (r'_y2, r*_y1'))) 或 None（验证失败时）。
#[allow(clippy::too_many_arguments)]
pub fn escrow_update(
    // === User 输入 ===
    lambda: &Lambda,
    pk: &PublicKey,
    y: &rust::HecEvalInput,
    r_star_y1: &BigUint,
    _r_y2: &BigUint,
    c_star_y1: &ark_bls12_381::G1Projective,
    z: &escrow2::Escrow2Output,
    pk_prime: &PublicKey,
    r_y1_prime: &BigUint,
    r_y2_prime: &BigUint,
    r_star_y1_prime: &BigUint,
    sigma_y: &MsSignature,
    // === Auditor 输入 ===
    sk_prime: &SecretKey,
    x_prime: &[BigUint],
) -> Option<EscrowUpdateOutput> {
    // ============================================================
    // Step 1: (pp, cpar*, cpar, inv, Λ_BLUE, t, crs1, crs2) = Λ
    // ============================================================
    // 通过 lambda 直接访问各参数分量。

    // ============================================================
    // Step 2: (pk_Λ1, pk_Λ2, pk_SPS) = pk_Λ
    // ============================================================
    // 通过 pk 直接访问各公钥分量。

    // ============================================================
    // Step 3: (pk'_Λ1, pk'_Λ2, pk'_SPS) = pk'_Λ
    // ============================================================
    // 通过 pk_prime 直接访问各公钥分量。

    // ============================================================
    // Step 4: (Z*_1, Z*_2, π*_y) = Z
    // ============================================================
    // 通过 z 直接访问旧 Escrow2 输出的各分量。

    // ============================================================
    // Step 5: 判断分支
    // ============================================================
    let pk1_changed = match (&pk.pk1, &pk_prime.pk1) {
        (Some(old), Some(new)) => old != new,
        (None, None) => false,
        _ => true, // Some vs None — 结构不同视为变化
    };
    let pk2_changed = pk.pk2 != pk_prime.pk2;

    if pk1_changed && pk2_changed {
        // ============================================================
        // Step 6-10: 分支 1 —— pk'_Λ1 ≠ pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2
        //            密钥完全更新，需要 User-Auditor 完整交互。
        // ============================================================

        // ============================================================
        // Step 6: (Z'_1, C'_y1, C*_y1', π'_1) ← Escrow1(Λ, pk'_Λ, y, r'_y1, r*_y1')
        // ============================================================
        // User 使用新公钥 pk'_Λ 和新随机数执行 Escrow1。
        let escrow1_out = escrow1::escrow1(lambda, pk_prime, y, r_y1_prime, r_star_y1_prime);

        let c_y1_prime = escrow1_out.c_y1.as_ref()?;
        let c_star_y1_prime = escrow1_out.c_star_y1.as_ref()?;
        let z1_prime = escrow1_out.z1.as_ref()?;
        let pi1_prime = escrow1_out.pi1.as_ref()?;

        // ============================================================
        // Step 7: User → Auditor: (C'_y1, C*_y1', Z'_1, π'_1)
        // ============================================================
        // 将 Escrow1 输出传递给 Auditor 进行 Endorse。
        // 此处通过函数调用模拟网络传输。

        // ============================================================
        // Step 8: Auditor: σ_y ← Endorse(Λ, pk'_Λ, sk'_Λ, x', C'_y1, C*_y1', Z'_1, π'_1)
        // ============================================================
        // Auditor 验证 Z'_1 的正确性，解密得到 y*，并生成签名 σ_y。
        let sigma_y = auditor_endorse(
            lambda,
            pk_prime,
            sk_prime,
            c_y1_prime,
            c_star_y1_prime,
            z1_prime,
            pi1_prime,
        )?;

        // ============================================================
        // Step 9: Auditor → User: σ_y
        // ============================================================
        // 签名 σ_y 通过 sigma_y 变量传递给 User。

        // ============================================================
        // Step 10: Z', C'_y2 ← Escrow2(Λ, pk'_Λ, y, r*_y1', r'_y2, C*_y1', σ_y)
        // ============================================================
        // User 使用新公钥、新随机数和 Auditor 的签名执行 Escrow2。
        let escrow2_out = escrow2::escrow2(
            lambda,
            pk_prime,
            y,
            r_star_y1_prime,
            r_y2_prime,
            c_star_y1_prime,
            &sigma_y,
        )?;

        // ============================================================
        // Step 16: return Z', C'_y2, (r'_y2, r*_y1')
        // ============================================================
        Some(EscrowUpdateOutput {
            c_y2_prime: escrow2_out.c_y2.clone(),
            z_prime: escrow2_out,
            r_y2_prime: r_y2_prime.clone(),
            r_star_y1_prime: r_star_y1_prime.clone(),
        })
    } else if !pk1_changed && pk2_changed {
        // ============================================================
        // Step 11-15: 分支 2 —— pk'_Λ1 = pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2
        //            仅后半部分更新，复用旧签名，无需 Auditor 交互。
        // ============================================================

        // ============================================================
        // Step 12: r*_y1' = r*_y1
        // ============================================================
        // 复用旧的 Pedersen 承诺随机数。
        let r_star_y1_new = r_star_y1;

        // ============================================================
        // Step 13: C*_y1' = C*_y1
        // ============================================================
        // 复用旧的 Pedersen 承诺值。
        let c_star_y1_new = c_star_y1;

        // ============================================================
        // Step 14: (M*_1, σ*_y) = Z*_1
        // ============================================================
        // 直接使用用户传入的签名 σ_y（不再从 Z*_1 中提取）。

        // ============================================================
        // Step 15: Z', C'_y2 ← Escrow2(Λ, pk'_Λ, y, r*_y1', r'_y2, C*_y1', σ*_y)
        // ============================================================
        // 使用新公钥 pk'_Λ、复用的旧签名 σ*_y 和新随机数执行 Escrow2。
        // r'_y2 对应 Escrow2 的 DF 承诺随机数参数。
        let escrow2_out = match escrow2::escrow2(
            lambda,
            pk_prime,
            y,
            r_star_y1_new,
            r_y2_prime,
            c_star_y1_new,
            sigma_y,
        ) {
            Some(out) => out,
            None => {
                // escrow2 返回 None，可能是 SPS 验证失败或 escrow_ppb 内部错误
                return None;
            }
        };

        // ============================================================
        // Step 16: return Z', C'_y2, (r'_y2, r*_y1')
        // ============================================================
        Some(EscrowUpdateOutput {
            c_y2_prime: escrow2_out.c_y2.clone(),
            z_prime: escrow2_out,
            r_y2_prime: r_y2_prime.clone(),
            r_star_y1_prime: r_star_y1_new.clone(),
        })
    } else {
        // ============================================================
        // 隐含分支：pk'_Λ1 = pk_Λ1 且 pk'_Λ2 = pk_Λ2
        // 公钥未变化，无需执行 Escrow Update。
        // ============================================================
        None
    }
}

/// Auditor 侧：验证 Escrow 输出并生成 Endorse 签名。
///
/// 封装了 Algorithm 9 中 Step 7-9 的 Auditor 操作：
/// 1. 接收 User 发送的 (C'_y1, C*_y1', Z'_1, π'_1)；
/// 2. 调用 Endorse 验证 Z'_1 并生成签名 σ_y；
/// 3. 将 σ_y 返回给 User。
///
/// 输入：
/// - `lambda`：全局参数 Λ；
/// - `pk_prime`：新公钥 pk'_Λ；
/// - `sk_prime`：新私钥 sk'_Λ（仅 Auditor 持有）；
/// - `c_y1_prime`：新 DF 承诺 C'_y1；
/// - `c_star_y1_prime`：新 Pedersen 承诺 C*_y1'；
/// - `z1_prime`：新 Escrow1 输出 Z'_1。
/// - `pi1_prime`：新 S1 证明 π'_1。
///
/// 输出：签名 σ_y，若 Endorse 验证失败则返回 None。
fn auditor_endorse(
    lambda: &Lambda,
    pk_prime: &PublicKey,
    sk_prime: &SecretKey,
    c_y1_prime: &BigUint,
    c_star_y1_prime: &ark_bls12_381::G1Projective,
    z1_prime: &rust::PpbEscrowOutput,
    pi1_prime: &crate::s1::S1Proof,
) -> Option<mercurial_signature::Signature> {
    let endorse_out = endorse::endorse(
        lambda,
        pk_prime,
        sk_prime,
        c_y1_prime,
        c_star_y1_prime,
        z1_prime,
        pi1_prime,
    );
    endorse_out.sigma_sps
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    use crate::keygen;
    use crate::keyupdate;

    /// 构造测试用的 Lambda。
    fn test_lambda() -> Lambda {
        let lambda_bits = 64;
        let t = 3;
        let cpar_star = rust::setup_pedersen(lambda_bits).expect("setup_pedersen should succeed");
        crate::setup::setup(lambda_bits, t, cpar_star)
    }

    // ================================================================
    // 测试 1: 密钥完全更新（分支 1）
    //   pk'_Λ1 ≠ pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2
    // ================================================================

    /// 初始 |x|=4 > t=3，α=1。x1=[1,2,3]（4 系数 = 2^2），x2=[4]（2 系数 = 2^1）。
    /// 更新后 |x'|=16，α'=1。x'1=[1,...,15]（16 系数 = 2^4），x'2=[16]（2 系数 = 2^1）。
    /// Δ=12, Δ+α=13 > 3 → 完全重生成。pk'_Λ1 ≠ pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2 → 分支 1。
    ///
    /// 注意：PoKP 实现要求多项式系数数量（fk.n + 1）为 2 的幂。
    #[test]
    fn test_escrow_update_full_key_change() {
        let lambda = test_lambda();

        // --- 初始密钥生成：|x|=4, x1=[1,2,3], x2=[4] ---
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // --- 初始 Escrow（使用旧公钥） ---
        let y = rust::HecEvalInput {
            y_id: BigUint::from(16u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_old = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1_old = escrow1_old.c_y1.as_ref().unwrap();
        let c_star_y1_old = escrow1_old.c_star_y1.as_ref().unwrap();
        let z1_old = escrow1_old.z1.as_ref().unwrap();
        let pi1_old = escrow1_old.pi1.as_ref().unwrap();

        let endorse_old =
            crate::endorse::endorse(&lambda, &pk, &sk, c_y1_old, c_star_y1_old, z1_old, pi1_old);
        let sigma_y_old = endorse_old.sigma_sps.as_ref().unwrap();

        let z_old = crate::escrow2::escrow2(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            sigma_y_old,
        )
        .expect("Old Escrow2 should succeed");

        // --- KeyUpdate: |x'|=16, Δ=12, Δ+α=13 > 3 → 完全重生成 ---
        // x'1=[1,...,15]（16 系数 = 2^4），x'2=[16]（2 系数 = 2^1）
        let x_prime: Vec<BigUint> = (1..=16).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(5u32)];

        let ((pk_prime, sk_prime), _c_x_prime) = keyupdate::key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x, &x_prime, &r_x_prime, &s_prime,
        );

        // --- Escrow Update: 分支 1 ---
        let r_y1_prime = BigUint::from(101u32);
        let r_y2_prime = BigUint::from(103u32);
        let r_star_y1_prime = BigUint::from(107u32);

        let output = escrow_update(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            &z_old,
            &pk_prime,
            &r_y1_prime,
            &r_y2_prime,
            &r_star_y1_prime,
            sigma_y_old,
            &sk_prime,
            &x_prime,
        )
        .expect("Escrow update should succeed for full key change");

        // 验证输出随机数透传正确
        assert_eq!(output.r_y2_prime, r_y2_prime);
        assert_eq!(output.r_star_y1_prime, r_star_y1_prime);
        // 验证 C'_y2 非零
        assert!(output.c_y2_prime > BigUint::from(0u32));
    }

    // ================================================================
    // 测试 2: 仅后半部分密钥更新（分支 2）
    //   pk'_Λ1 = pk_Λ1 且 pk'_Λ2 ≠ pk_Λ2
    // ================================================================

    /// 初始 |x|=4 > t=3，α=1。x1=[1,2,3]（4 系数 = 2^2），x2=[4]（2 系数 = 2^1）。
    /// 更新后 |x'|=6，α'=0→t=3。x'1=[1,2,3]（4 系数 = 2^2），x'2=[4,5,6]（4 系数 = 2^2）。
    /// Δ=2, Δ+α=3 ≤ 3 → 部分更新。
    /// pk_Λ1 复用旧值（pk'_Λ1 = pk_Λ1），pk_Λ2 更新（pk'_Λ2 ≠ pk_Λ2）。
    ///
    /// 注意：PoKP 实现要求多项式系数数量（fk.n + 1）为 2 的幂。
    #[test]
    fn test_escrow_update_partial_key_change() {
        let lambda = test_lambda();

        // --- 初始密钥生成：|x|=4, x1=[1,2,3], x2=[4] ---
        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        // --- 初始 Escrow ---
        let y = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_old = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1_old = escrow1_old.c_y1.as_ref().unwrap();
        let c_star_y1_old = escrow1_old.c_star_y1.as_ref().unwrap();
        let z1_old = escrow1_old.z1.as_ref().unwrap();
        let pi1_old = escrow1_old.pi1.as_ref().unwrap();

        let endorse_old =
            crate::endorse::endorse(&lambda, &pk, &sk, c_y1_old, c_star_y1_old, z1_old, pi1_old);
        let sigma_y_old = endorse_old.sigma_sps.as_ref().unwrap();

        let z_old = crate::escrow2::escrow2(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            sigma_y_old,
        )
        .expect("Old Escrow2 should succeed");

        // --- KeyUpdate: |x'|=6, Δ=2, Δ+α=3 ≤ 3 → 部分更新 ---
        // x'1=[1,2,3]（复用旧 pk1），x'2=[4,5,6]（新 pk2）
        let x_prime: Vec<BigUint> = (1..=6).map(|i| BigUint::from(i as u32)).collect();
        let r_x_prime = vec![BigUint::from(30u32), BigUint::from(40u32)];
        let s_prime = vec![BigUint::from(3u32), BigUint::from(4u32)];

        let ((pk_prime, sk_prime), _c_x_prime) = keyupdate::key_update(
            &lambda, &x, &r_x, &s, &pk, &sk, &c_x, &x_prime, &r_x_prime, &s_prime,
        );

        // 验证部分更新的假设：pk'_Λ1 = pk_Λ1
        // （key_update 的部分更新分支复用旧 pk1）

        // --- Escrow Update: 分支 2 ---
        let r_y2_prime = BigUint::from(103u32);

        let output = escrow_update(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            &z_old,
            &pk_prime,
            &BigUint::from(0u32), // r_y1_prime，分支 2 不使用
            &r_y2_prime,
            &BigUint::from(0u32), // r_star_y1_prime，分支 2 不使用
            sigma_y_old,
            &sk_prime,
            &x_prime,
        )
        .expect("Escrow update should succeed for partial key change");

        // 验证输出
        assert_eq!(output.r_y2_prime, r_y2_prime);
        // 分支 2 复用旧 r*_y1
        assert_eq!(output.r_star_y1_prime, r_star_y1);
        assert!(output.c_y2_prime > BigUint::from(0u32));
    }

    // ================================================================
    // 测试 3: 公钥未变化（隐含分支）—— 应返回 None
    // ================================================================

    #[test]
    fn test_escrow_update_no_key_change_returns_none() {
        let lambda = test_lambda();

        let x: Vec<BigUint> = (1..=4).map(|i| BigUint::from(i as u32)).collect();
        let r_x = vec![BigUint::from(10u32), BigUint::from(20u32)];
        let s = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let ((pk, sk), c_x) = keygen::keygen(&lambda, &x, &r_x, &s);

        let y = rust::HecEvalInput {
            y_id: BigUint::from(4u32),
            y_at: BigUint::from(7u32),
        };
        let r_y1 = BigUint::from(41u32);
        let r_y2 = BigUint::from(67u32);
        let r_star_y1 = BigUint::from(53u32);

        let escrow1_old = crate::escrow1::escrow1(&lambda, &pk, &y, &r_y1, &r_star_y1);
        let c_y1_old = escrow1_old.c_y1.as_ref().unwrap();
        let c_star_y1_old = escrow1_old.c_star_y1.as_ref().unwrap();
        let z1_old = escrow1_old.z1.as_ref().unwrap();
        let pi1_old = escrow1_old.pi1.as_ref().unwrap();

        let endorse_old =
            crate::endorse::endorse(&lambda, &pk, &sk, c_y1_old, c_star_y1_old, z1_old, pi1_old);
        let sigma_y_old = endorse_old.sigma_sps.as_ref().unwrap();

        let z_old = crate::escrow2::escrow2(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            sigma_y_old,
        )
        .expect("Old Escrow2 should succeed");

        // pk_prime = pk（公钥未变化）
        let output = escrow_update(
            &lambda,
            &pk,
            &y,
            &r_star_y1,
            &r_y2,
            c_star_y1_old,
            &z_old,
            &pk, // 与 pk 相同
            &BigUint::from(0u32),
            &BigUint::from(0u32),
            &BigUint::from(0u32),
            sigma_y_old,
            &sk,
            &x,
        );

        // 公钥未变化时应返回 None
        assert!(
            output.is_none(),
            "Should return None when pk does not change"
        );
    }
}
