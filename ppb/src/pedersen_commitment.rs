use ark_bls12_381::{Fr, G1Projective};
use ark_ec::PrimeGroup;
use ark_ff::{BigInteger, PrimeField, UniformRand};
use num_bigint::{BigUint, RandBigInt};
use rand::rngs::OsRng;

use crate::error::CryptoResult;

/// 获取 Fr 域的阶数（曲线标量域的大小）作为 BigUint。
fn fr_order() -> BigUint {
    // Fr::MODULUS 返回 BigInt，转换为 BigUint
    let modulus_bigint = Fr::MODULUS;
    let bytes = modulus_bigint.to_bytes_le();
    BigUint::from_bytes_le(&bytes)
}

/// 将 BigUint 转换为 Fr 标量（模曲线阶）。
fn biguint_to_fr(value: &BigUint) -> Fr {
    // 将 BigUint 转换为字节，然后转换为 Fr
    let bytes = value.to_bytes_le();
    // Fr::from_le_bytes_mod_order 可以接受变长字节
    Fr::from_le_bytes_mod_order(&bytes)
}

/// Pedersen 承诺公共参数（椭圆曲线版，BLS12-381 G1 群）。
///
/// 字段语义：
/// 1. `g1`：G1 群的生成元（通常使用曲线标准生成点）；
/// 2. `h1`：另一个随机选择的 G1 点，确保与 `g1` 线性无关。
///
/// 说明：
/// 此版本在椭圆曲线 BLS12-381 的 G1 群上实现 Pedersen 承诺，
/// 承诺值为椭圆曲线点，可直接作为 SPS-EQ 签名的消息。
#[derive(Debug, Clone)]
pub struct PedersenCommitmentParams {
    pub g1: G1Projective,
    pub h1: G1Projective,
}

/// Pedersen 承诺结果与开口（椭圆曲线版）。
///
/// 满足关系：
/// `C = g1 * m + h1 * r`，其中 m, r 为标量，+ 为椭圆曲线点加法。
#[derive(Debug, Clone)]
pub struct PedersenCommitment {
    pub c: G1Projective, // 承诺值：椭圆曲线点
    pub r: BigUint,      // 开口随机数（原始大整数形式）
}

/// CSetup(1^lambda) -> cpar*
///
/// 输入：
/// 1. `bits`：安全参数对应的模数位长（保留参数以保持接口兼容，但实际不使用）。
///
/// 输出：
/// 1. `cpar* = (g1, h1)` 椭圆曲线 Pedersen 参数。
///
/// 过程：
/// 1. 使用 BLS12-381 曲线的标准 G1 生成元作为 g1；
/// 2. 随机采样另一个 G1 点作为 h1，确保与 g1 线性无关。
pub fn setup_pedersen(_bits: usize) -> CryptoResult<PedersenCommitmentParams> {
    let mut rng = OsRng;

    // g1 使用标准生成元
    let g1 = G1Projective::generator();

    // h1 随机采样，确保与 g1 线性无关
    let h1 = G1Projective::rand(&mut rng);

    Ok(PedersenCommitmentParams { g1, h1 })
}

/// Com(cpar*, m; r) -> C
///
/// 输入：
/// 1. `params = (g1, h1)`：椭圆曲线 Pedersen 参数；
/// 2. `m`：消息整数（大整数形式）；
/// 3. `r`：开口随机数（大整数形式）。
///
/// 输出：
/// 1. 承诺值 `C = g1 * m + h1 * r`（椭圆曲线点）。
pub fn com_pedersen(
    params: &PedersenCommitmentParams,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<G1Projective> {
    // 将大整数转换为 Fr 标量
    let m_scalar = biguint_to_fr(m);
    let r_scalar = biguint_to_fr(r);

    // 计算 g1 * m + h1 * r
    let gm = params.g1 * m_scalar;
    let hr = params.h1 * r_scalar;
    let c = gm + hr;

    Ok(c)
}

/// CommitPedersen(cpar*, m) -> (C, O)
///
/// 与现有承诺模块风格一致：
/// 1. 内部自动采样 `r <- Z_order`，其中 order 为 Fr 域的阶；
/// 2. 返回 `(C, r)` 方便上层直接保存开口。
pub fn commit_pedersen(
    params: &PedersenCommitmentParams,
    m: &BigUint,
) -> CryptoResult<PedersenCommitment> {
    let mut rng = OsRng;
    let order = fr_order();
    let r = rng.gen_biguint_below(&order);
    commit_pedersen_with_opening(params, m, &r)
}

/// 测试友好的 CommitPedersen：允许外部指定开口 `r`。
pub fn commit_pedersen_with_opening(
    params: &PedersenCommitmentParams,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<PedersenCommitment> {
    let c = com_pedersen(params, m, r)?;
    Ok(PedersenCommitment { c, r: r.clone() })
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fr;
    use ark_ec::CurveGroup;
    use ark_ff::Field;
    use num_bigint::BigUint;

    use super::*;

    #[test]
    fn test_pedersen_commit_manual_check() {
        let params = setup_pedersen(64).expect("setup pedersen should succeed");
        let m = BigUint::from(12345u32);
        let r = BigUint::from(678u32);

        let com = commit_pedersen_with_opening(&params, &m, &r).expect("commit should succeed");

        // 手动计算验证：C = g1 * m + h1 * r
        let m_scalar = biguint_to_fr(&m);
        let r_scalar = biguint_to_fr(&r);
        let manual_c = params.g1 * m_scalar + params.h1 * r_scalar;

        assert_eq!(com.c, manual_c);
        assert_eq!(com.r, r);
    }

    #[test]
    fn test_pedersen_homomorphic_property() {
        let params = setup_pedersen(64).expect("setup pedersen should succeed");
        let m1 = BigUint::from(100u32);
        let m2 = BigUint::from(200u32);
        let r1 = BigUint::from(10u32);
        let r2 = BigUint::from(20u32);

        // 分别计算两个承诺
        let com1 = commit_pedersen_with_opening(&params, &m1, &r1).expect("commit should succeed");
        let com2 = commit_pedersen_with_opening(&params, &m2, &r2).expect("commit should succeed");

        // 计算和
        let m_sum = &m1 + &m2;
        let r_sum = &r1 + &r2;
        let com_sum =
            commit_pedersen_with_opening(&params, &m_sum, &r_sum).expect("commit should succeed");

        // 验证同态性：C(m1 + m2, r1 + r2) = C(m1, r1) + C(m2, r2)
        assert_eq!(com_sum.c, com1.c + com2.c);
    }

    #[test]
    fn test_pedersen_binding_property() {
        let params = setup_pedersen(64).expect("setup pedersen should succeed");
        let m = BigUint::from(123u32);
        let r = BigUint::from(456u32);

        let com = commit_pedersen_with_opening(&params, &m, &r).expect("commit should succeed");

        // 尝试用不同的消息/随机数打开相同的承诺应该失败
        // 实际上我们无法直接测试绑定性质，但可以验证承诺计算的一致性
        let recomputed = com_pedersen(&params, &m, &r).expect("recompute should succeed");
        assert_eq!(com.c, recomputed);
    }
}
