use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::error::{CryptoError, CryptoResult};
use crate::hash::fiat_shamir_challenge_biguints;
use crate::math::{abs_qr_rep, gcd, generate_safe_rsa_modulus, sample_unit_mod_n2};

/// Damgard-Fujisaki 参数（工作在 Z_{n^2}）。
#[derive(Debug, Clone)]
pub struct DfParams {
    pub n: BigUint,
    pub n2: BigUint,
    pub g: BigUint,
    pub h: BigUint,
}

/// DF 承诺与开口。
///
/// c = g^m * h^r mod n^2
/// r 为开口随机数。
#[derive(Debug, Clone)]
pub struct DfCommitment {
    pub c: BigUint,
    pub r: BigUint,
}

/// SetupDF(1^lambda) -> paramsDF
///
/// 1. 生成安全模数 n = pq；
/// 2. 在 Z*_{n^2} 中采样 g, h。
pub fn setup_df(bits: usize) -> CryptoResult<DfParams> {
    let (_, _, n) = generate_safe_rsa_modulus(bits)?;
    let n2 = &n * &n;

    let mut rng = OsRng;
    let g = sample_unit_mod_n2(&mut rng, &n2);
    let h = sample_unit_mod_n2(&mut rng, &n2);

    Ok(DfParams { n, n2, g, h })
}

/// CommitDF(params, m) -> (C, O)
///
/// 按论文形式，O = r，C = g^m * h^r mod n^2。
/// randomness_bits 对应开口随机数的位长（可由上层设为 2B+lambda）。
pub fn commit_df(
    params: &DfParams,
    m: &BigUint,
    randomness_bits: usize,
) -> CryptoResult<DfCommitment> {
    if randomness_bits == 0 {
        return Err(CryptoError::InvalidInput("randomness bits must be > 0"));
    }

    let bits_u64 = u64::try_from(randomness_bits)
        .map_err(|_| CryptoError::InvalidInput("randomness bits too large"))?;
    let mut rng = OsRng;
    let r = rng.gen_biguint(bits_u64);

    commit_df_with_opening(params, m, &r)
}

/// 测试友好的 CommitDF：允许外部指定开口 r。
///
/// 该接口不会额外约束 m 的范围，
/// 由协议上层决定消息空间与绑定/隐藏参数。
pub fn commit_df_with_opening(
    params: &DfParams,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<DfCommitment> {
    let gm = params.g.modpow(m, &params.n2);
    let hr = params.h.modpow(r, &params.n2);
    let c = (gm * hr) % &params.n2;

    Ok(DfCommitment { c, r: r.clone() })
}

const VECTOR_COMMITMENT_DOMAIN: u32 = 0x5331; // "S1"

/// 为 DF/S1 向量承诺确定性派生基。
///
/// 论文里的 `cpar=(G_0,...,G_n,H)` 需要一组向量基；当前工程的
/// `DfParams` 只显式保存 `(g,h)`，所以这里从公共参数和下标哈希派生
/// `G_i`。验证方可重算同一组基，调用方不需要额外保存。
pub(crate) fn derive_df_vector_bases(params: &DfParams, len: usize) -> CryptoResult<Vec<BigUint>> {
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let mut bases = Vec::with_capacity(len);
    let domain = BigUint::from(VECTOR_COMMITMENT_DOMAIN);
    for i in 0..len {
        let idx_u64 = u64::try_from(i + 1)
            .map_err(|_| CryptoError::InvalidInput("vector base index too large"))?;
        let idx = BigUint::from(idx_u64);
        let mut counter = BigUint::zero();

        loop {
            let candidate = fiat_shamir_challenge_biguints(&[
                &domain, &params.n, &params.n2, &params.g, &params.h, &idx, &counter,
            ]) % &params.n2;

            if gcd(candidate.clone(), params.n2.clone()) != BigUint::one() {
                counter += BigUint::one();
                continue;
            }

            let base_raw = candidate.modpow(&params.n, &params.n2);
            let base = abs_qr_rep(&base_raw, &params.n2);
            if base > BigUint::one() {
                bases.push(base);
                break;
            }

            counter += BigUint::one();
        }
    }

    Ok(bases)
}

/// 使用给定多基计算 DF 向量承诺：
///
/// `C = H^r * Π_i G_i^{a_i} mod n^2`。
pub(crate) fn commit_df_vector_with_bases(
    params: &DfParams,
    bases: &[BigUint],
    values: &[BigUint],
    r: &BigUint,
) -> CryptoResult<DfCommitment> {
    if bases.len() != values.len() {
        return Err(CryptoError::InvalidInput(
            "vector bases/value length mismatch",
        ));
    }

    let mut c = params.h.modpow(r, &params.n2);
    for (base, value) in bases.iter().zip(values.iter()) {
        c = (c * base.modpow(value, &params.n2)) % &params.n2;
    }

    Ok(DfCommitment { c, r: r.clone() })
}

/// DF 多项式承诺：对输入列表 x 和掩码 s 计算多项式系数，
/// 使用确定性多基承诺系数向量。
///
/// 对应 Algorithm 1: Commit(Λ, x, r_x; s) -> C_x
///
/// 过程：
/// 1. P <- s * ∏(x - x_i)，展开为系数向量 coeffs；
/// 2. C = H^r * Π_i G_i^{coeffs_i} mod n^2。
///
/// 返回承诺值 C 和系数向量 coeffs。
pub fn commit_df_multibase(
    params: &DfParams,
    x: &[BigUint],
    r: &BigUint,
    s: &BigUint,
) -> CryptoResult<(DfCommitment, Vec<BigUint>)> {
    // Step 1: P <- s * ∏(x - x_i)，展开为系数向量
    let coeffs = crate::hec::expand_roots_to_coefficients_mod_n(x, s, &params.n)
        .map_err(|_| CryptoError::InvalidInput("expand_roots_to_coefficients_mod_n failed"))?;

    // Step 2: C = H^r * Π_i G_i^{a_i} mod n^2
    let bases = derive_df_vector_bases(params, coeffs.len())?;
    let commitment = commit_df_vector_with_bases(params, &bases, &coeffs, r)?;

    Ok((commitment, coeffs))
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;

    #[test]
    fn test_df_commit_manual_check() {
        let params = setup_df(64).expect("setup df should succeed");
        let m = BigUint::from(12345u32);
        let r = BigUint::from(67890u32);

        let com = commit_df_with_opening(&params, &m, &r).expect("commit should succeed");
        let manual =
            (params.g.modpow(&m, &params.n2) * params.h.modpow(&r, &params.n2)) % &params.n2;

        assert_eq!(com.c, manual);
        assert_eq!(com.r, r);
    }

    #[test]
    fn test_df_multibase_matches_manual_vector_formula() {
        let params = setup_df(64).expect("setup df should succeed");
        let x = vec![BigUint::from(2u32), BigUint::from(3u32)];
        let r = BigUint::from(7u32);
        let s = BigUint::from(1u32);

        let (commitment, coeffs) =
            commit_df_multibase(&params, &x, &r, &s).expect("multibase commit should succeed");
        let bases = derive_df_vector_bases(&params, coeffs.len()).expect("bases should derive");
        let manual = commit_df_vector_with_bases(&params, &bases, &coeffs, &r)
            .expect("manual commit should succeed");

        assert_eq!(commitment.c, manual.c);
        assert_eq!(commitment.r, r);
    }

    #[test]
    fn test_df_multibase_binds_positions_not_only_sum() {
        let params = setup_df(64).expect("setup df should succeed");
        let bases = derive_df_vector_bases(&params, 2).expect("bases should derive");
        let r = BigUint::from(11u32);

        let a = vec![BigUint::from(1u32), BigUint::from(2u32)];
        let b = vec![BigUint::from(2u32), BigUint::from(1u32)];
        let ca =
            commit_df_vector_with_bases(&params, &bases, &a, &r).expect("commit should succeed");
        let cb =
            commit_df_vector_with_bases(&params, &bases, &b, &r).expect("commit should succeed");

        assert_eq!(
            a.iter().fold(BigUint::from(0u32), |acc, v| acc + v),
            b.iter().fold(BigUint::from(0u32), |acc, v| acc + v)
        );
        assert_ne!(ca.c, cb.c);
    }
}
