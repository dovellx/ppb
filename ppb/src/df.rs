use num_bigint::{BigUint, RandBigInt};
use rand::rngs::OsRng;

use crate::error::{CryptoError, CryptoResult};
use crate::math::{generate_safe_rsa_modulus, sample_unit_mod_n2};

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
pub fn commit_df(params: &DfParams, m: &BigUint, randomness_bits: usize) -> CryptoResult<DfCommitment> {
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
pub fn commit_df_with_opening(params: &DfParams, m: &BigUint, r: &BigUint) -> CryptoResult<DfCommitment> {
    let gm = params.g.modpow(m, &params.n2);
    let hr = params.h.modpow(r, &params.n2);
    let c = (gm * hr) % &params.n2;

    Ok(DfCommitment { c, r: r.clone() })
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
        let manual = (params.g.modpow(&m, &params.n2) * params.h.modpow(&r, &params.n2)) % &params.n2;

        assert_eq!(com.c, manual);
        assert_eq!(com.r, r);
    }
}
