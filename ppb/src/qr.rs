use num_bigint::{BigUint, RandBigInt};
use rand::rngs::OsRng;

use crate::error::{CryptoError, CryptoResult};
use crate::math::{abs_qr_rep, generate_safe_rsa_modulus, sample_abs_qr_element, sample_unit_mod_n2};

/// |QR_{n^2}| 承诺参数。
#[derive(Debug, Clone)]
pub struct QrParams {
    pub n: BigUint,
    pub n2: BigUint,
    pub g: BigUint,
    pub g_prime: BigUint,
    pub h_prime: BigUint,
}

/// 双元承诺值 C = (C1, C2)。
#[derive(Debug, Clone)]
pub struct QrCommitment {
    pub c1: BigUint,
    pub c2: BigUint,
}

/// 开口 O = (s, r)。
#[derive(Debug, Clone)]
pub struct QrOpening {
    pub s: BigUint,
    pub r: BigUint,
}

/// SetupQR(1^lambda) -> paramsQR
///
/// 1. 生成安全模数 n = pq；
/// 2. 在 |QR_{n^2}| 采样 g；
/// 3. 在 Z*_{n^2} 采样 (g', h')。
pub fn setup_qr(bits: usize) -> CryptoResult<QrParams> {
    let (_, _, n) = generate_safe_rsa_modulus(bits)?;
    let n2 = &n * &n;

    let mut rng = OsRng;
    let g = sample_abs_qr_element(&mut rng, &n2);
    let g_prime = sample_unit_mod_n2(&mut rng, &n2);
    let h_prime = sample_unit_mod_n2(&mut rng, &n2);

    Ok(QrParams {
        n,
        n2,
        g,
        g_prime,
        h_prime,
    })
}

/// ComQR(params, M) -> (C, O)
///
/// C1 = |M * g^s| mod n^2
/// C2 = (g')^s * (h')^r mod n^2
///
/// randomness_bits 由上层映射到论文中的 2B+lambda。
pub fn commit_qr(params: &QrParams, m: &BigUint, randomness_bits: usize) -> CryptoResult<(QrCommitment, QrOpening)> {
    if m >= &params.n2 {
        return Err(CryptoError::InvalidInput("M must be in Z_{n^2}"));
    }
    if randomness_bits == 0 {
        return Err(CryptoError::InvalidInput("randomness bits must be > 0"));
    }

    let bits_u64 = u64::try_from(randomness_bits)
        .map_err(|_| CryptoError::InvalidInput("randomness bits too large"))?;
    let mut rng = OsRng;
    let s = rng.gen_biguint(bits_u64);
    let r = rng.gen_biguint(bits_u64);

    commit_qr_with_opening(params, m, &s, &r)
}

/// 测试友好的 ComQR：外部指定开口 (s, r)。
pub fn commit_qr_with_opening(
    params: &QrParams,
    m: &BigUint,
    s: &BigUint,
    r: &BigUint,
) -> CryptoResult<(QrCommitment, QrOpening)> {
    if m >= &params.n2 {
        return Err(CryptoError::InvalidInput("M must be in Z_{n^2}"));
    }

    let gs = params.g.modpow(s, &params.n2);
    let c1_raw = (m * gs) % &params.n2;
    let c1 = abs_qr_rep(&c1_raw, &params.n2);

    let gp_s = params.g_prime.modpow(s, &params.n2);
    let hp_r = params.h_prime.modpow(r, &params.n2);
    let c2 = (gp_s * hp_r) % &params.n2;

    let commitment = QrCommitment { c1, c2 };
    let opening = QrOpening {
        s: s.clone(),
        r: r.clone(),
    };
    Ok((commitment, opening))
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;
    use crate::math::abs_qr_rep;

    #[test]
    fn test_qr_commit_manual_check() {
        let params = setup_qr(64).expect("setup qr should succeed");
        let m = BigUint::from(987u32);
        let s = BigUint::from(111u32);
        let r = BigUint::from(222u32);

        let (com, opening) = commit_qr_with_opening(&params, &m, &s, &r).expect("commit qr should succeed");

        let gs = params.g.modpow(&s, &params.n2);
        let c1_manual = abs_qr_rep(&((m.clone() * gs) % &params.n2), &params.n2);
        let c2_manual =
            (params.g_prime.modpow(&s, &params.n2) * params.h_prime.modpow(&r, &params.n2)) % &params.n2;

        assert_eq!(com.c1, c1_manual);
        assert_eq!(com.c2, c2_manual);
        assert_eq!(opening.s, s);
        assert_eq!(opening.r, r);
    }
}
