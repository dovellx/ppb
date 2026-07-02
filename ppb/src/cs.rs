use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::error::{CryptoError, CryptoResult};
use crate::math::{abs_qr_rep, generate_safe_rsa_modulus, modinv, sample_abs_qr_element};

/// 修改版 Camenisch-Shoup 参数。
///
/// 字段含义：
/// 1. n: 安全 RSA 模数 n = pq
/// 2. n2: n^2，避免重复计算
/// 3. g: 位于 |QR_{n^2}| 的生成元素（按论文构造）
/// 4. h: 取值为 1 + n（Paillier 型提升基）
#[derive(Debug, Clone)]
pub struct CsParams {
    pub n: BigUint,
    pub n2: BigUint,
    pub g: BigUint,
    pub h: BigUint,
}

/// CS 公钥：k = |g^x| mod n^2。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CsPubKey {
    pub k: BigUint,
}

/// CS 私钥：指数 x。
#[derive(Debug, Clone)]
pub struct CsSecretKey {
    pub x: BigUint,
}

/// CS 密文：c = (c0, c1)。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CsCiphertext {
    pub c0: BigUint,
    pub c1: BigUint,
}

/// Setup(1^lambda) -> paramsCS
///
/// 实现细节：
/// 1. 生成安全模数 n = pq；
/// 2. 在 |QR_{n^2}| 中取 g'，并设 g = |(g')^n|；
/// 3. 设 h = 1 + n。
pub fn setup_cs(bits: usize) -> CryptoResult<CsParams> {
    let (_, _, n) = generate_safe_rsa_modulus(bits)?;
    let n2 = &n * &n;
    let mut rng = OsRng;

    let g_prime = sample_abs_qr_element(&mut rng, &n2);
    let g_raw = g_prime.modpow(&n, &n2);
    let g = abs_qr_rep(&g_raw, &n2);

    let h = &n + BigUint::one();
    Ok(CsParams { n, n2, g, h })
}

/// KeyGen(paramsCS) -> (pk, sk)
///
/// 私钥 x 从 [1, n^2/4) 采样，公钥 k = |g^x|。
pub fn keygen_cs(params: &CsParams) -> CryptoResult<(CsPubKey, CsSecretKey)> {
    let mut rng = OsRng;
    let upper = &params.n2 >> 2usize;
    if upper <= BigUint::one() {
        return Err(CryptoError::InvalidInput("n^2 too small"));
    }

    let x = rng.gen_biguint_range(&BigUint::one(), &upper);
    let k_raw = params.g.modpow(&x, &params.n2);
    let k = abs_qr_rep(&k_raw, &params.n2);
    Ok((CsPubKey { k }, CsSecretKey { x }))
}

/// Enc(pk, m in [0, n)) -> c
///
/// 采样 r in [1, n/4)，并输出：
/// c0 = |g^r|,
/// c1 = |k^r * h^m|。
pub fn enc_cs(params: &CsParams, pk: &CsPubKey, m: &BigUint) -> CryptoResult<CsCiphertext> {
    if m >= &params.n {
        return Err(CryptoError::InvalidInput("message must be in [0, n)"));
    }

    let mut rng = OsRng;
    let upper = &params.n >> 2usize;
    if upper <= BigUint::one() {
        return Err(CryptoError::InvalidInput("n too small"));
    }
    let r = rng.gen_biguint_range(&BigUint::one(), &upper);

    enc_cs_with_randomness(params, pk, m, &r)
}

/// 使用指定随机数执行 CS 加密：Enc(pk, m; r)。
///
/// 该 helper 供 HEC/PPB 证明代码复用：证明生成器需要重建“某个公开密文
/// 正是用 witness 中的随机数加密得到的”，因此不能只调用内部采样随机数的
/// `enc_cs`。随机数统一映射到 `Z_n`，密文分量仍规约为 `|QR_{n^2}|`
/// 代表元，从而与 `enc_cs` 的输出语义完全一致。
pub(crate) fn enc_cs_with_randomness(
    params: &CsParams,
    pk: &CsPubKey,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<CsCiphertext> {
    if m >= &params.n {
        return Err(CryptoError::InvalidInput("message must be in [0, n)"));
    }
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let r_mod = r % &params.n;
    let c0_raw = params.g.modpow(&r_mod, &params.n2);
    let c0 = abs_qr_rep(&c0_raw, &params.n2);

    let kr = pk.k.modpow(&r_mod, &params.n2);
    let hm = params.h.modpow(m, &params.n2);
    let c1_raw = (kr * hm) % &params.n2;
    let c1 = abs_qr_rep(&c1_raw, &params.n2);

    Ok(CsCiphertext { c0, c1 })
}

/// Dec(sk, c=(c0,c1)) -> m
///
/// 按论文给出的“绝对值表示”修正规则实现：
/// 1. t = 2^{-1} mod n
/// 2. M = c1 / c0^x mod n^2
/// 3. m = ((M^(2t) mod n^2) - 1) / n
///
/// 关键点：指数使用 2t 本身，而不是 (2t mod n)。
/// 否则在 |QR_{n^2}| 代表元下可能无法正确消除符号歧义。
pub fn dec_cs(params: &CsParams, sk: &CsSecretKey, c: &CsCiphertext) -> CryptoResult<BigUint> {
    let two = BigUint::from(2u32);
    let t = modinv(&two, &params.n)?;
    let exp = &two * &t;

    let c0x = c.c0.modpow(&sk.x, &params.n2);
    let c0x_inv = modinv(&c0x, &params.n2)?;
    let m_term = (&c.c1 * c0x_inv) % &params.n2;

    let lifted = m_term.modpow(&exp, &params.n2);
    if lifted.is_zero() {
        return Err(CryptoError::InvalidInput("invalid ciphertext structure"));
    }

    Ok((&lifted - BigUint::one()) / &params.n)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;

    #[test]
    fn test_cs_roundtrip() {
        let params = setup_cs(64).expect("setup cs should succeed");
        let (pk, sk) = keygen_cs(&params).expect("keygen should succeed");
        let m = BigUint::from(42u32);
        let ct = enc_cs(&params, &pk, &m).expect("enc should succeed");
        let dec = dec_cs(&params, &sk, &ct).expect("dec should succeed");
        assert_eq!(dec, m);
    }
}
