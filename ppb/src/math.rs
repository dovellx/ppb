use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::RngCore;
use rand::rngs::OsRng;

use crate::error::{CryptoError, CryptoResult};

/// 将元素映射到绝对值二次剩余群 |QR_{n^2}| 的代表元。
///
/// 规则：
/// 若 x > floor(n^2 / 2)，返回 n^2 - x；否则返回 x。
///
/// 该映射用于把互为相反数的两个代表统一到“绝对值”侧，
/// 是本文实现中 |QR_{n^2}| 语义的基础工具。
pub fn abs_qr_rep(x: &BigUint, n2: &BigUint) -> BigUint {
    let half = n2 >> 1usize;
    if x > &half { n2 - x } else { x.clone() }
}

/// Euclid 算法：计算 gcd(a, b)。
pub fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// 扩展 Euclid：求 a 在模 m 下的逆元。
///
/// 返回值 inv 满足 a * inv = 1 (mod m)。
/// 若 gcd(a, m) != 1，则返回错误。
pub fn modinv(a: &BigUint, m: &BigUint) -> CryptoResult<BigUint> {
    let mut t = BigInt::zero();
    let mut new_t = BigInt::one();
    let mut r = m
        .to_bigint()
        .ok_or(CryptoError::InvalidInput("modulus conversion failed"))?;
    let mut new_r = a
        .to_bigint()
        .ok_or(CryptoError::InvalidInput("value conversion failed"))?;

    while new_r != BigInt::zero() {
        let q = &r / &new_r;
        let temp_t = &t - &q * &new_t;
        t = new_t;
        new_t = temp_t;

        let temp_r = &r - &q * &new_r;
        r = new_r;
        new_r = temp_r;
    }

    if r != BigInt::one() {
        return Err(CryptoError::ModularInverseUnavailable);
    }

    let m_bi = m
        .to_bigint()
        .ok_or(CryptoError::InvalidInput("modulus conversion failed"))?;
    let mut t_norm = t % &m_bi;
    if t_norm < BigInt::zero() {
        t_norm += &m_bi;
    }
    t_norm
        .try_into()
        .map_err(|_| CryptoError::InvalidInput("inverse conversion failed"))
}

/// 根据 n^2 推导协议中使用的 B（位长近似）。
///
/// 推导依据：
/// 1. 多处证明代码中把明文上界写成 2^B 量级；
/// 2. 在当前实现里，常用近似关系是 2^B ≈ n^2 / 4；
/// 3. 因此可用 B ≈ bitlen(n^2) - 2。
///
/// 该函数的目标不是“精确恢复论文中所有上下界常数”，
/// 而是统一工程口径，避免不同模块各自拷贝并演化出不一致版本。
///
/// 返回错误的场景：
/// 1. n^2 位长无法安全转换为 usize；
/// 2. n^2 太小（bitlen < 3）导致 B 非正或无意义。
pub fn derive_b_bits_from_n2(n2: &BigUint) -> CryptoResult<usize> {
    let bits_u64 = n2.bits();
    let bits = usize::try_from(bits_u64)
        .map_err(|_| CryptoError::InvalidInput("n^2 bit length too large"))?;
    if bits < 3 {
        return Err(CryptoError::InvalidInput("n^2 too small to derive B"));
    }
    Ok(bits - 2)
}

/// 采样指定 bit 长度的奇数，最高位强制为 1。
fn random_odd_with_bits<R: RngCore>(rng: &mut R, bits: usize) -> CryptoResult<BigUint> {
    if bits < 2 {
        return Err(CryptoError::InvalidInput("prime bits must be >= 2"));
    }
    let bits_u64 =
        u64::try_from(bits).map_err(|_| CryptoError::InvalidInput("bit size too large"))?;
    let mut x = rng.gen_biguint(bits_u64);
    let one = BigUint::one();
    x |= &one << (bits - 1);
    x |= one;
    Ok(x)
}

/// Miller-Rabin 概率素性测试。
///
/// rounds 越大，误判合数为素数的概率越低。
/// 该函数用于安全素数搜索中的候选过滤。
fn is_probable_prime<R: RngCore>(n: &BigUint, rounds: usize, rng: &mut R) -> bool {
    let two = BigUint::from(2u32);
    let three = BigUint::from(3u32);
    if *n < two {
        return false;
    }
    if *n == two || *n == three {
        return true;
    }
    if (n % &two).is_zero() {
        return false;
    }

    let one = BigUint::one();
    let n_minus_one = n - &one;
    let mut d = n_minus_one.clone();
    let mut s = 0usize;
    while (&d % &two).is_zero() {
        d >>= 1usize;
        s += 1;
    }

    for _ in 0..rounds {
        let a = rng.gen_biguint_range(&two, &(n - &two));
        let mut x = a.modpow(&d, n);
        if x == one || x == n_minus_one {
            continue;
        }

        let mut witness_loop_ok = false;
        for _ in 1..s {
            x = x.modpow(&two, n);
            if x == n_minus_one {
                witness_loop_ok = true;
                break;
            }
        }

        if !witness_loop_ok {
            return false;
        }
    }
    true
}

/// 生成安全素数 p = 2p' + 1，其中 p' 也是素数。
fn generate_safe_prime<R: RngCore>(rng: &mut R, bits: usize) -> CryptoResult<BigUint> {
    let one = BigUint::one();
    let two = BigUint::from(2u32);

    for _ in 0..10_000 {
        let p_prime = random_odd_with_bits(rng, bits - 1)?;
        if !is_probable_prime(&p_prime, 32, rng) {
            continue;
        }
        let p = &two * &p_prime + &one;
        if is_probable_prime(&p, 32, rng) {
            return Ok(p);
        }
    }
    Err(CryptoError::PrimeGenerationFailed)
}

/// 生成安全 RSA 模数 n = pq，其中 p, q 均为安全素数。
///
/// 返回 (p, q, n)。
pub fn generate_safe_rsa_modulus(bits: usize) -> CryptoResult<(BigUint, BigUint, BigUint)> {
    if bits < 32 || bits % 2 != 0 {
        return Err(CryptoError::InvalidInput("RSA bits must be even and >= 32"));
    }
    let mut rng = OsRng;
    let half = bits / 2;
    let p = generate_safe_prime(&mut rng, half)?;
    let mut q = generate_safe_prime(&mut rng, half)?;
    let mut tries = 0usize;

    while p == q {
        q = generate_safe_prime(&mut rng, half)?;
        tries += 1;
        if tries > 64 {
            return Err(CryptoError::PrimeGenerationFailed);
        }
    }
    let n = &p * &q;
    Ok((p, q, n))
}

/// 在 Z*_{n^2} 中采样一个单位元。
///
/// 通过拒绝采样保证 gcd(x, n^2) = 1。
pub fn sample_unit_mod_n2<R: RngCore>(rng: &mut R, n2: &BigUint) -> BigUint {
    let one = BigUint::one();
    loop {
        let x = rng.gen_biguint_below(n2);
        if x > one && gcd(x.clone(), n2.clone()) == one {
            return x;
        }
    }
}

/// 在 |QR_{n^2}| 中采样元素。
///
/// 过程：先取单位元 x，再计算 x^2 mod n^2 落入 QR_{n^2}，
/// 最后映射到绝对值代表元。
pub fn sample_abs_qr_element<R: RngCore>(rng: &mut R, n2: &BigUint) -> BigUint {
    let x = sample_unit_mod_n2(rng, n2);
    let y = x.modpow(&BigUint::from(2u32), n2);
    abs_qr_rep(&y, n2)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abs_qr_rep() {
        let n2 = BigUint::from(100u32);
        let x1 = BigUint::from(30u32);
        let x2 = BigUint::from(80u32);
        assert_eq!(abs_qr_rep(&x1, &n2), BigUint::from(30u32));
        assert_eq!(abs_qr_rep(&x2, &n2), BigUint::from(20u32));
    }

    #[test]
    fn test_modinv_small() {
        let inv =
            modinv(&BigUint::from(3u32), &BigUint::from(11u32)).expect("inverse should exist");
        assert_eq!(inv, BigUint::from(4u32));
    }
}
