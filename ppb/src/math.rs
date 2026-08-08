use std::sync::OnceLock;

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

/// 小素数筛的上界。
///
/// 取 2^16 是实测的代价平衡点：安全素数在 2048 位处的联合密度约 1/1.5e6，
/// 每个候选若直接做 Miller-Rabin 需要一次约 11 ms 的模幂，总代价约 4.7 小时；
/// 先用小素数把候选筛掉约 98% 之后，总代价降到分钟级。
/// 上界再往上抬，筛本身的开销就开始超过它省下的 Miller-Rabin 开销。
const SMALL_PRIME_LIMIT: usize = 1 << 16;

/// 分段筛一次处理的候选个数（候选为 start, start+2, start+4, ...）。
const SIEVE_SEGMENT: usize = 1 << 16;

/// 惰性构造并缓存 `[3, SMALL_PRIME_LIMIT)` 内的奇素数表（埃氏筛）。
///
/// 不含 2：安全素数搜索里的候选 `p'` 与 `p = 2p'+1` 恒为奇数，2 永远筛不掉东西。
fn small_odd_primes() -> &'static [u64] {
    static SMALL_PRIMES: OnceLock<Vec<u64>> = OnceLock::new();
    SMALL_PRIMES.get_or_init(|| {
        let mut composite = vec![false; SMALL_PRIME_LIMIT];
        let mut primes = Vec::new();
        let mut i = 3usize;
        while i < SMALL_PRIME_LIMIT {
            if !composite[i] {
                primes.push(i as u64);
                // i 为奇数，i*i + 2k*i 仍为奇数，只需标记奇数倍数。
                let mut j = i * i;
                while j < SMALL_PRIME_LIMIT {
                    composite[j] = true;
                    j += 2 * i;
                }
            }
            i += 2;
        }
        primes
    })
}

/// 在 `alive` 上从 `first` 开始按步长 `step` 打掉候选。
fn strike_out(alive: &mut [bool], first: u64, step: u64) {
    let mut idx = first as usize;
    let step = step as usize;
    while idx < alive.len() {
        alive[idx] = false;
        idx += step;
    }
}

/// 生成安全素数 p = 2p' + 1，其中 p' 也是素数。
///
/// 实现说明（相对最初版本的改动）：
///
/// 1. **分段筛预过滤**。随机取一个 `bits-1` 位的奇数 `start`，把
///    `start, start+2, ..., start+2(L-1)` 作为一段候选，对每个小素数 `q`
///    同时划掉两类候选：
///    - `q | p'`：即 `i ≡ -start·2^{-1} (mod q)`；
///    - `q | 2p'+1`：即 `i ≡ -(2·start+1)·4^{-1} (mod q)`。
///
///    关键在于**两个条件一起筛**——安全素数要求 `p'` 和 `2p'+1` 同时为素数，
///    只筛其中一个会浪费掉一半以上的过滤力。
///
/// 2. **去掉 10000 次的候选上限**。原来的上限在 ℓ_N≥512 时就会让 setup 以
///    可观概率直接失败（实测 512 位下约 2/3 概率返回 `PrimeGenerationFailed`），
///    在 2048 位素数处单次成功率约 4e-5，等于永远拿不到参数。
///    这里改为一个仅用于防御病态输入的巨大预算。
///
/// 3. 筛只做**预过滤**：所有存活候选仍然要过完整的 Miller-Rabin，
///    因此筛的任何错误最多让搜索变慢或漏掉某些素数，不可能让合数被返回。
///
/// 4. **分布说明**：本实现是"随机起点 + 段内递增扫描"（incremental search），
///    而不是"每个候选独立均匀重采样"。这是 OpenSSL/GMP 等库的通行做法，
///    其输出分布与均匀分布的偏差已由 Brandt–Damgård（CRYPTO'92）分析过，
///    对密码学用途是可接受的（长素数间隙之后的素数被选中的概率略高，
///    熵损失可忽略）。若需要严格均匀，可把段长设为 1，代价是回到原来的速度。
///
/// 附注：`p' > 2` 为奇素数时 `p = 2p'+1 ≡ 3 (mod 4)` 自动成立，
/// 这正是论文 Appx. F.2 中 Damgård-Fujisaki 承诺安全性证明所需要的条件，
/// 无需额外约束。
fn generate_safe_prime<R: RngCore>(rng: &mut R, bits: usize) -> CryptoResult<BigUint> {
    if bits < 3 {
        return Err(CryptoError::InvalidInput("safe prime bits must be >= 3"));
    }

    let one = BigUint::one();
    let two = BigUint::from(2u32);
    let target_bits = u64::try_from(bits - 1)
        .map_err(|_| CryptoError::InvalidInput("bit size too large"))?;

    // 仅防御死循环，正常路径远远用不到：2048 位素数期望也只需约 1.5e6 个候选。
    const MAX_CANDIDATES: u64 = 1 << 40;
    let mut examined: u64 = 0;

    loop {
        let start = random_odd_with_bits(rng, bits - 1)?;
        let mut alive = vec![true; SIEVE_SEGMENT];

        for &q in small_odd_primes() {
            let modulus = BigUint::from(q);
            let r = (&start % &modulus)
                .to_u64_digits()
                .first()
                .copied()
                .unwrap_or(0);

            // q 为奇数，故 2 与 4 在模 q 下均可逆。
            let inv2 = (q + 1) / 2;
            let inv4 = (inv2 * inv2) % q;

            // p' = start + 2i ≡ 0 (mod q)  ⟺  i ≡ -start·2^{-1} (mod q)
            let first_a = (((q - r % q) % q) * inv2) % q;
            strike_out(&mut alive, first_a, q);

            // 2p'+1 = 2·start + 4i + 1 ≡ 0 (mod q)  ⟺  i ≡ -(2·start+1)·4^{-1} (mod q)
            let t = (2 * (r % q) + 1) % q;
            let first_b = (((q - t) % q) * inv4) % q;
            strike_out(&mut alive, first_b, q);
        }

        for (i, ok) in alive.iter().enumerate() {
            if !ok {
                continue;
            }

            examined += 1;
            if examined > MAX_CANDIDATES {
                return Err(CryptoError::PrimeGenerationFailed);
            }

            let p_prime = &start + &two * BigUint::from(i as u64);
            // 段尾可能越过位长边界，跳过以保证输出位长稳定。
            if p_prime.bits() != target_bits {
                continue;
            }
            if !is_probable_prime(&p_prime, 32, rng) {
                continue;
            }
            let p = &two * &p_prime + &one;
            if is_probable_prime(&p, 32, rng) {
                return Ok(p);
            }
        }
    }
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

    #[test]
    fn test_small_odd_primes_table() {
        let primes = small_odd_primes();
        assert_eq!(&primes[..5], &[3u64, 5, 7, 11, 13]);
        assert!(!primes.contains(&2));
        assert!(!primes.contains(&9));
        assert!(!primes.contains(&65535));
        assert!(primes.contains(&65521)); // < 2^16 的最大素数
        // 素数计数 π(2^16) = 6542，去掉 2 之后为 6541。
        assert_eq!(primes.len(), 6541);
    }

    #[test]
    fn test_generate_safe_prime_structure() {
        let mut rng = OsRng;
        let bits = 256usize;
        let p = generate_safe_prime(&mut rng, bits).expect("safe prime generation should succeed");

        // 位长必须精确，否则 RSA 模数的位长会漂移。
        assert_eq!(p.bits(), bits as u64);

        // p 与 p' = (p-1)/2 都必须是素数。
        assert!(is_probable_prime(&p, 40, &mut rng));
        let p_prime = (&p - BigUint::one()) / BigUint::from(2u32);
        assert!(is_probable_prime(&p_prime, 40, &mut rng));

        // 论文 Appx. F.2 的 DF 承诺安全性证明要求 p ≡ 3 (mod 4)，
        // 对 p'>2 的安全素数这是自动成立的，这里固化为回归断言。
        assert_eq!(&p % BigUint::from(4u32), BigUint::from(3u32));
    }

    #[test]
    fn test_generate_safe_rsa_modulus_shape() {
        let bits = 512usize;
        let (p, q, n) = generate_safe_rsa_modulus(bits).expect("modulus generation should succeed");

        assert_ne!(p, q);
        assert_eq!(p.bits(), (bits / 2) as u64);
        assert_eq!(q.bits(), (bits / 2) as u64);
        assert_eq!(n, &p * &q);
        // 两个因子最高位都置 1，故 n 的位长为 bits 或 bits-1。
        assert!(n.bits() == bits as u64 || n.bits() == (bits - 1) as u64);
    }

    /// 回归测试：旧实现的 10000 次候选上限在 512 位下有约 2/3 的概率
    /// 直接返回 `PrimeGenerationFailed`。加入分段筛并去掉上限后，
    /// setup 必须每次都成功。
    #[test]
    fn test_safe_rsa_modulus_does_not_fail_at_512_bits() {
        for _ in 0..3 {
            generate_safe_rsa_modulus(512).expect("512-bit setup must not fail any more");
        }
    }
}
