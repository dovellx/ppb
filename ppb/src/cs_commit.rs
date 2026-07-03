use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;
use rand::RngCore;

use crate::cs::CsCiphertext;
use crate::df::DfParams;
use crate::error::{CryptoError, CryptoResult};
use crate::hash::fiat_shamir_challenge_biguints;
use crate::math::{derive_b_bits_from_n2, gcd, modinv, sample_abs_qr_element};

/// 针对 CS 密文承诺层的公共参数。
///
/// 对应伪代码：
/// SetupCS(1^lambda, paramsCS, paramsDF) -> params
///
/// 字段语义：
/// 1. n2: 群/环模数 n^2（所有乘法和幂运算都在该模下进行）
/// 2. g: 新采样的 |QR_{n^2}| 元素（用于隐藏密文分量）
/// 3. g_star: 来自 CS 参数的 g*（即原加密参数中的基）
/// 4. h_star: 来自 CS 参数的 h*（即原加密参数中的 1+n）
/// 5. g_prime, h_prime: 来自 DF 参数的两个生成元
/// 6. lambda_bits: 安全参数 lambda（以 bit 表示）
///
/// 说明：
/// 为了与现有 DF/QR 实现保持一致，本模块不在参数中固化 B 或 B+lambda，
/// 而是在 Commit 阶段由调用方显式传入 randomness_bits。
#[derive(Debug, Clone)]
pub struct CsCommitParams {
    pub n: BigUint,
    pub n2: BigUint,
    pub g: BigUint,
    pub g_star: BigUint,
    pub h_star: BigUint,
    pub g_prime: BigUint,
    pub h_prime: BigUint,
    pub lambda_bits: usize,
}

/// CS 密文承诺值 C = (C1, C2, C3, C4)。
#[derive(Debug, Clone)]
pub struct CsCommitment {
    pub c1: BigUint,
    pub c2: BigUint,
    pub c3: BigUint,
    pub c4: BigUint,
}

/// CS 密文承诺开口 O = (a1, a2, s1, s2, r1, r2, b1, b2)。
///
/// 其中 a1, a2, b1, b2 仅取 {-1, +1}。
#[derive(Debug, Clone)]
pub struct CsCommitOpening {
    pub a1: i8,
    pub a2: i8,
    pub s1: BigUint,
    pub s2: BigUint,
    pub r1: BigUint,
    pub r2: BigUint,
    pub b1: i8,
    pub b2: i8,
}

/// 最终返回的承诺对 (C, O)。
#[derive(Debug, Clone)]
pub struct CsCommitmentWithOpening {
    pub commitment: CsCommitment,
    pub opening: CsCommitOpening,
}

/// ProveComCS 输出证明 π。
///
/// 与题面保持一致：
/// π = (R2, R4, z_s1, z_r1, z_s2, z_r2)
#[derive(Debug, Clone)]
pub struct CsComProof {
    pub r2: BigUint,
    pub r4: BigUint,
    pub z_s1: BigUint,
    pub z_r1: BigUint,
    pub z_s2: BigUint,
    pub z_r2: BigUint,
}

/// ProveAddCS 输出的极简证明 π = (e, z1, z2, z3, z4)。
///
/// 其中 z1..z4 在整数域 Z 中，允许为负数。
#[derive(Debug, Clone)]
pub struct CsAddProof {
    pub e: BigUint,
    pub z1: BigInt,
    pub z2: BigInt,
    pub z3: BigInt,
    pub z4: BigInt,
}

/// ProveMultCS 输出证明。
///
/// 对应题面给出的标准格式：
/// pi = (R_y, R_1, R_2, R_3, R_4, z_y, z_ry, z_1, z_2, z_3, z_4)
#[derive(Debug, Clone)]
pub struct CsMultProof {
    pub r_y: BigUint,
    pub r1: BigUint,
    pub r2: BigUint,
    pub r3: BigUint,
    pub r4: BigUint,
    pub z_y: BigInt,
    pub z_ry: BigInt,
    pub z1: BigInt,
    pub z2: BigInt,
    pub z3: BigInt,
    pub z4: BigInt,
}

/// ProveEncCS 输出证明。
///
/// pi = (R_y, R_1, R_2, R_3, R_4, z_y, z_ry, z_ra, z_s1, z_r1, z_s2, z_r2)
#[derive(Debug, Clone)]
pub struct CsEncProof {
    pub r_y: BigUint,
    pub r1: BigUint,
    pub r2: BigUint,
    pub r3: BigUint,
    pub r4: BigUint,
    pub z_y: BigInt,
    pub z_ry: BigInt,
    pub z_ra: BigInt,
    pub z_s1: BigInt,
    pub z_r1: BigInt,
    pub z_s2: BigInt,
    pub z_r2: BigInt,
}

/// 将符号位 sign（-1 或 +1）乘到模 n^2 的元素 x 上。
///
/// 数学上：
/// sign = +1 => x
/// sign = -1 => (-x) mod n^2
fn apply_sign_mod_n2(x: &BigUint, sign: i8, n2: &BigUint) -> CryptoResult<BigUint> {
    match sign {
        1 => Ok(x % n2),
        -1 => {
            if x.is_zero() {
                Ok(BigUint::zero())
            } else {
                Ok((n2 - (x % n2)) % n2)
            }
        }
        _ => Err(CryptoError::InvalidInput("sign must be -1 or +1")),
    }
}

/// 在 {-1, +1} 中均匀采样符号。
fn sample_sign() -> i8 {
    let mut rng = OsRng;
    if (rng.next_u32() & 1) == 0 {
        -1
    } else {
        1
    }
}

/// 统一的 Fiat-Shamir 挑战构造器。
///
/// 重构说明：
/// 1. 具体编码细节（长度前缀）与哈希计算已经下沉到 `hash.rs`；
/// 2. 这里保留一个本地包装器，只负责协议字段顺序编排，
///    让每个证明函数仍可读出“挑战由哪些字段构成”；
/// 3. 这样可以在不改协议逻辑的前提下，避免多个模块复制同一段编码代码。
fn fs_challenge_from_biguints(values: &[&BigUint]) -> BigUint {
    fiat_shamir_challenge_biguints(values)
}

/// 统一推导盲化采样位长：B + 2lambda + lambda_c。
///
/// - 当 lambda_c = 0 时，对应 B + 2lambda；
/// - 当 lambda_c > 0 时，对应扩展盲化区间（例如 mult/enc 里的 +lambda_c）。
fn derive_blinding_bits(params: &CsCommitParams, lambda_c: usize) -> CryptoResult<usize> {
    let b_bits = derive_b_bits_from_n2(&params.n2)?;
    b_bits
        .checked_add(
            params
                .lambda_bits
                .checked_mul(2)
                .ok_or(CryptoError::InvalidInput("2*lambda overflow"))?,
        )
        .and_then(|v| v.checked_add(lambda_c))
        .ok_or(CryptoError::InvalidInput("B+2lambda+lambda_c overflow"))
}

/// 计算 ProveComCS 的 Fiat-Shamir 挑战：
/// e <- Hash(n, g', h', C2, C4, R2, R4)
fn fs_challenge_for_cs_com(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    r2: &BigUint,
    r4: &BigUint,
) -> BigUint {
    fs_challenge_from_biguints(&[
        &params.n,
        &params.g_prime,
        &params.h_prime,
        &commitment.c2,
        &commitment.c4,
        r2,
        r4,
    ])
}

/// 计算 ProveAddCS/VerifyAddCS 的 Fiat-Shamir 挑战：
/// e <- Hash(n, g, g', h', D1, D2, D3, D4, R'_1, R'_2, R'_3, R'_4)
fn fs_challenge_for_cs_add(
    params: &CsCommitParams,
    d1: &BigUint,
    d2: &BigUint,
    d3: &BigUint,
    d4: &BigUint,
    rp1: &BigUint,
    rp2: &BigUint,
    rp3: &BigUint,
    rp4: &BigUint,
) -> BigUint {
    fs_challenge_from_biguints(&[
        &params.n,
        &params.g,
        &params.g_prime,
        &params.h_prime,
        d1,
        d2,
        d3,
        d4,
        rp1,
        rp2,
        rp3,
        rp4,
    ])
}

/// 计算 ProveMultCS/VerifyMultCS 的 Fiat-Shamir 挑战：
/// e <- Hash(params, C_a, C_b, C_y, R_y, R_1, R_2, R_3, R_4)
fn fs_challenge_for_cs_mult(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cy: &BigUint,
    r_y: &BigUint,
    r1: &BigUint,
    r2: &BigUint,
    r3: &BigUint,
    r4: &BigUint,
) -> BigUint {
    fs_challenge_from_biguints(&[
        &params.n,
        &params.g,
        &params.g_prime,
        &params.h_prime,
        &ca.c1,
        &ca.c2,
        &ca.c3,
        &ca.c4,
        &cb.c1,
        &cb.c2,
        &cb.c3,
        &cb.c4,
        cy,
        r_y,
        r1,
        r2,
        r3,
        r4,
    ])
}

/// 计算 ProveEncCS/VerifyEncCS 的 Fiat-Shamir 挑战：
/// e <- Hash(params, k, C_a, C_y, R_y, R_1, R_2, R_3, R_4)
fn fs_challenge_for_cs_enc(
    params: &CsCommitParams,
    k: &BigUint,
    ca: &CsCommitment,
    cy: &BigUint,
    r_y: &BigUint,
    r1: &BigUint,
    r2: &BigUint,
    r3: &BigUint,
    r4: &BigUint,
) -> BigUint {
    fs_challenge_from_biguints(&[
        &params.n,
        &params.g_star,
        &params.g_prime,
        &params.h_prime,
        k,
        &ca.c1,
        &ca.c2,
        &ca.c3,
        &ca.c4,
        cy,
        r_y,
        r1,
        r2,
        r3,
        r4,
    ])
}

/// 将 BigUint 转换为 BigInt，统一处理转换失败错误。
fn bu_to_bi(v: &BigUint) -> CryptoResult<BigInt> {
    v.to_bigint()
        .ok_or(CryptoError::InvalidInput("BigUint->BigInt conversion failed"))
}

/// 检查符号是否属于 {-1, +1}。
fn is_pm_one(sign: i8) -> bool {
    matches!(sign, -1 | 1)
}

/// 三个符号相乘（都必须是 {-1,+1}），输出仍为 {-1,+1}。
fn mul_three_signs(a: i8, b: i8, c: i8) -> CryptoResult<i8> {
    if !is_pm_one(a) || !is_pm_one(b) || !is_pm_one(c) {
        return Err(CryptoError::InvalidInput("sign must be in {-1,+1}"));
    }
    let prod = i16::from(a) * i16::from(b) * i16::from(c);
    match prod {
        -1 => Ok(-1),
        1 => Ok(1),
        _ => Err(CryptoError::InvalidInput("invalid sign multiplication result")),
    }
}

/// 两个符号相除（在 {-1,+1} 上），等价于相乘。
fn div_two_signs(a: i8, b: i8) -> CryptoResult<i8> {
    mul_three_signs(a, b, 1)
}

/// 计算 sign^exp（sign in {-1,+1}, exp in Z）。
///
/// 在 {-1,+1} 群上：
/// 1. 指数奇偶即可决定结果；
/// 2. 负指数与正指数在该群上等价（因为 sign^{-1} = sign）。
fn sign_pow_i8(sign: i8, exp: &BigInt) -> CryptoResult<i8> {
    if !is_pm_one(sign) {
        return Err(CryptoError::InvalidInput("sign must be in {-1,+1}"));
    }

    let is_even = (exp % BigInt::from(2u32)) == BigInt::zero();
    if is_even {
        Ok(1)
    } else {
        Ok(sign)
    }
}

/// 将符号位映射为模 n^2 的元素：+1 -> 1, -1 -> n^2-1。
fn sign_to_mod_element(sign: i8, n2: &BigUint) -> CryptoResult<BigUint> {
    apply_sign_mod_n2(&BigUint::one(), sign, n2)
}

/// 在模 n^2 下做除法：num / den := num * den^{-1} mod n^2。
fn div_mod_n2(num: &BigUint, den: &BigUint, n2: &BigUint) -> CryptoResult<BigUint> {
    let den_mod = den % n2;
    let den_inv = modinv(&den_mod, n2)?;
    Ok(((num % n2) * den_inv) % n2)
}

/// 有符号指数模幂：base^exp mod modulus。
///
/// 当 exp < 0 时，使用 base^{-1} 的正指数幂。
fn modpow_signed(base: &BigUint, exp: &BigInt, modulus: &BigUint) -> CryptoResult<BigUint> {
    if exp >= &BigInt::zero() {
        let exp_u = exp
            .to_biguint()
            .ok_or(CryptoError::InvalidInput("non-negative exponent conversion failed"))?;
        return Ok(base.modpow(&exp_u, modulus));
    }

    let inv = modinv(base, modulus)?;
    let abs_exp = (-exp)
        .to_biguint()
        .ok_or(CryptoError::InvalidInput("negative exponent abs conversion failed"))?;
    Ok(inv.modpow(&abs_exp, modulus))
}

/// 在对称区间 [-2^ell, 2^ell] 中均匀采样一个整数。
fn sample_symmetric_bigint(rng: &mut OsRng, ell: usize) -> CryptoResult<BigInt> {
    let ell_u64 = u64::try_from(ell).map_err(|_| CryptoError::InvalidInput("ell too large"))?;
    let two_pow_ell = BigUint::one() << ell;
    let upper_inclusive = (BigUint::one() << (ell_u64 + 1)) + BigUint::one();
    let t = rng.gen_biguint_below(&upper_inclusive);
    Ok(BigInt::from(t) - BigInt::from(two_pow_ell))
}

/// 从三个承诺计算 D_i = Cc_i / (Ca_i * Cb_i) (mod n^2)。
fn compute_add_relation_d(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cc: &CsCommitment,
) -> CryptoResult<(BigUint, BigUint, BigUint, BigUint)> {
    let den1 = (&ca.c1 * &cb.c1) % &params.n2;
    let den2 = (&ca.c2 * &cb.c2) % &params.n2;
    let den3 = (&ca.c3 * &cb.c3) % &params.n2;
    let den4 = (&ca.c4 * &cb.c4) % &params.n2;

    let d1 = div_mod_n2(&cc.c1, &den1, &params.n2)?;
    let d2 = div_mod_n2(&cc.c2, &den2, &params.n2)?;
    let d3 = div_mod_n2(&cc.c3, &den3, &params.n2)?;
    let d4 = div_mod_n2(&cc.c4, &den4, &params.n2)?;
    Ok((d1, d2, d3, d4))
}

/// SetupCS(1^lambda, paramsCS, paramsDF) -> params
///
/// 输入：
/// 1. lambda_bits: 安全参数 lambda（位长）
/// 2. params_cs: 取自 CS 原语参数（应至少包含 n^2, g*, h*）
/// 3. params_df: 取自 DF 原语参数（应至少包含 n^2, g', h'）
///
/// 输出：
/// params = (G, g, g*, h*, g', h') 的工程结构化表达。
///
/// 注意：
/// 1. 本实现会检查 CS 与 DF 的 n^2 一致性；
/// 2. 为与 DF/QR 模块一致，随机数位长在 Commit 阶段由外部传入。
pub fn setup_cs_commit(
    lambda_bits: usize,
    params_cs: &crate::cs::CsParams,
    params_df: &DfParams,
) -> CryptoResult<CsCommitParams> {
    if lambda_bits == 0 {
        return Err(CryptoError::InvalidInput("lambda_bits must be > 0"));
    }
    if params_cs.n2 != params_df.n2 {
        return Err(CryptoError::InvalidInput("paramsCS.n2 must equal paramsDF.n2"));
    }
    if params_cs.n != params_df.n {
        return Err(CryptoError::InvalidInput("paramsCS.n must equal paramsDF.n"));
    }

    let n = params_cs.n.clone();
    let n2 = params_cs.n2.clone();
    let mut rng = OsRng;
    let g = sample_abs_qr_element(&mut rng, &n2);

    Ok(CsCommitParams {
        n,
        n2,
        g,
        g_star: params_cs.g.clone(),
        h_star: params_cs.h.clone(),
        g_prime: params_df.g.clone(),
        h_prime: params_df.h.clone(),
        lambda_bits,
    })
}

/// CommitCS(params, c) -> (C, O)
///
/// 对应伪代码：
/// 1. parse c = (c1, c2)
/// 2. s1, s2 <-$ [2B+lambda]; r1, r2 <-$ [2B+lambda]
/// 3. a1, a2, b1, b2 <-$ {-1, +1}
/// 4. C1 <- a1 * c1 * g^s1
/// 5. C2 <- b1 * (g')^s1 * (h')^r1
/// 6. C3 <- a2 * c2 * g^s2
/// 7. C4 <- b2 * (g')^s2 * (h')^r2
/// 8. 输出 C=(C1,C2,C3,C4), O=(a1,a2,s1,s2,r1,r2,b1,b2)
///
/// 重要实现说明：
/// 1. 上述所有乘法都在 Z_{n^2} 下进行；
/// 2. 符号位通过 (-x mod n^2) 实现，不直接使用有符号大整数；
/// 3. 入参密文采用现有 CsCiphertext 结构，映射关系为：
///    伪代码 c1 对应 c.c0，伪代码 c2 对应 c.c1。
/// 4. randomness_bits 与 DF/QR 中同名参数语义一致：
///    r <- [0, 2^{randomness_bits})，上层可将其设为 B+lambda 或 2B+lambda。
pub fn commit_cs(
    params: &CsCommitParams,
    c: &CsCiphertext,
    randomness_bits: usize,
) -> CryptoResult<CsCommitmentWithOpening> {
    if randomness_bits == 0 {
        return Err(CryptoError::InvalidInput("randomness bits must be > 0"));
    }
    let bits_u64 = u64::try_from(randomness_bits)
        .map_err(|_| CryptoError::InvalidInput("randomness bits too large"))?;
    let mut rng = OsRng;

    let s1 = rng.gen_biguint(bits_u64);
    let s2 = rng.gen_biguint(bits_u64);
    let r1 = rng.gen_biguint(bits_u64);
    let r2 = rng.gen_biguint(bits_u64);

    let a1 = sample_sign();
    let a2 = sample_sign();
    let b1 = sample_sign();
    let b2 = sample_sign();

    let gs1 = params.g.modpow(&s1, &params.n2);
    let gs2 = params.g.modpow(&s2, &params.n2);
    let gp_s1 = params.g_prime.modpow(&s1, &params.n2);
    let gp_s2 = params.g_prime.modpow(&s2, &params.n2);
    let hp_r1 = params.h_prime.modpow(&r1, &params.n2);
    let hp_r2 = params.h_prime.modpow(&r2, &params.n2);

    let c1_unsigned = (&c.c0 * gs1) % &params.n2;
    let c2_unsigned = (gp_s1 * hp_r1) % &params.n2;
    let c3_unsigned = (&c.c1 * gs2) % &params.n2;
    let c4_unsigned = (gp_s2 * hp_r2) % &params.n2;

    let c1 = apply_sign_mod_n2(&c1_unsigned, a1, &params.n2)?;
    let c2 = apply_sign_mod_n2(&c2_unsigned, b1, &params.n2)?;
    let c3 = apply_sign_mod_n2(&c3_unsigned, a2, &params.n2)?;
    let c4 = apply_sign_mod_n2(&c4_unsigned, b2, &params.n2)?;

    Ok(CsCommitmentWithOpening {
        commitment: CsCommitment { c1, c2, c3, c4 },
        opening: CsCommitOpening {
            a1,
            a2,
            s1,
            s2,
            r1,
            r2,
            b1,
            b2,
        },
    })
}

/// 预留接口：证明 CS 加法关系。
///
/// 对应算法：
/// ProveAddCS(params, Ca, Cb, Cc, [a,b,c,Oa,Ob,Oc]) -> pi
///
/// 本实现遵循你给出的 NIZK 细节：
/// 1. 盲化值在对称区间 [-2^ell, 2^ell] 采样，ell = B + 2lambda；
/// 2. 挑战哈希使用 R_i 的平方 R'_i；
/// 3. 响应使用减法 z_i = k_i - e * gamma_i（在整数域 Z 中，不取模）；
/// 4. 输出极简证明 pi = (e, z1, z2, z3, z4)。
pub fn prove_cs_add(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cc: &CsCommitment,
    oa: &CsCommitOpening,
    ob: &CsCommitOpening,
    oc: &CsCommitOpening,
) -> CryptoResult<CsAddProof> {
    // 所有符号位必须是 ±1。
    let all_signs = [oa.a1, oa.a2, oa.b1, oa.b2, ob.a1, ob.a2, ob.b1, ob.b2, oc.a1, oc.a2, oc.b1, oc.b2];
    if !all_signs.into_iter().all(is_pm_one) {
        return Err(CryptoError::InvalidInput("all signs in openings must be in {-1,+1}"));
    }

    // 计算 D_i = Cc_i / (Ca_i * Cb_i)。
    let (d1, d2, d3, d4) = compute_add_relation_d(params, ca, cb, cc)?;

    // 计算 gamma_i（整数域，允许负数）。
    let gamma1 = bu_to_bi(&oc.s1)? - bu_to_bi(&oa.s1)? - bu_to_bi(&ob.s1)?;
    let gamma2 = bu_to_bi(&oc.r1)? - bu_to_bi(&oa.r1)? - bu_to_bi(&ob.r1)?;
    let gamma3 = bu_to_bi(&oc.s2)? - bu_to_bi(&oa.s2)? - bu_to_bi(&ob.s2)?;
    let gamma4 = bu_to_bi(&oc.r2)? - bu_to_bi(&oa.r2)? - bu_to_bi(&ob.r2)?;

    // 计算 beta_i。由于 ±1 的逆元等于自身，ac/(aa*ab) 等价于 ac*aa*ab。
    let beta1 = mul_three_signs(oc.a1, oa.a1, ob.a1)?;
    let beta2 = mul_three_signs(oc.b1, oa.b1, ob.b1)?;
    let beta3 = mul_three_signs(oc.a2, oa.a2, ob.a2)?;
    let beta4 = mul_three_signs(oc.b2, oa.b2, ob.b2)?;

    // 在进入 NIZK 前先检查见证是否真的满足四条关系。
    let d1_expected = (sign_to_mod_element(beta1, &params.n2)? * modpow_signed(&params.g, &gamma1, &params.n2)?)
        % &params.n2;
    if d1_expected != d1 {
        return Err(CryptoError::InvalidInput("witness does not satisfy D1 relation"));
    }

    let d2_expected = (
        sign_to_mod_element(beta2, &params.n2)?
            * modpow_signed(&params.g_prime, &gamma1, &params.n2)?
            * modpow_signed(&params.h_prime, &gamma2, &params.n2)?
    ) % &params.n2;
    if d2_expected != d2 {
        return Err(CryptoError::InvalidInput("witness does not satisfy D2 relation"));
    }

    let d3_expected = (sign_to_mod_element(beta3, &params.n2)? * modpow_signed(&params.g, &gamma3, &params.n2)?)
        % &params.n2;
    if d3_expected != d3 {
        return Err(CryptoError::InvalidInput("witness does not satisfy D3 relation"));
    }

    let d4_expected = (
        sign_to_mod_element(beta4, &params.n2)?
            * modpow_signed(&params.g_prime, &gamma3, &params.n2)?
            * modpow_signed(&params.h_prime, &gamma4, &params.n2)?
    ) % &params.n2;
    if d4_expected != d4 {
        return Err(CryptoError::InvalidInput("witness does not satisfy D4 relation"));
    }

    // ell = B + 2lambda。
    // 盲化必须覆盖 256 位 Fiat-Shamir 挑战 e：否则 z = k - e·γ 的高位直接泄露 γ，
    // 击穿零知识/统计隐藏。取 B + 2λ + 256（与 mult/enc 一致）。
    let ell = derive_blinding_bits(params, 256)?;

    // 1) 盲化阶段：在对称区间采样 k_i，并计算 R_i。
    let mut rng = OsRng;
    let k1 = sample_symmetric_bigint(&mut rng, ell)?;
    let k2 = sample_symmetric_bigint(&mut rng, ell)?;
    let k3 = sample_symmetric_bigint(&mut rng, ell)?;
    let k4 = sample_symmetric_bigint(&mut rng, ell)?;

    let r1 = modpow_signed(&params.g, &k1, &params.n2)?;
    let r2 = (modpow_signed(&params.g_prime, &k1, &params.n2)?
        * modpow_signed(&params.h_prime, &k2, &params.n2)?)
        % &params.n2;
    let r3 = modpow_signed(&params.g, &k3, &params.n2)?;
    let r4 = (modpow_signed(&params.g_prime, &k3, &params.n2)?
        * modpow_signed(&params.h_prime, &k4, &params.n2)?)
        % &params.n2;

    // 2) 挑战阶段：对 R_i 的平方进行哈希。
    let two = BigUint::from(2u32);
    let rp1 = r1.modpow(&two, &params.n2);
    let rp2 = r2.modpow(&two, &params.n2);
    let rp3 = r3.modpow(&two, &params.n2);
    let rp4 = r4.modpow(&two, &params.n2);
    let e = fs_challenge_for_cs_add(params, &d1, &d2, &d3, &d4, &rp1, &rp2, &rp3, &rp4);

    // 3) 响应阶段：z_i = k_i - e*gamma_i，整数域计算，不取模。
    let e_bi = bu_to_bi(&e)?;
    let z1 = &k1 - (&e_bi * &gamma1);
    let z2 = &k2 - (&e_bi * &gamma2);
    let z3 = &k3 - (&e_bi * &gamma3);
    let z4 = &k4 - (&e_bi * &gamma4);

    Ok(CsAddProof { e, z1, z2, z3, z4 })
}

/// VerifyAddCS(params, Ca, Cb, Cc, pi) -> {0,1}
///
/// 验证流程：
/// 1. 由 (Ca,Cb,Cc) 计算 D1..D4；
/// 2. 用 proof 中 (e,z1..z4) 重构 R'_1..R'_4；
/// 3. 计算 e' = Hash(n, g, g', h', D1, D2, D3, D4, R'_1, R'_2, R'_3, R'_4)；
/// 4. 检查 e == e'。
pub fn verify_cs_add(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cc: &CsCommitment,
    proof: &CsAddProof,
) -> CryptoResult<bool> {
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let (d1, d2, d3, d4) = compute_add_relation_d(params, ca, cb, cc)?;
    let two = BigUint::from(2u32);
    let two_e = &two * &proof.e;

    let two_bi = BigInt::from(2u32);
    let two_z1 = &proof.z1 * &two_bi;
    let two_z2 = &proof.z2 * &two_bi;
    let two_z3 = &proof.z3 * &two_bi;
    let two_z4 = &proof.z4 * &two_bi;

    // 根据验证公式重构 R'_i。
    let rp1 = (modpow_signed(&params.g, &two_z1, &params.n2)? * d1.modpow(&two_e, &params.n2)) % &params.n2;
    let rp2 = (
        modpow_signed(&params.g_prime, &two_z1, &params.n2)?
            * modpow_signed(&params.h_prime, &two_z2, &params.n2)?
            * d2.modpow(&two_e, &params.n2)
    ) % &params.n2;
    let rp3 = (modpow_signed(&params.g, &two_z3, &params.n2)? * d3.modpow(&two_e, &params.n2)) % &params.n2;
    let rp4 = (
        modpow_signed(&params.g_prime, &two_z3, &params.n2)?
            * modpow_signed(&params.h_prime, &two_z4, &params.n2)?
            * d4.modpow(&two_e, &params.n2)
    ) % &params.n2;

    let e_prime = fs_challenge_for_cs_add(params, &d1, &d2, &d3, &d4, &rp1, &rp2, &rp3, &rp4);
    Ok(proof.e == e_prime)
}

/// 预留接口：证明 CS 承诺关系。
///
/// 算法目标：
/// 证明知道开口 O=(a1,a2,s1,s2,r1,r2,b1,b2)，使得：
/// C2 = b1 * (g')^s1 * (h')^r1,  b1 in {-1,+1}
/// C4 = b2 * (g')^s2 * (h')^r2,  b2 in {-1,+1}
///
/// 这里实现题面给出的 NIZK 三阶段：
/// 1. Commit: 采样 k_{s1},k_{r1},k_{s2},k_{r2} 并计算 R2,R4
/// 2. Challenge: e <- Hash(n, g', h', C2, C4, R2, R4)
/// 3. Response: z = k + e * witness（在整数域直接加法，不取模）
///
/// 注意：
/// 1. prove 函数会先检查 opening 是否与 commitment 一致，避免为无效实例出证明；
/// 2. 采样上界按 2^{B+2lambda} 实现，其中 B 由 n^2 位长近似推导；
/// 3. 返回证明不包含 b1,b2（与题面给出的 π 形式一致）。
pub fn prove_cs_com(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    opening: &CsCommitOpening,
) -> CryptoResult<CsComProof> {
    if !matches!(opening.b1, -1 | 1) || !matches!(opening.b2, -1 | 1) {
        return Err(CryptoError::InvalidInput("b1 and b2 must be in {-1, +1}"));
    }

    // 先验证见证与承诺一致，防止为错误语句输出“合法格式”证明。
    let c2_unsigned =
        (params.g_prime.modpow(&opening.s1, &params.n2) * params.h_prime.modpow(&opening.r1, &params.n2)) % &params.n2;
    let c2_expected = apply_sign_mod_n2(&c2_unsigned, opening.b1, &params.n2)?;
    if c2_expected != commitment.c2 {
        return Err(CryptoError::InvalidInput("opening does not satisfy C2 equation"));
    }

    let c4_unsigned =
        (params.g_prime.modpow(&opening.s2, &params.n2) * params.h_prime.modpow(&opening.r2, &params.n2)) % &params.n2;
    let c4_expected = apply_sign_mod_n2(&c4_unsigned, opening.b2, &params.n2)?;
    if c4_expected != commitment.c4 {
        return Err(CryptoError::InvalidInput("opening does not satisfy C4 equation"));
    }

    // 盲化必须覆盖 256 位 Fiat-Shamir 挑战 e：否则 z = k + e·w 的高位直接泄露开口 w，
    // 击穿零知识/统计隐藏。取 B + 2λ + 256（与 mult/enc 一致）。
    let blind_bits = derive_blinding_bits(params, 256)?;
    let blind_bits_u64 =
        u64::try_from(blind_bits).map_err(|_| CryptoError::InvalidInput("B+2lambda too large"))?;

    // 1) Commit 阶段：生成盲化随机数并计算 R2, R4。
    let mut rng = OsRng;
    let k_s1 = rng.gen_biguint(blind_bits_u64);
    let k_r1 = rng.gen_biguint(blind_bits_u64);
    let k_s2 = rng.gen_biguint(blind_bits_u64);
    let k_r2 = rng.gen_biguint(blind_bits_u64);

    let r2 = (params.g_prime.modpow(&k_s1, &params.n2) * params.h_prime.modpow(&k_r1, &params.n2)) % &params.n2;
    let r4 = (params.g_prime.modpow(&k_s2, &params.n2) * params.h_prime.modpow(&k_r2, &params.n2)) % &params.n2;

    // 2) Challenge 阶段：Fiat-Shamir 挑战。
    let e = fs_challenge_for_cs_com(params, commitment, &r2, &r4);

    // 3) Response 阶段：在整数域计算响应，不做模约简。
    let z_s1 = &k_s1 + (&e * &opening.s1);
    let z_r1 = &k_r1 + (&e * &opening.r1);
    let z_s2 = &k_s2 + (&e * &opening.s2);
    let z_r2 = &k_r2 + (&e * &opening.r2);

    Ok(CsComProof {
        r2,
        r4,
        z_s1,
        z_r1,
        z_s2,
        z_r2,
    })
}

/// VerifyComCS(params, C, pi) -> {0,1}
///
/// 验证算法严格对应你给出的伪代码：
/// 1. 重新计算挑战 e = Hash(n, g', h', C2, C4, R2, R4)
/// 2. 检查以下两条平方关系（平方用于消去隐藏符号 b1, b2）：
///
///    (g')^(2 z_s1) (h')^(2 z_r1) ?= R2^2 * C2^(2e) (mod n^2)
///    (g')^(2 z_s2) (h')^(2 z_r2) ?= R4^2 * C4^(2e) (mod n^2)
///
/// 3. 两个条件同时成立则接受，否则拒绝。
///
/// 返回：
/// - Ok(true): 证明通过
/// - Ok(false): 证明不通过
/// - Err(...): 输入不合法（例如模数为 0）
pub fn verify_cs_com(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    proof: &CsComProof,
) -> CryptoResult<bool> {
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_cs_com(params, commitment, &proof.r2, &proof.r4);
    let two = BigUint::from(2u32);

    let two_e = &two * &e;
    let two_z_s1 = &two * &proof.z_s1;
    let two_z_r1 = &two * &proof.z_r1;
    let two_z_s2 = &two * &proof.z_s2;
    let two_z_r2 = &two * &proof.z_r2;

    let lhs_1 =
        (params.g_prime.modpow(&two_z_s1, &params.n2) * params.h_prime.modpow(&two_z_r1, &params.n2)) % &params.n2;
    let rhs_1 = (proof.r2.modpow(&two, &params.n2) * commitment.c2.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_2 =
        (params.g_prime.modpow(&two_z_s2, &params.n2) * params.h_prime.modpow(&two_z_r2, &params.n2)) % &params.n2;
    let rhs_2 = (proof.r4.modpow(&two, &params.n2) * commitment.c4.modpow(&two_e, &params.n2)) % &params.n2;

    Ok(lhs_1 == rhs_1 && lhs_2 == rhs_2)
}

/// `Prove^Com` 的“对公开密文开口”变体的证明对象。
///
/// 背景与动机：
/// - `CsComProof`（上面的 `prove_cs_com`）只证明“知道某个开口”，也就是只验证
///   承诺的第二分量 C2/C4 是良构的 DF 承诺，从而让抽取器可以还原 (s1,r1,s2,r2)。
///   它【不】把承诺绑定到任何具体的公开明文。
/// - 但论文 Alg.2 的递归【基例】要求的是更强的语句：
///     π1 = NIZK[r : Com_AH(⌊x0⌋, r) = CP]
///   即“CP 承诺的正是那个【公开的、折叠后的输入密文】x0”。
///   缺了这一层锚定，简洁求值证明的可靠性会被击穿（prover 可令 E 为任意密文）。
///
/// 因此这里补一个专门的证明系统：给定【公开】密文 x0=(u,v)，证明
///     C1 = ±u·g^{s1},  C2 = ±(g')^{s1}(h')^{r1},
///     C3 = ±v·g^{s2},  C4 = ±(g')^{s2}(h')^{r2}
/// 其中 ± 是隐藏的符号位 (a1,b1,a2,b2)∈{-1,+1}。
///
/// 证明结构（Fiat-Shamir 化的 eqrep-Z_{n^2}，用“平方”消符号）：
/// - R1=g^{k_s1}, R2=(g')^{k_s1}(h')^{k_r1}, R3=g^{k_s2}, R4=(g')^{k_s2}(h')^{k_r2}
/// - e = Hash(statement, R1..R4)
/// - z_s1=k_s1+e·s1, z_r1=k_r1+e·r1, z_s2=k_s2+e·s2, z_r2=k_r2+e·r2
///
/// 关键点：R1/R3 用基 g，把值分量指数 s1/s2 与 C2/C4 里出现的【同一个】 s1/s2
/// 绑在一起，这正是缺失的锚定；u,v 作为公开常数进入验证式（不进入见证）。
#[derive(Debug, Clone)]
pub struct CsComCtProof {
    /// R1 = g^{k_s1}（值分量 C1 的盲化承诺，基为 g）。
    pub r1: BigUint,
    /// R2 = (g')^{k_s1}(h')^{k_r1}（随机分量 C2 的盲化承诺）。
    pub r2: BigUint,
    /// R3 = g^{k_s2}（值分量 C3 的盲化承诺，基为 g）。
    pub r3: BigUint,
    /// R4 = (g')^{k_s2}(h')^{k_r2}（随机分量 C4 的盲化承诺）。
    pub r4: BigUint,
    /// z_s1 = k_s1 + e·s1（整数域，不取模）。
    pub z_s1: BigUint,
    /// z_r1 = k_r1 + e·r1。
    pub z_r1: BigUint,
    /// z_s2 = k_s2 + e·s2。
    pub z_s2: BigUint,
    /// z_r2 = k_r2 + e·r2。
    pub z_r2: BigUint,
}

/// 计算“对公开密文开口”证明的 Fiat-Shamir 挑战：
/// e <- Hash(n, g, g', h', C1, C2, C3, C4, u, v, R1, R2, R3, R4)
///
/// 注意：挑战必须同时绑定【完整承诺 C=(C1..C4)】与【公开密文 (u,v)】，
/// 否则同一份证明可被搬到另一条 (C, x0) 语句上复用（可转移性 → 可靠性隐患）。
fn fs_challenge_for_cs_com_ct(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    u: &BigUint,
    v: &BigUint,
    r1: &BigUint,
    r2: &BigUint,
    r3: &BigUint,
    r4: &BigUint,
) -> BigUint {
    fs_challenge_from_biguints(&[
        &params.n,
        &params.g,
        &params.g_prime,
        &params.h_prime,
        &commitment.c1,
        &commitment.c2,
        &commitment.c3,
        &commitment.c4,
        u,
        v,
        r1,
        r2,
        r3,
        r4,
    ])
}

/// 证明承诺 `commitment` 打开到【公开】密文 `x0`（论文 Alg.2 基例 π1）。
///
/// 参数：
/// - `commitment`：待证承诺 C=(C1,C2,C3,C4)；
/// - `x0`：公开的目标密文 (u,v)；
/// - `opening`：C 对 x0 的真实开口 O=(a1,a2,s1,s2,r1,r2,b1,b2)。
///
/// 该函数会先自检见证与承诺一致，避免对错误实例产出“格式合法”的证明。
pub fn prove_cs_com_ciphertext(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    x0: &CsCiphertext,
    opening: &CsCommitOpening,
) -> CryptoResult<CsComCtProof> {
    // 符号位必须在 {-1,+1}，否则平方消符号的语义不成立。
    if !is_pm_one(opening.a1)
        || !is_pm_one(opening.b1)
        || !is_pm_one(opening.a2)
        || !is_pm_one(opening.b2)
    {
        return Err(CryptoError::InvalidInput("signs must be in {-1,+1}"));
    }

    let n2 = &params.n2;
    // 公开密文分量统一规约到 [0, n^2)。
    let u = &x0.c0 % n2;
    let v = &x0.c1 % n2;

    // ---- 见证一致性自检：四条主等式都必须成立 ----
    // C1 = a1 · u · g^{s1}
    let c1_expected = apply_sign_mod_n2(&((&u * params.g.modpow(&opening.s1, n2)) % n2), opening.a1, n2)?;
    // C2 = b1 · (g')^{s1} · (h')^{r1}
    let c2_expected = apply_sign_mod_n2(
        &((params.g_prime.modpow(&opening.s1, n2) * params.h_prime.modpow(&opening.r1, n2)) % n2),
        opening.b1,
        n2,
    )?;
    // C3 = a2 · v · g^{s2}
    let c3_expected = apply_sign_mod_n2(&((&v * params.g.modpow(&opening.s2, n2)) % n2), opening.a2, n2)?;
    // C4 = b2 · (g')^{s2} · (h')^{r2}
    let c4_expected = apply_sign_mod_n2(
        &((params.g_prime.modpow(&opening.s2, n2) * params.h_prime.modpow(&opening.r2, n2)) % n2),
        opening.b2,
        n2,
    )?;
    if c1_expected != commitment.c1
        || c2_expected != commitment.c2
        || c3_expected != commitment.c3
        || c4_expected != commitment.c4
    {
        return Err(CryptoError::InvalidInput("opening does not open C to x0"));
    }

    // ---- Commit 阶段 ----
    // 盲化位长取 B + 2λ + 256：其中 256 覆盖 Fiat-Shamir 挑战 e 的位长，
    // 2λ 提供统计隐藏余量，从而保证 z = k + e·w 不泄露见证 w（s1,r1,s2,r2）。
    let blind_bits = derive_blinding_bits(params, 256)?;
    let blind_bits_u64 =
        u64::try_from(blind_bits).map_err(|_| CryptoError::InvalidInput("blind bits too large"))?;
    let mut rng = OsRng;
    let k_s1 = rng.gen_biguint(blind_bits_u64);
    let k_r1 = rng.gen_biguint(blind_bits_u64);
    let k_s2 = rng.gen_biguint(blind_bits_u64);
    let k_r2 = rng.gen_biguint(blind_bits_u64);

    // R1/R3 用基 g（对应值分量 C1/C3 的指数 s1/s2）；
    // R2/R4 用基 (g',h')（对应随机分量 C2/C4）。
    let r1 = params.g.modpow(&k_s1, n2);
    let r2 = (params.g_prime.modpow(&k_s1, n2) * params.h_prime.modpow(&k_r1, n2)) % n2;
    let r3 = params.g.modpow(&k_s2, n2);
    let r4 = (params.g_prime.modpow(&k_s2, n2) * params.h_prime.modpow(&k_r2, n2)) % n2;

    // ---- Challenge 阶段 ----
    let e = fs_challenge_for_cs_com_ct(params, commitment, &u, &v, &r1, &r2, &r3, &r4);

    // ---- Response 阶段（整数域线性组合，不取模）----
    Ok(CsComCtProof {
        r1,
        r2,
        r3,
        r4,
        z_s1: &k_s1 + &e * &opening.s1,
        z_r1: &k_r1 + &e * &opening.r1,
        z_s2: &k_s2 + &e * &opening.s2,
        z_r2: &k_r2 + &e * &opening.r2,
    })
}

/// 验证承诺 `commitment` 打开到【公开】密文 `x0`。
///
/// 验证式（全部两边平方以消去隐藏符号 a1,b1,a2,b2）：
/// 令 A1 = C1^2 · (u^2)^{-1} = g^{2 s1}，A3 = C3^2 · (v^2)^{-1} = g^{2 s2}，则
///   (1) g^{2 z_s1}                      ?= R1^2 · A1^e
///   (2) (g')^{2 z_s1} (h')^{2 z_r1}     ?= R2^2 · C2^{2e}
///   (3) g^{2 z_s2}                      ?= R3^2 · A3^e
///   (4) (g')^{2 z_s2} (h')^{2 z_r2}     ?= R4^2 · C4^{2e}
///
/// 等式 (1)/(3) 把值分量（除掉公开 u,v 后剩下的 g^{2 s}）与 (2)/(4) 里的【同一
/// 个】 s1/s2 绑定，这正是“承诺确实打开到 x0”的锚定。
pub fn verify_cs_com_ciphertext(
    params: &CsCommitParams,
    commitment: &CsCommitment,
    x0: &CsCiphertext,
    proof: &CsComCtProof,
) -> CryptoResult<bool> {
    let n2 = &params.n2;
    if n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let u = &x0.c0 % n2;
    let v = &x0.c1 % n2;
    // u,v 必须是 Z*_{n^2} 单位元，否则 u^2/v^2 不可逆（诚实密文分量落在 |QR_{n^2}|，
    // 必然与 n^2 互素；这里对畸形输入直接判否，而不是抛错）。
    if gcd(u.clone(), n2.clone()) != BigUint::one() || gcd(v.clone(), n2.clone()) != BigUint::one() {
        return Ok(false);
    }

    let two = BigUint::from(2u32);
    let e = fs_challenge_for_cs_com_ct(params, commitment, &u, &v, &proof.r1, &proof.r2, &proof.r3, &proof.r4);
    let two_e = &two * &e;

    // A1 = C1^2 / u^2 = g^{2 s1}; A3 = C3^2 / v^2 = g^{2 s2}
    let a1 = (commitment.c1.modpow(&two, n2) * modinv(&u.modpow(&two, n2), n2)?) % n2;
    let a3 = (commitment.c3.modpow(&two, n2) * modinv(&v.modpow(&two, n2), n2)?) % n2;

    // (1) g^{2 z_s1} ?= R1^2 · A1^e
    let ok1 = params.g.modpow(&(&two * &proof.z_s1), n2)
        == (proof.r1.modpow(&two, n2) * a1.modpow(&e, n2)) % n2;
    // (2) (g')^{2 z_s1} (h')^{2 z_r1} ?= R2^2 · C2^{2e}
    let ok2 = (params.g_prime.modpow(&(&two * &proof.z_s1), n2)
        * params.h_prime.modpow(&(&two * &proof.z_r1), n2))
        % n2
        == (proof.r2.modpow(&two, n2) * commitment.c2.modpow(&two_e, n2)) % n2;
    // (3) g^{2 z_s2} ?= R3^2 · A3^e
    let ok3 = params.g.modpow(&(&two * &proof.z_s2), n2)
        == (proof.r3.modpow(&two, n2) * a3.modpow(&e, n2)) % n2;
    // (4) (g')^{2 z_s2} (h')^{2 z_r2} ?= R4^2 · C4^{2e}
    let ok4 = (params.g_prime.modpow(&(&two * &proof.z_s2), n2)
        * params.h_prime.modpow(&(&two * &proof.z_r2), n2))
        % n2
        == (proof.r4.modpow(&two, n2) * commitment.c4.modpow(&two_e, n2)) % n2;

    Ok(ok1 && ok2 && ok3 && ok4)
}

/// ProveMultCS(params, Ca, Cb, Cy, [Oa, Ob, y, r_y, b_y, {b_i}]) -> pi
///
/// 说明：
/// 1. y、r_y 在整数域 Z 中处理，可为负；
/// 2. b_y 与 b_i 为符号见证，必须在 {-1,+1}；
/// 3. 为保证稳定零知识，盲化因子在对称区间 [-2^ell, 2^ell] 采样，
///    ell = B + 2lambda + lambda_c，当前实现取 lambda_c=256。
pub fn prove_cs_mult(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cy: &BigUint,
    oa: &CsCommitOpening,
    ob: &CsCommitOpening,
    y: &BigInt,
    r_y: &BigInt,
    b_y: i8,
    b: [i8; 4],
) -> CryptoResult<CsMultProof> {
    if !is_pm_one(b_y) || !b.into_iter().all(is_pm_one) {
        return Err(CryptoError::InvalidInput("b_y and b_i must be in {-1,+1}"));
    }

    // 1) 从开口构造 gamma_i。
    let gamma1 = bu_to_bi(&oa.s1)? - (y * bu_to_bi(&ob.s1)?);
    let gamma2 = bu_to_bi(&oa.r1)? - (y * bu_to_bi(&ob.r1)?);
    let gamma3 = bu_to_bi(&oa.s2)? - (y * bu_to_bi(&ob.s2)?);
    let gamma4 = bu_to_bi(&oa.r2)? - (y * bu_to_bi(&ob.r2)?);

    // 2) 由 Oa/Ob 推导 beta_i 并与输入 b_i 对齐检查。
    //
    // 注意：beta_i 需要按指数 y 的奇偶处理输入符号项：
    // beta = sign_out / (sign_in^y)
    // 若 y 为偶数，sign_in^y = +1；若 y 为奇数，sign_in^y = sign_in。
    let ob_a1_pow_y = sign_pow_i8(ob.a1, y)?;
    let ob_b1_pow_y = sign_pow_i8(ob.b1, y)?;
    let ob_a2_pow_y = sign_pow_i8(ob.a2, y)?;
    let ob_b2_pow_y = sign_pow_i8(ob.b2, y)?;

    let beta1 = div_two_signs(oa.a1, ob_a1_pow_y)?;
    let beta2 = div_two_signs(oa.b1, ob_b1_pow_y)?;
    let beta3 = div_two_signs(oa.a2, ob_a2_pow_y)?;
    let beta4 = div_two_signs(oa.b2, ob_b2_pow_y)?;
    if [beta1, beta2, beta3, beta4] != b {
        return Err(CryptoError::InvalidInput("input b_i do not match signs derived from Oa/Ob"));
    }

    // 3) 检查 Cy 与四个主等式关系，防止无效实例生成证明。
    let cy_expected = apply_sign_mod_n2(
        &((modpow_signed(&params.g_prime, y, &params.n2)? * modpow_signed(&params.h_prime, r_y, &params.n2)?)
            % &params.n2),
        b_y,
        &params.n2,
    )?;
    if &cy_expected != cy {
        return Err(CryptoError::InvalidInput("witness does not satisfy Cy equation"));
    }

    let ca1_expected = apply_sign_mod_n2(
        &((modpow_signed(&cb.c1, y, &params.n2)? * modpow_signed(&params.g, &gamma1, &params.n2)?) % &params.n2),
        b[0],
        &params.n2,
    )?;
    if ca1_expected != ca.c1 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca1 equation"));
    }

    let ca2_expected = apply_sign_mod_n2(
        &((modpow_signed(&cb.c2, y, &params.n2)?
            * modpow_signed(&params.g_prime, &gamma1, &params.n2)?
            * modpow_signed(&params.h_prime, &gamma2, &params.n2)?)
            % &params.n2),
        b[1],
        &params.n2,
    )?;
    if ca2_expected != ca.c2 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca2 equation"));
    }

    let ca3_expected = apply_sign_mod_n2(
        &((modpow_signed(&cb.c3, y, &params.n2)? * modpow_signed(&params.g, &gamma3, &params.n2)?) % &params.n2),
        b[2],
        &params.n2,
    )?;
    if ca3_expected != ca.c3 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca3 equation"));
    }

    let ca4_expected = apply_sign_mod_n2(
        &((modpow_signed(&cb.c4, y, &params.n2)?
            * modpow_signed(&params.g_prime, &gamma3, &params.n2)?
            * modpow_signed(&params.h_prime, &gamma4, &params.n2)?)
            % &params.n2),
        b[3],
        &params.n2,
    )?;
    if ca4_expected != ca.c4 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca4 equation"));
    }

    // 4) 盲化采样参数：ell = B + 2lambda + lambda_c。
    let ell = derive_blinding_bits(params, 256)?;

    // 5) Commit 阶段：采样盲化并计算 R 值。
    let mut rng = OsRng;
    let k_y = sample_symmetric_bigint(&mut rng, ell)?;
    let k_ry = sample_symmetric_bigint(&mut rng, ell)?;
    let k1 = sample_symmetric_bigint(&mut rng, ell)?;
    let k2 = sample_symmetric_bigint(&mut rng, ell)?;
    let k3 = sample_symmetric_bigint(&mut rng, ell)?;
    let k4 = sample_symmetric_bigint(&mut rng, ell)?;

    let r_y_elem = (modpow_signed(&params.g_prime, &k_y, &params.n2)?
        * modpow_signed(&params.h_prime, &k_ry, &params.n2)?)
        % &params.n2;
    let r1 =
        (modpow_signed(&cb.c1, &k_y, &params.n2)? * modpow_signed(&params.g, &k1, &params.n2)?) % &params.n2;
    let r2 = (modpow_signed(&cb.c2, &k_y, &params.n2)?
        * modpow_signed(&params.g_prime, &k1, &params.n2)?
        * modpow_signed(&params.h_prime, &k2, &params.n2)?)
        % &params.n2;
    let r3 =
        (modpow_signed(&cb.c3, &k_y, &params.n2)? * modpow_signed(&params.g, &k3, &params.n2)?) % &params.n2;
    let r4 = (modpow_signed(&cb.c4, &k_y, &params.n2)?
        * modpow_signed(&params.g_prime, &k3, &params.n2)?
        * modpow_signed(&params.h_prime, &k4, &params.n2)?)
        % &params.n2;

    // 6) Challenge 阶段。
    let e = fs_challenge_for_cs_mult(params, ca, cb, cy, &r_y_elem, &r1, &r2, &r3, &r4);

    // 7) Response 阶段：z = k + e * witness（整数域）。
    let e_bi = bu_to_bi(&e)?;
    let z_y = &k_y + (&e_bi * y);
    let z_ry = &k_ry + (&e_bi * r_y);
    let z1 = &k1 + (&e_bi * &gamma1);
    let z2 = &k2 + (&e_bi * &gamma2);
    let z3 = &k3 + (&e_bi * &gamma3);
    let z4 = &k4 + (&e_bi * &gamma4);

    Ok(CsMultProof {
        r_y: r_y_elem,
        r1,
        r2,
        r3,
        r4,
        z_y,
        z_ry,
        z1,
        z2,
        z3,
        z4,
    })
}

/// VerifyMultCS(params, Ca, Cb, Cy, pi) -> {0,1}
///
/// 验证你给出的 5 条平方关系：
/// 1) Cy 标量承诺关系
/// 2)~5) 四个密文分量同态标量乘法关系
pub fn verify_cs_mult(
    params: &CsCommitParams,
    ca: &CsCommitment,
    cb: &CsCommitment,
    cy: &BigUint,
    proof: &CsMultProof,
) -> CryptoResult<bool> {
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_cs_mult(
        params,
        ca,
        cb,
        cy,
        &proof.r_y,
        &proof.r1,
        &proof.r2,
        &proof.r3,
        &proof.r4,
    );
    let two = BigUint::from(2u32);
    let two_e = &two * &e;

    let two_bi = BigInt::from(2u32);
    let two_z_y = &proof.z_y * &two_bi;
    let two_z_ry = &proof.z_ry * &two_bi;
    let two_z1 = &proof.z1 * &two_bi;
    let two_z2 = &proof.z2 * &two_bi;
    let two_z3 = &proof.z3 * &two_bi;
    let two_z4 = &proof.z4 * &two_bi;

    let lhs_y = (modpow_signed(&params.g_prime, &two_z_y, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z_ry, &params.n2)?)
        % &params.n2;
    let rhs_y = (proof.r_y.modpow(&two, &params.n2) * cy.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_1 =
        (modpow_signed(&cb.c1, &two_z_y, &params.n2)? * modpow_signed(&params.g, &two_z1, &params.n2)?) % &params.n2;
    let rhs_1 = (proof.r1.modpow(&two, &params.n2) * ca.c1.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_2 = (modpow_signed(&cb.c2, &two_z_y, &params.n2)?
        * modpow_signed(&params.g_prime, &two_z1, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z2, &params.n2)?)
        % &params.n2;
    let rhs_2 = (proof.r2.modpow(&two, &params.n2) * ca.c2.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_3 =
        (modpow_signed(&cb.c3, &two_z_y, &params.n2)? * modpow_signed(&params.g, &two_z3, &params.n2)?) % &params.n2;
    let rhs_3 = (proof.r3.modpow(&two, &params.n2) * ca.c3.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_4 = (modpow_signed(&cb.c4, &two_z_y, &params.n2)?
        * modpow_signed(&params.g_prime, &two_z3, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z4, &params.n2)?)
        % &params.n2;
    let rhs_4 = (proof.r4.modpow(&two, &params.n2) * ca.c4.modpow(&two_e, &params.n2)) % &params.n2;

    Ok(lhs_y == rhs_y && lhs_1 == rhs_1 && lhs_2 == rhs_2 && lhs_3 == rhs_3 && lhs_4 == rhs_4)
}

/// 预留接口：证明 CS 加密正确性。
///
/// ProveEncCS(params, pkAH=k, Ca, Cy, [a, r_a, y, Oa, Oy, b_y, {b_i}]) -> pi
///
/// 对应关系：
/// Cy   = b_y (g')^y (h')^{r_y}
/// Ca,1 = b1  (g*)^{r_a} (g')^{s_a1}
/// Ca,2 = b2  (g')^{s_a1} (h')^{r_a1}
/// Ca,3 = b3  k^{r_a} (h*)^y (g')^{s_a2}
/// Ca,4 = b4  (g')^{s_a2} (h')^{r_a2}
pub fn prove_cs_enc(
    params: &CsCommitParams,
    k: &BigUint,
    ca: &CsCommitment,
    cy: &BigUint,
    oa: &CsCommitOpening,
    y: &BigInt,
    r_y: &BigInt,
    r_a: &BigInt,
    b_y: i8,
    b: [i8; 4],
) -> CryptoResult<CsEncProof> {
    if !is_pm_one(b_y) || !b.into_iter().all(is_pm_one) {
        return Err(CryptoError::InvalidInput("b_y and b_i must be in {-1,+1}"));
    }
    if [oa.a1, oa.b1, oa.a2, oa.b2] != b {
        return Err(CryptoError::InvalidInput("input b_i do not match signs from Oa"));
    }

    // 先检查见证与公共语句的一致性。
    let cy_expected = apply_sign_mod_n2(
        &((modpow_signed(&params.g_prime, y, &params.n2)? * modpow_signed(&params.h_prime, r_y, &params.n2)?)
            % &params.n2),
        b_y,
        &params.n2,
    )?;
    if &cy_expected != cy {
        return Err(CryptoError::InvalidInput("witness does not satisfy Cy equation"));
    }

    let ca1_expected = apply_sign_mod_n2(
        &((modpow_signed(&params.g_star, r_a, &params.n2)? * params.g_prime.modpow(&oa.s1, &params.n2))
            % &params.n2),
        b[0],
        &params.n2,
    )?;
    if ca1_expected != ca.c1 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca1 equation"));
    }

    let ca2_expected = apply_sign_mod_n2(
        &((params.g_prime.modpow(&oa.s1, &params.n2) * params.h_prime.modpow(&oa.r1, &params.n2)) % &params.n2),
        b[1],
        &params.n2,
    )?;
    if ca2_expected != ca.c2 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca2 equation"));
    }

    let ca3_expected = apply_sign_mod_n2(
        &((modpow_signed(k, r_a, &params.n2)?
            * modpow_signed(&params.h_star, y, &params.n2)?
            * params.g_prime.modpow(&oa.s2, &params.n2))
            % &params.n2),
        b[2],
        &params.n2,
    )?;
    if ca3_expected != ca.c3 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca3 equation"));
    }

    let ca4_expected = apply_sign_mod_n2(
        &((params.g_prime.modpow(&oa.s2, &params.n2) * params.h_prime.modpow(&oa.r2, &params.n2)) % &params.n2),
        b[3],
        &params.n2,
    )?;
    if ca4_expected != ca.c4 {
        return Err(CryptoError::InvalidInput("witness does not satisfy Ca4 equation"));
    }

    // 盲化位长：ell = B + 2lambda + lambda_c。
    let ell = derive_blinding_bits(params, 256)?;

    // 1) Commit：采样 7 个盲化因子并构造 5 个盲化承诺。
    let mut rng = OsRng;
    let k_y = sample_symmetric_bigint(&mut rng, ell)?;
    let k_ry = sample_symmetric_bigint(&mut rng, ell)?;
    let k_ra = sample_symmetric_bigint(&mut rng, ell)?;
    let k_s1 = sample_symmetric_bigint(&mut rng, ell)?;
    let k_r1 = sample_symmetric_bigint(&mut rng, ell)?;
    let k_s2 = sample_symmetric_bigint(&mut rng, ell)?;
    let k_r2 = sample_symmetric_bigint(&mut rng, ell)?;

    let r_y_elem = (modpow_signed(&params.g_prime, &k_y, &params.n2)?
        * modpow_signed(&params.h_prime, &k_ry, &params.n2)?)
        % &params.n2;
    let r1 = (modpow_signed(&params.g_star, &k_ra, &params.n2)?
        * modpow_signed(&params.g_prime, &k_s1, &params.n2)?)
        % &params.n2;
    let r2 = (modpow_signed(&params.g_prime, &k_s1, &params.n2)?
        * modpow_signed(&params.h_prime, &k_r1, &params.n2)?)
        % &params.n2;
    let r3 = (modpow_signed(k, &k_ra, &params.n2)?
        * modpow_signed(&params.h_star, &k_y, &params.n2)?
        * modpow_signed(&params.g_prime, &k_s2, &params.n2)?)
        % &params.n2;
    let r4 = (modpow_signed(&params.g_prime, &k_s2, &params.n2)?
        * modpow_signed(&params.h_prime, &k_r2, &params.n2)?)
        % &params.n2;

    // 2) Challenge。
    let e = fs_challenge_for_cs_enc(params, k, ca, cy, &r_y_elem, &r1, &r2, &r3, &r4);

    // 3) Response。
    let e_bi = bu_to_bi(&e)?;
    let z_y = &k_y + (&e_bi * y);
    let z_ry = &k_ry + (&e_bi * r_y);
    let z_ra = &k_ra + (&e_bi * r_a);
    let z_s1 = &k_s1 + (&e_bi * bu_to_bi(&oa.s1)?);
    let z_r1 = &k_r1 + (&e_bi * bu_to_bi(&oa.r1)?);
    let z_s2 = &k_s2 + (&e_bi * bu_to_bi(&oa.s2)?);
    let z_r2 = &k_r2 + (&e_bi * bu_to_bi(&oa.r2)?);

    Ok(CsEncProof {
        r_y: r_y_elem,
        r1,
        r2,
        r3,
        r4,
        z_y,
        z_ry,
        z_ra,
        z_s1,
        z_r1,
        z_s2,
        z_r2,
    })
}

/// VerifyEncCS(params, k, Ca, Cy, pi) -> {0,1}
///
/// 按题面算法验证五条平方等式：
/// - Condition_y
/// - Condition_1..Condition_4
pub fn verify_cs_enc(
    params: &CsCommitParams,
    k: &BigUint,
    ca: &CsCommitment,
    cy: &BigUint,
    proof: &CsEncProof,
) -> CryptoResult<bool> {
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_cs_enc(params, k, ca, cy, &proof.r_y, &proof.r1, &proof.r2, &proof.r3, &proof.r4);
    let two = BigUint::from(2u32);
    let two_e = &two * &e;

    let two_bi = BigInt::from(2u32);
    let two_z_y = &proof.z_y * &two_bi;
    let two_z_ry = &proof.z_ry * &two_bi;
    let two_z_ra = &proof.z_ra * &two_bi;
    let two_z_s1 = &proof.z_s1 * &two_bi;
    let two_z_r1 = &proof.z_r1 * &two_bi;
    let two_z_s2 = &proof.z_s2 * &two_bi;
    let two_z_r2 = &proof.z_r2 * &two_bi;

    let lhs_y = (modpow_signed(&params.g_prime, &two_z_y, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z_ry, &params.n2)?)
        % &params.n2;
    let rhs_y = (proof.r_y.modpow(&two, &params.n2) * cy.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_1 = (modpow_signed(&params.g_star, &two_z_ra, &params.n2)?
        * modpow_signed(&params.g_prime, &two_z_s1, &params.n2)?)
        % &params.n2;
    let rhs_1 = (proof.r1.modpow(&two, &params.n2) * ca.c1.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_2 = (modpow_signed(&params.g_prime, &two_z_s1, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z_r1, &params.n2)?)
        % &params.n2;
    let rhs_2 = (proof.r2.modpow(&two, &params.n2) * ca.c2.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_3 = (modpow_signed(k, &two_z_ra, &params.n2)?
        * modpow_signed(&params.h_star, &two_z_y, &params.n2)?
        * modpow_signed(&params.g_prime, &two_z_s2, &params.n2)?)
        % &params.n2;
    let rhs_3 = (proof.r3.modpow(&two, &params.n2) * ca.c3.modpow(&two_e, &params.n2)) % &params.n2;

    let lhs_4 = (modpow_signed(&params.g_prime, &two_z_s2, &params.n2)?
        * modpow_signed(&params.h_prime, &two_z_r2, &params.n2)?)
        % &params.n2;
    let rhs_4 = (proof.r4.modpow(&two, &params.n2) * ca.c4.modpow(&two_e, &params.n2)) % &params.n2;

    Ok(lhs_y == rhs_y && lhs_1 == rhs_1 && lhs_2 == rhs_2 && lhs_3 == rhs_3 && lhs_4 == rhs_4)
}

/// 测试辅助函数：允许外部指定全部随机开口和符号，方便构造可重复测试。
#[cfg(test)]
fn commit_cs_with_opening(
    params: &CsCommitParams,
    c: &CsCiphertext,
    opening: &CsCommitOpening,
) -> CryptoResult<CsCommitment> {
    let gs1 = params.g.modpow(&opening.s1, &params.n2);
    let gs2 = params.g.modpow(&opening.s2, &params.n2);
    let gp_s1 = params.g_prime.modpow(&opening.s1, &params.n2);
    let gp_s2 = params.g_prime.modpow(&opening.s2, &params.n2);
    let hp_r1 = params.h_prime.modpow(&opening.r1, &params.n2);
    let hp_r2 = params.h_prime.modpow(&opening.r2, &params.n2);

    let c1_unsigned = (&c.c0 * gs1) % &params.n2;
    let c2_unsigned = (gp_s1 * hp_r1) % &params.n2;
    let c3_unsigned = (&c.c1 * gs2) % &params.n2;
    let c4_unsigned = (gp_s2 * hp_r2) % &params.n2;

    Ok(CsCommitment {
        c1: apply_sign_mod_n2(&c1_unsigned, opening.a1, &params.n2)?,
        c2: apply_sign_mod_n2(&c2_unsigned, opening.b1, &params.n2)?,
        c3: apply_sign_mod_n2(&c3_unsigned, opening.a2, &params.n2)?,
        c4: apply_sign_mod_n2(&c4_unsigned, opening.b2, &params.n2)?,
    })
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;
    use crate::cs::{enc_cs, keygen_cs, setup_cs};
    use crate::df::setup_df;
    use crate::math::sample_unit_mod_n2;

    #[test]
    fn test_setup_cs_commit_params_consistency() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };

        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");
        assert_eq!(params.n, cs_params.n);
        assert_eq!(params.n2, cs_params.n2);
        assert_eq!(params.g_star, cs_params.g);
        assert_eq!(params.h_star, cs_params.h);
        assert_eq!(params.g_prime, df_params.g);
        assert_eq!(params.h_prime, df_params.h);
    }

    #[test]
    fn test_setup_cs_commit_reject_mismatched_modulus() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = setup_df(64).expect("setup df should succeed");
        let result = setup_cs_commit(40, &cs_params, &df_params);

        if cs_params.n2 != df_params.n2 {
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_commit_cs_formula_manual_check() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let m = BigUint::from(7u32);
        let ct = enc_cs(&cs_params, &pk, &m).expect("enc should succeed");

        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let opening = CsCommitOpening {
            a1: 1,
            a2: -1,
            s1: BigUint::from(10u32),
            s2: BigUint::from(11u32),
            r1: BigUint::from(12u32),
            r2: BigUint::from(13u32),
            b1: -1,
            b2: 1,
        };

        let manual = commit_cs_with_opening(&params, &ct, &opening).expect("manual commit should succeed");
        let manual_again = commit_cs_with_opening(&params, &ct, &opening).expect("manual commit should succeed");
        assert_eq!(manual.c1, manual_again.c1);
        assert_eq!(manual.c2, manual_again.c2);
        assert_eq!(manual.c3, manual_again.c3);
        assert_eq!(manual.c4, manual_again.c4);
    }

    #[test]
    fn test_prove_cs_com_generate_valid_responses() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let m = BigUint::from(9u32);
        let ct = enc_cs(&cs_params, &pk, &m).expect("enc should succeed");
        let committed = commit_cs(&params, &ct, 96).expect("commit cs should succeed");

        let proof =
            prove_cs_com(&params, &committed.commitment, &committed.opening).expect("prove cs com should succeed");

        // 使用与 prove 相同 transcript 重新计算挑战，检查响应是否满足线性关系。
        let e = fs_challenge_for_cs_com(&params, &committed.commitment, &proof.r2, &proof.r4);

        // 还原无符号基项：若 C2 = -U，则再次乘以 -1 可得到 U。
        let c2_unsigned = apply_sign_mod_n2(&committed.commitment.c2, committed.opening.b1, &params.n2)
            .expect("valid sign");
        let c4_unsigned = apply_sign_mod_n2(&committed.commitment.c4, committed.opening.b2, &params.n2)
            .expect("valid sign");

        let lhs2 =
            (params.g_prime.modpow(&proof.z_s1, &params.n2) * params.h_prime.modpow(&proof.z_r1, &params.n2))
                % &params.n2;
        let rhs2 = (&proof.r2 * c2_unsigned.modpow(&e, &params.n2)) % &params.n2;
        assert_eq!(lhs2, rhs2);

        let lhs4 =
            (params.g_prime.modpow(&proof.z_s2, &params.n2) * params.h_prime.modpow(&proof.z_r2, &params.n2))
                % &params.n2;
        let rhs4 = (&proof.r4 * c4_unsigned.modpow(&e, &params.n2)) % &params.n2;
        assert_eq!(lhs4, rhs4);
    }

    #[test]
    fn test_verify_cs_com_accept_valid_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let m = BigUint::from(11u32);
        let ct = enc_cs(&cs_params, &pk, &m).expect("enc should succeed");
        let committed = commit_cs(&params, &ct, 96).expect("commit cs should succeed");

        let proof =
            prove_cs_com(&params, &committed.commitment, &committed.opening).expect("prove cs com should succeed");

        let ok = verify_cs_com(&params, &committed.commitment, &proof).expect("verify should run");
        assert!(ok);
    }

    /// 修复1回归测试：`prove/verify_cs_com_ciphertext` 是“对公开密文开口”的证明。
    /// 正例：对真实承诺的目标密文 x0 验证通过。
    /// 反例（关键）：把公开目标换成另一条密文 x0'，验证必须失败——这正是
    /// 简洁求值证明基例所需的“锚定到公开折叠值”能力（缺了它可靠性被击穿）。
    #[test]
    fn test_verify_cs_com_ciphertext_accepts_and_rejects_wrong_public_value() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");

        // x0：被承诺的真实密文。
        let x0 = enc_cs(&cs_params, &pk, &BigUint::from(11u32)).expect("enc x0 should succeed");
        let committed = commit_cs(&params, &x0, 96).expect("commit cs should succeed");

        let proof = prove_cs_com_ciphertext(&params, &committed.commitment, &x0, &committed.opening)
            .expect("prove cs com ciphertext should succeed");

        // 正例：对 x0 验证通过。
        let ok = verify_cs_com_ciphertext(&params, &committed.commitment, &x0, &proof)
            .expect("verify should run");
        assert!(ok);

        // 反例：换成另一条公开密文 x0'（消息不同），验证必须拒绝。
        let x0_prime = enc_cs(&cs_params, &pk, &BigUint::from(12u32)).expect("enc x0' should succeed");
        assert_ne!(x0.c0, x0_prime.c0);
        let rejected = verify_cs_com_ciphertext(&params, &committed.commitment, &x0_prime, &proof)
            .expect("verify should run");
        assert!(!rejected);
    }

    #[test]
    fn test_verify_cs_com_reject_tampered_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let m = BigUint::from(13u32);
        let ct = enc_cs(&cs_params, &pk, &m).expect("enc should succeed");
        let committed = commit_cs(&params, &ct, 96).expect("commit cs should succeed");

        let mut proof =
            prove_cs_com(&params, &committed.commitment, &committed.opening).expect("prove cs com should succeed");

        proof.z_s1 += BigUint::from(1u32);
        let ok = verify_cs_com(&params, &committed.commitment, &proof).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_prove_and_verify_cs_add_accept() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let cta = enc_cs(&cs_params, &pk, &BigUint::from(3u32)).expect("enc a should succeed");
        let ctb = enc_cs(&cs_params, &pk, &BigUint::from(5u32)).expect("enc b should succeed");
        let wa = commit_cs(&params, &cta, 96).expect("commit a should succeed");
        let wb = commit_cs(&params, &ctb, 96).expect("commit b should succeed");

        // 构造满足加法关系的 Oc 与 Cc：先选 gamma/beta，再反推 Cc = D * Ca * Cb。
        let gamma1 = BigInt::from(5u32);
        let gamma2 = BigInt::from(7u32);
        let gamma3 = BigInt::from(11u32);
        let gamma4 = BigInt::from(13u32);

        let beta1 = -1i8;
        let beta2 = 1i8;
        let beta3 = -1i8;
        let beta4 = 1i8;

        let oc = CsCommitOpening {
            a1: mul_three_signs(beta1, wa.opening.a1, wb.opening.a1).expect("valid signs"),
            a2: mul_three_signs(beta3, wa.opening.a2, wb.opening.a2).expect("valid signs"),
            s1: (bu_to_bi(&wa.opening.s1).expect("bi")
                + bu_to_bi(&wb.opening.s1).expect("bi")
                + gamma1.clone())
            .to_biguint()
            .expect("non-negative"),
            s2: (bu_to_bi(&wa.opening.s2).expect("bi")
                + bu_to_bi(&wb.opening.s2).expect("bi")
                + gamma3.clone())
            .to_biguint()
            .expect("non-negative"),
            r1: (bu_to_bi(&wa.opening.r1).expect("bi")
                + bu_to_bi(&wb.opening.r1).expect("bi")
                + gamma2.clone())
            .to_biguint()
            .expect("non-negative"),
            r2: (bu_to_bi(&wa.opening.r2).expect("bi")
                + bu_to_bi(&wb.opening.r2).expect("bi")
                + gamma4.clone())
            .to_biguint()
            .expect("non-negative"),
            b1: mul_three_signs(beta2, wa.opening.b1, wb.opening.b1).expect("valid signs"),
            b2: mul_three_signs(beta4, wa.opening.b2, wb.opening.b2).expect("valid signs"),
        };

        let d1 = (sign_to_mod_element(beta1, &params.n2).expect("sign")
            * modpow_signed(&params.g, &gamma1, &params.n2).expect("pow"))
            % &params.n2;
        let d2 = (sign_to_mod_element(beta2, &params.n2).expect("sign")
            * modpow_signed(&params.g_prime, &gamma1, &params.n2).expect("pow")
            * modpow_signed(&params.h_prime, &gamma2, &params.n2).expect("pow"))
            % &params.n2;
        let d3 = (sign_to_mod_element(beta3, &params.n2).expect("sign")
            * modpow_signed(&params.g, &gamma3, &params.n2).expect("pow"))
            % &params.n2;
        let d4 = (sign_to_mod_element(beta4, &params.n2).expect("sign")
            * modpow_signed(&params.g_prime, &gamma3, &params.n2).expect("pow")
            * modpow_signed(&params.h_prime, &gamma4, &params.n2).expect("pow"))
            % &params.n2;

        let cc = CsCommitment {
            c1: (&d1 * &wa.commitment.c1 * &wb.commitment.c1) % &params.n2,
            c2: (&d2 * &wa.commitment.c2 * &wb.commitment.c2) % &params.n2,
            c3: (&d3 * &wa.commitment.c3 * &wb.commitment.c3) % &params.n2,
            c4: (&d4 * &wa.commitment.c4 * &wb.commitment.c4) % &params.n2,
        };

        let proof = prove_cs_add(
            &params,
            &wa.commitment,
            &wb.commitment,
            &cc,
            &wa.opening,
            &wb.opening,
            &oc,
        )
        .expect("prove add should succeed");

        let ok = verify_cs_add(&params, &wa.commitment, &wb.commitment, &cc, &proof)
            .expect("verify add should run");
        assert!(ok);
    }

    #[test]
    fn test_verify_cs_add_reject_tampered_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let cta = enc_cs(&cs_params, &pk, &BigUint::from(2u32)).expect("enc a should succeed");
        let ctb = enc_cs(&cs_params, &pk, &BigUint::from(4u32)).expect("enc b should succeed");
        let wa = commit_cs(&params, &cta, 96).expect("commit a should succeed");
        let wb = commit_cs(&params, &ctb, 96).expect("commit b should succeed");

        let gamma1 = BigInt::from(3u32);
        let gamma2 = BigInt::from(5u32);
        let gamma3 = BigInt::from(7u32);
        let gamma4 = BigInt::from(9u32);

        let beta1 = 1i8;
        let beta2 = -1i8;
        let beta3 = 1i8;
        let beta4 = -1i8;

        let oc = CsCommitOpening {
            a1: mul_three_signs(beta1, wa.opening.a1, wb.opening.a1).expect("valid signs"),
            a2: mul_three_signs(beta3, wa.opening.a2, wb.opening.a2).expect("valid signs"),
            s1: (bu_to_bi(&wa.opening.s1).expect("bi")
                + bu_to_bi(&wb.opening.s1).expect("bi")
                + gamma1.clone())
            .to_biguint()
            .expect("non-negative"),
            s2: (bu_to_bi(&wa.opening.s2).expect("bi")
                + bu_to_bi(&wb.opening.s2).expect("bi")
                + gamma3.clone())
            .to_biguint()
            .expect("non-negative"),
            r1: (bu_to_bi(&wa.opening.r1).expect("bi")
                + bu_to_bi(&wb.opening.r1).expect("bi")
                + gamma2.clone())
            .to_biguint()
            .expect("non-negative"),
            r2: (bu_to_bi(&wa.opening.r2).expect("bi")
                + bu_to_bi(&wb.opening.r2).expect("bi")
                + gamma4.clone())
            .to_biguint()
            .expect("non-negative"),
            b1: mul_three_signs(beta2, wa.opening.b1, wb.opening.b1).expect("valid signs"),
            b2: mul_three_signs(beta4, wa.opening.b2, wb.opening.b2).expect("valid signs"),
        };

        let d1 = (sign_to_mod_element(beta1, &params.n2).expect("sign")
            * modpow_signed(&params.g, &gamma1, &params.n2).expect("pow"))
            % &params.n2;
        let d2 = (sign_to_mod_element(beta2, &params.n2).expect("sign")
            * modpow_signed(&params.g_prime, &gamma1, &params.n2).expect("pow")
            * modpow_signed(&params.h_prime, &gamma2, &params.n2).expect("pow"))
            % &params.n2;
        let d3 = (sign_to_mod_element(beta3, &params.n2).expect("sign")
            * modpow_signed(&params.g, &gamma3, &params.n2).expect("pow"))
            % &params.n2;
        let d4 = (sign_to_mod_element(beta4, &params.n2).expect("sign")
            * modpow_signed(&params.g_prime, &gamma3, &params.n2).expect("pow")
            * modpow_signed(&params.h_prime, &gamma4, &params.n2).expect("pow"))
            % &params.n2;

        let cc = CsCommitment {
            c1: (&d1 * &wa.commitment.c1 * &wb.commitment.c1) % &params.n2,
            c2: (&d2 * &wa.commitment.c2 * &wb.commitment.c2) % &params.n2,
            c3: (&d3 * &wa.commitment.c3 * &wb.commitment.c3) % &params.n2,
            c4: (&d4 * &wa.commitment.c4 * &wb.commitment.c4) % &params.n2,
        };

        let mut proof = prove_cs_add(
            &params,
            &wa.commitment,
            &wb.commitment,
            &cc,
            &wa.opening,
            &wb.opening,
            &oc,
        )
        .expect("prove add should succeed");

        proof.e += BigUint::from(1u32);
        let ok = verify_cs_add(&params, &wa.commitment, &wb.commitment, &cc, &proof)
            .expect("verify add should run");
        assert!(!ok);
    }

    #[test]
    fn test_prove_and_verify_cs_mult_accept() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let ctb = enc_cs(&cs_params, &pk, &BigUint::from(6u32)).expect("enc b should succeed");
        let wb = commit_cs(&params, &ctb, 96).expect("commit b should succeed");

        let y = BigInt::from(3u32);
        let r_y = BigInt::from(17u32);
        let b_y = -1i8;
        let b = [1i8, -1i8, 1i8, -1i8];

        let gamma1 = BigInt::from(5u32);
        let gamma2 = BigInt::from(7u32);
        let gamma3 = BigInt::from(11u32);
        let gamma4 = BigInt::from(13u32);

        let oa = CsCommitOpening {
            a1: mul_three_signs(b[0], ob_sign(wb.opening.a1), 1).expect("valid signs"),
            a2: mul_three_signs(b[2], ob_sign(wb.opening.a2), 1).expect("valid signs"),
            s1: (y.clone() * bu_to_bi(&wb.opening.s1).expect("bi") + gamma1.clone())
                .to_biguint()
                .expect("non-negative"),
            s2: (y.clone() * bu_to_bi(&wb.opening.s2).expect("bi") + gamma3.clone())
                .to_biguint()
                .expect("non-negative"),
            r1: (y.clone() * bu_to_bi(&wb.opening.r1).expect("bi") + gamma2.clone())
                .to_biguint()
                .expect("non-negative"),
            r2: (y.clone() * bu_to_bi(&wb.opening.r2).expect("bi") + gamma4.clone())
                .to_biguint()
                .expect("non-negative"),
            b1: mul_three_signs(b[1], ob_sign(wb.opening.b1), 1).expect("valid signs"),
            b2: mul_three_signs(b[3], ob_sign(wb.opening.b2), 1).expect("valid signs"),
        };

        let cy = apply_sign_mod_n2(
            &((modpow_signed(&params.g_prime, &y, &params.n2).expect("pow")
                * modpow_signed(&params.h_prime, &r_y, &params.n2).expect("pow"))
                % &params.n2),
            b_y,
            &params.n2,
        )
        .expect("cy build");

        let ca = CsCommitment {
            c1: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c1, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g, &gamma1, &params.n2).expect("pow"))
                    % &params.n2),
                b[0],
                &params.n2,
            )
            .expect("ca1"),
            c2: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c2, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g_prime, &gamma1, &params.n2).expect("pow")
                    * modpow_signed(&params.h_prime, &gamma2, &params.n2).expect("pow"))
                    % &params.n2),
                b[1],
                &params.n2,
            )
            .expect("ca2"),
            c3: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c3, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g, &gamma3, &params.n2).expect("pow"))
                    % &params.n2),
                b[2],
                &params.n2,
            )
            .expect("ca3"),
            c4: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c4, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g_prime, &gamma3, &params.n2).expect("pow")
                    * modpow_signed(&params.h_prime, &gamma4, &params.n2).expect("pow"))
                    % &params.n2),
                b[3],
                &params.n2,
            )
            .expect("ca4"),
        };

        let proof = prove_cs_mult(
            &params,
            &ca,
            &wb.commitment,
            &cy,
            &oa,
            &wb.opening,
            &y,
            &r_y,
            b_y,
            b,
        )
        .expect("prove mult should succeed");

        let ok = verify_cs_mult(&params, &ca, &wb.commitment, &cy, &proof).expect("verify mult should run");
        assert!(ok);
    }

    #[test]
    fn test_verify_cs_mult_reject_tampered_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let ctb = enc_cs(&cs_params, &pk, &BigUint::from(8u32)).expect("enc b should succeed");
        let wb = commit_cs(&params, &ctb, 96).expect("commit b should succeed");

        let y = BigInt::from(3u32);
        let r_y = BigInt::from(19u32);
        let b_y = 1i8;
        let b = [-1i8, 1i8, -1i8, 1i8];

        let gamma1 = BigInt::from(3u32);
        let gamma2 = BigInt::from(5u32);
        let gamma3 = BigInt::from(7u32);
        let gamma4 = BigInt::from(9u32);

        let oa = CsCommitOpening {
            a1: mul_three_signs(b[0], ob_sign(wb.opening.a1), 1).expect("valid signs"),
            a2: mul_three_signs(b[2], ob_sign(wb.opening.a2), 1).expect("valid signs"),
            s1: (y.clone() * bu_to_bi(&wb.opening.s1).expect("bi") + gamma1.clone())
                .to_biguint()
                .expect("non-negative"),
            s2: (y.clone() * bu_to_bi(&wb.opening.s2).expect("bi") + gamma3.clone())
                .to_biguint()
                .expect("non-negative"),
            r1: (y.clone() * bu_to_bi(&wb.opening.r1).expect("bi") + gamma2.clone())
                .to_biguint()
                .expect("non-negative"),
            r2: (y.clone() * bu_to_bi(&wb.opening.r2).expect("bi") + gamma4.clone())
                .to_biguint()
                .expect("non-negative"),
            b1: mul_three_signs(b[1], ob_sign(wb.opening.b1), 1).expect("valid signs"),
            b2: mul_three_signs(b[3], ob_sign(wb.opening.b2), 1).expect("valid signs"),
        };

        let cy = apply_sign_mod_n2(
            &((modpow_signed(&params.g_prime, &y, &params.n2).expect("pow")
                * modpow_signed(&params.h_prime, &r_y, &params.n2).expect("pow"))
                % &params.n2),
            b_y,
            &params.n2,
        )
        .expect("cy build");

        let ca = CsCommitment {
            c1: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c1, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g, &gamma1, &params.n2).expect("pow"))
                    % &params.n2),
                b[0],
                &params.n2,
            )
            .expect("ca1"),
            c2: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c2, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g_prime, &gamma1, &params.n2).expect("pow")
                    * modpow_signed(&params.h_prime, &gamma2, &params.n2).expect("pow"))
                    % &params.n2),
                b[1],
                &params.n2,
            )
            .expect("ca2"),
            c3: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c3, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g, &gamma3, &params.n2).expect("pow"))
                    % &params.n2),
                b[2],
                &params.n2,
            )
            .expect("ca3"),
            c4: apply_sign_mod_n2(
                &((modpow_signed(&wb.commitment.c4, &y, &params.n2).expect("pow")
                    * modpow_signed(&params.g_prime, &gamma3, &params.n2).expect("pow")
                    * modpow_signed(&params.h_prime, &gamma4, &params.n2).expect("pow"))
                    % &params.n2),
                b[3],
                &params.n2,
            )
            .expect("ca4"),
        };

        let mut proof = prove_cs_mult(
            &params,
            &ca,
            &wb.commitment,
            &cy,
            &oa,
            &wb.opening,
            &y,
            &r_y,
            b_y,
            b,
        )
        .expect("prove mult should succeed");
        proof.z1 += BigInt::from(1u32);

        let ok = verify_cs_mult(&params, &ca, &wb.commitment, &cy, &proof).expect("verify mult should run");
        assert!(!ok);
    }

    #[test]
    fn test_prove_and_verify_cs_enc_accept() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let y = BigInt::from(5u32);
        let r_y = BigInt::from(7u32);
        let r_a = BigInt::from(11u32);
        let b_y = -1i8;
        let b = [1i8, -1i8, 1i8, -1i8];

        let oa = CsCommitOpening {
            a1: b[0],
            a2: b[2],
            s1: BigUint::from(13u32),
            s2: BigUint::from(17u32),
            r1: BigUint::from(19u32),
            r2: BigUint::from(23u32),
            b1: b[1],
            b2: b[3],
        };

        let cy = apply_sign_mod_n2(
            &((modpow_signed(&params.g_prime, &y, &params.n2).expect("pow")
                * modpow_signed(&params.h_prime, &r_y, &params.n2).expect("pow"))
                % &params.n2),
            b_y,
            &params.n2,
        )
        .expect("cy build");

        let ca = CsCommitment {
            c1: apply_sign_mod_n2(
                &((modpow_signed(&params.g_star, &r_a, &params.n2).expect("pow")
                    * params.g_prime.modpow(&oa.s1, &params.n2))
                    % &params.n2),
                b[0],
                &params.n2,
            )
            .expect("ca1"),
            c2: apply_sign_mod_n2(
                &((params.g_prime.modpow(&oa.s1, &params.n2) * params.h_prime.modpow(&oa.r1, &params.n2))
                    % &params.n2),
                b[1],
                &params.n2,
            )
            .expect("ca2"),
            c3: apply_sign_mod_n2(
                &((modpow_signed(&pk.k, &r_a, &params.n2).expect("pow")
                    * modpow_signed(&params.h_star, &y, &params.n2).expect("pow")
                    * params.g_prime.modpow(&oa.s2, &params.n2))
                    % &params.n2),
                b[2],
                &params.n2,
            )
            .expect("ca3"),
            c4: apply_sign_mod_n2(
                &((params.g_prime.modpow(&oa.s2, &params.n2) * params.h_prime.modpow(&oa.r2, &params.n2))
                    % &params.n2),
                b[3],
                &params.n2,
            )
            .expect("ca4"),
        };

        let proof = prove_cs_enc(&params, &pk.k, &ca, &cy, &oa, &y, &r_y, &r_a, b_y, b)
            .expect("prove enc should succeed");
        let ok = verify_cs_enc(&params, &pk.k, &ca, &cy, &proof).expect("verify enc should run");
        assert!(ok);
    }

    #[test]
    fn test_verify_cs_enc_reject_tampered_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let y = BigInt::from(3u32);
        let r_y = BigInt::from(5u32);
        let r_a = BigInt::from(7u32);
        let b_y = 1i8;
        let b = [-1i8, 1i8, -1i8, 1i8];

        let oa = CsCommitOpening {
            a1: b[0],
            a2: b[2],
            s1: BigUint::from(29u32),
            s2: BigUint::from(31u32),
            r1: BigUint::from(37u32),
            r2: BigUint::from(41u32),
            b1: b[1],
            b2: b[3],
        };

        let cy = apply_sign_mod_n2(
            &((modpow_signed(&params.g_prime, &y, &params.n2).expect("pow")
                * modpow_signed(&params.h_prime, &r_y, &params.n2).expect("pow"))
                % &params.n2),
            b_y,
            &params.n2,
        )
        .expect("cy build");

        let ca = CsCommitment {
            c1: apply_sign_mod_n2(
                &((modpow_signed(&params.g_star, &r_a, &params.n2).expect("pow")
                    * params.g_prime.modpow(&oa.s1, &params.n2))
                    % &params.n2),
                b[0],
                &params.n2,
            )
            .expect("ca1"),
            c2: apply_sign_mod_n2(
                &((params.g_prime.modpow(&oa.s1, &params.n2) * params.h_prime.modpow(&oa.r1, &params.n2))
                    % &params.n2),
                b[1],
                &params.n2,
            )
            .expect("ca2"),
            c3: apply_sign_mod_n2(
                &((modpow_signed(&pk.k, &r_a, &params.n2).expect("pow")
                    * modpow_signed(&params.h_star, &y, &params.n2).expect("pow")
                    * params.g_prime.modpow(&oa.s2, &params.n2))
                    % &params.n2),
                b[2],
                &params.n2,
            )
            .expect("ca3"),
            c4: apply_sign_mod_n2(
                &((params.g_prime.modpow(&oa.s2, &params.n2) * params.h_prime.modpow(&oa.r2, &params.n2))
                    % &params.n2),
                b[3],
                &params.n2,
            )
            .expect("ca4"),
        };

        let mut proof = prove_cs_enc(&params, &pk.k, &ca, &cy, &oa, &y, &r_y, &r_a, b_y, b)
            .expect("prove enc should succeed");
        proof.z_ra += BigInt::from(1u32);

        let ok = verify_cs_enc(&params, &pk.k, &ca, &cy, &proof).expect("verify enc should run");
        assert!(!ok);
    }

    #[test]
    fn test_prove_cs_enc_reject_invalid_sign() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut OsRng, &cs_params.n2),
        };
        let params = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");

        let ca = CsCommitment {
            c1: BigUint::one(),
            c2: BigUint::one(),
            c3: BigUint::one(),
            c4: BigUint::one(),
        };
        let oa = CsCommitOpening {
            a1: 1,
            a2: 1,
            s1: BigUint::one(),
            s2: BigUint::one(),
            r1: BigUint::one(),
            r2: BigUint::one(),
            b1: 1,
            b2: 1,
        };

        let err = prove_cs_enc(
            &params,
            &pk.k,
            &ca,
            &BigUint::one(),
            &oa,
            &BigInt::one(),
            &BigInt::one(),
            &BigInt::one(),
            0,
            [1, 1, 1, 1],
        )
        .expect_err("invalid sign should be rejected");
        assert_eq!(err, CryptoError::InvalidInput("b_y and b_i must be in {-1,+1}"));
    }

    fn ob_sign(v: i8) -> i8 {
        v
    }
}
