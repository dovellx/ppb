use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::cs::{dec_cs, enc_cs, keygen_cs, setup_cs, CsParams, CsPubKey, CsSecretKey};
use crate::error::{CryptoError, CryptoResult};
use crate::math::abs_qr_rep;
use crate::pok::{CamenischShoupCiphertext, CiphertextPolynomial, Scalar};

/// HEC 全局参数。
///
/// 这里直接复用现有 CS 参数作为 `hecpar`：
/// 1. `cs_params` 决定明文模数 `n` 与密文模数 `n^2`；
/// 2. HECenc 中所有“多项式系数运算”都在 `Z_n` 上进行；
/// 3. 随后再把系数作为 CS 明文加密。
#[derive(Debug, Clone)]
pub struct HecParams {
    pub cs_params: CsParams,
}

/// 论文记号 `f_{n,k}` 的工程化承载结构。
///
/// - `n`: 名单规模（应与输入 `x` 的长度一致）
/// - `k`: k是用户属性yat的比特长度
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HecFunctionKey {
    pub n: usize,
    pub k: usize,
}

/// HECenc 的公开输出 X = (pkAH, A1, ..., A_{n+1})。
///
/// 为了后续直接对接 `Algorithm 2`，这里额外封装了 `CiphertextPolynomial`。
#[derive(Debug, Clone)]
pub struct HecPublicPackage {
    pub pk_ah: CsPubKey,
    pub encrypted_coeffs: Vec<CamenischShoupCiphertext>,
    pub polynomial: CiphertextPolynomial,
}

/// HECenc 的私有审计上下文 d = (skE, fk, x)。
#[derive(Debug, Clone)]
pub struct HecAuditData {
    pub sk_e: CsSecretKey,
    pub fk: HecFunctionKey,
    pub x: Vec<Scalar>,
}

/// HECenc 总输出：(X, d)。
#[derive(Debug, Clone)]
pub struct HecEncOutput {
    pub x_public: HecPublicPackage,
    pub d_audit: HecAuditData,
}

/// HECeval 的用户输入 y = (y_id, y_at)。
///
/// 字段语义：
/// 1. `y_id`: 身份标识（用于代入名单多项式）
/// 2. `y_at`: 审计/追踪种子
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HecEvalInput {
    pub y_id: Scalar,
    pub y_at: Scalar,
}

/// HECeval 的随机性输入 r^Z = (r_id, r_at, r1, r2, r3)。
///
/// 对应算法步骤：
/// 1. `r_id`, `r_at` 用于加密 `Y_id`, `Y_at`；
/// 2. `r1`, `r2` 用于盲化 `E` 并混入 `y_id/y_at`；
/// 3. `r3` 用于 Non-Frameability 项，必须非零。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HecEvalRandomness {
    pub rid: Scalar,
    pub rat: Scalar,
    pub r1: Scalar,
    pub r2: Scalar,
    pub r3: Scalar,
}

/// HECeval 输出 Z = (Z_id, Z_at, Z_nf)。
#[derive(Debug, Clone)]
pub struct HecEvalOutput {
    pub z_id: CamenischShoupCiphertext,
    pub z_at: CamenischShoupCiphertext,
    pub z_nf: CamenischShoupCiphertext,
}

/// 初始化 HEC 参数（内部调用 CS.Setup）。
pub fn setup_hec(security_bits: usize) -> CryptoResult<HecParams> {
    let cs_params = setup_cs(security_bits)?;
    Ok(HecParams { cs_params })
}

/// 在 `Z_n` 中采样一个非零随机标量。
fn sample_nonzero_scalar_mod_n(n: &BigUint) -> CryptoResult<BigUint> {
    if n <= &BigUint::one() {
        return Err(CryptoError::InvalidInput("n must be > 1"));
    }
    let mut rng = OsRng;
    loop {
        let s = rng.gen_biguint_below(n);
        if !s.is_zero() {
            return Ok(s);
        }
    }
}

/// 使用指定随机数执行 CS 加密：Enc(pk, m; r)。
///
/// 说明：
/// 1. 标准 `enc_cs` 会内部随机采样 r；
/// 2. HECeval 需要显式使用输入随机数 `(rid, rat)`，因此单独实现此 helper；
/// 3. 为保持与全库一致，结果仍映射到 |QR_{n^2}| 代表元。
fn enc_cs_with_randomness(
    params: &CsParams,
    pk: &CsPubKey,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<CamenischShoupCiphertext> {
    if m >= &params.n {
        return Err(CryptoError::InvalidInput("message must be in [0, n)"));
    }
    if params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    // 工程实现里把外部输入随机数映射到 Z_n，保证同态公式在明文模 n 上闭合。
    let r_mod = r % &params.n;

    let c0_raw = params.g.modpow(&r_mod, &params.n2);
    let c0 = abs_qr_rep(&c0_raw, &params.n2);

    let kr = pk.k.modpow(&r_mod, &params.n2);
    let hm = params.h.modpow(m, &params.n2);
    let c1_raw = (kr * hm) % &params.n2;
    let c1 = abs_qr_rep(&c1_raw, &params.n2);

    Ok(CamenischShoupCiphertext { c0, c1 })
}

/// CS 密文同态加法：Enc(a) ⊕ Enc(b) = Enc(a+b)。
fn cs_homomorphic_add(
    left: &CamenischShoupCiphertext,
    right: &CamenischShoupCiphertext,
    n2: &BigUint,
) -> CamenischShoupCiphertext {
    CamenischShoupCiphertext {
        c0: (&left.c0 * &right.c0) % n2,
        c1: (&left.c1 * &right.c1) % n2,
    }
}

/// CS 密文同态标量乘法：k ⊙ Enc(m) = Enc(k*m)。
fn cs_homomorphic_scalar_mul(
    value: &CamenischShoupCiphertext,
    scalar: &BigUint,
    n2: &BigUint,
) -> CamenischShoupCiphertext {
    CamenischShoupCiphertext {
        c0: value.c0.modpow(scalar, n2),
        c1: value.c1.modpow(scalar, n2),
    }
}

/// 把根集合 `x_1..x_n` 展开为多项式系数（升幂顺序），并在 `Z_n` 下缩放随机掩码 `s`。
///
/// 目标多项式：
/// P(chi) = s * Π_{i=1..n} (chi - x_i)
///
/// 返回系数向量：
/// [P_0, P_1, ..., P_n]，对应 `P_0 + P_1*chi + ... + P_n*chi^n`。
///
/// 实现细节：
/// 1. 采用迭代乘法，每次把当前多项式乘以 `(chi - x_i)`；
/// 2. 所有加减乘都在 `mod n` 下进行；
/// 3. 减法通过 `(-x_i) mod n = (n - (x_i mod n)) mod n` 实现。
pub fn expand_roots_to_coefficients_mod_n(x: &[Scalar], s: &Scalar, n: &BigUint) -> CryptoResult<Vec<Scalar>> {
    if n.is_zero() {
        return Err(CryptoError::InvalidInput("modulus n must be non-zero"));
    }

    // 初始多项式为常数 1。
    let mut coeffs = vec![BigUint::one()];

    for root in x {
        let root_mod = root % n;
        let minus_root = if root_mod.is_zero() {
            BigUint::zero()
        } else {
            (n - &root_mod) % n
        };

        let mut next = vec![BigUint::zero(); coeffs.len() + 1];
        for (j, coeff) in coeffs.iter().enumerate() {
            // 常数侧：a_j * (-x_i)
            next[j] = (&next[j] + ((coeff * &minus_root) % n)) % n;
            // 一次项提升：a_j * chi
            next[j + 1] = (&next[j + 1] + (coeff % n)) % n;
        }
        coeffs = next;
    }

    // 全体系数乘以随机掩码 s。
    let s_mod = s % n;
    for coeff in &mut coeffs {
        *coeff = ((&*coeff) * &s_mod) % n;
    }

    Ok(coeffs)
}

/// HECenc(hecpar, f_{n,k}, x) 实现。
///
/// 对应算法流程：
/// 1. `(pk_AH, sk_E) <- KeyGen(1^lambda)`：复用 `CS.KeyGen`；
/// 2. `s <-$ M_pk_AH`：在 `Z_n` 中采样非零随机数；
/// 3. `P <- s * Π(chi - x_i)`：在 `Z_n` 中展开为系数；
/// 4. 逐系数加密 `A_i <- Enc(pk_AH, P_i)`；
/// 5. 返回公开包 `X` 与审计上下文 `d`。
pub fn hec_enc(hecpar: &HecParams, fk: &HecFunctionKey, x: &[Scalar]) -> CryptoResult<HecEncOutput> {
    if x.is_empty() {
        return Err(CryptoError::InvalidInput("x must be non-empty"));
    }
    if fk.n != x.len() {
        return Err(CryptoError::InvalidInput("fk.n must equal x.len()"));
    }

    // Step 1: 生成 AH 密钥对。
    let (pk_ah, sk_e) = keygen_cs(&hecpar.cs_params)?;

    // Step 2: 采样随机掩码 s。
    let s = sample_nonzero_scalar_mod_n(&hecpar.cs_params.n)?;

    // Step 3: 在 Z_n 下展开名单多项式系数。
    let coeffs = expand_roots_to_coefficients_mod_n(x, &s, &hecpar.cs_params.n)?;

    // Step 4: 加密每个系数（包括 0 系数，也必须走正式加密流程）。
    let mut encrypted_coeffs = Vec::with_capacity(coeffs.len());
    for coeff in &coeffs {
        let enc = enc_cs(&hecpar.cs_params, &pk_ah, coeff)?;
        encrypted_coeffs.push(enc);
    }

    let polynomial = CiphertextPolynomial::new(encrypted_coeffs.clone(), &hecpar.cs_params.n2)?;

    Ok(HecEncOutput {
        x_public: HecPublicPackage {
            pk_ah,
            encrypted_coeffs,
            polynomial,
        },
        d_audit: HecAuditData {
            sk_e,
            fk: fk.clone(),
            x: x.to_vec(),
        },
    })
}

/// HECeval(hecpar, f_{n,k}, ell, X, y; r^Z) 实现。
///
/// 直接对应算法：
/// 1. parse X=(pkAH, A1..A_{n+1}), y=(y_id,y_at), r^Z=(r_id,r_at,r1,r2,r3)
/// 2. if r3 == 0 return ⊥
/// 3. E <- sum_i (A_i ⊙ y_id^i) = Enc(P(y_id))
/// 4. Y_id <- Enc(pkAH, y_id; r_id)
/// 5. Y_at <- Enc(pkAH, y_at; r_at)
/// 6. Z_id <- (r1 ⊙ E) ⊕ Y_id
/// 7. Z_at <- (r2 ⊙ E) ⊕ Y_at
/// 8. Z_nf <- r3 ⊙ E
/// 9. return Z=(Z_id, Z_at, Z_nf)
///
/// 工程细节：
/// 1. 为保持明文语义一致，`y` 与 `r^Z` 全部先映射到 `Z_n`；
/// 2. `ell` 在当前 HEC_DIRECT 路径中只做接口保留，不参与代数计算；
/// 3. 多项式评估严格通过 `CiphertextPolynomial::evaluate` 完成。
pub fn hec_eval(
    hecpar: &HecParams,
    fk: &HecFunctionKey,
    _ell: usize,
    x_public: &HecPublicPackage,
    y: &HecEvalInput,
    r_z: &HecEvalRandomness,
) -> CryptoResult<HecEvalOutput> {
    if fk.n + 1 != x_public.encrypted_coeffs.len() {
        return Err(CryptoError::InvalidInput(
            "public package coefficient count must be fk.n + 1",
        ));
    }

    let n = &hecpar.cs_params.n;
    let n2 = &hecpar.cs_params.n2;

    // parse y 与 r^Z，并映射到明文环 Z_n。
    let y_id = &y.y_id % n;
    let y_at = &y.y_at % n;
    let rid = &r_z.rid % n;
    let rat = &r_z.rat % n;
    let r1 = &r_z.r1 % n;
    let r2 = &r_z.r2 % n;
    let r3 = &r_z.r3 % n;

    // 防御性检查：r3 绝对不能为 0。
    if r3.is_zero() {
        return Err(CryptoError::InvalidInput("r3 must be non-zero in Z_n"));
    }

    // Step 3: E <- Enc(P(y_id))。
    // 注意这里按算法语义从 X=(A1..A_{n+1}) 解析构建多项式再 evaluate。
    let poly_from_x = CiphertextPolynomial::new(x_public.encrypted_coeffs.clone(), n2)?;
    let e = poly_from_x.evaluate(&y_id);

    // Step 4 & 5: 独立加密 y_id / y_at（使用外部给定随机数）。
    let y_id_enc = enc_cs_with_randomness(&hecpar.cs_params, &x_public.pk_ah, &y_id, &rid)?;
    let y_at_enc = enc_cs_with_randomness(&hecpar.cs_params, &x_public.pk_ah, &y_at, &rat)?;

    // Step 6: Z_id <- (r1 ⊙ E) ⊕ Y_id。
    let z_id = cs_homomorphic_add(&cs_homomorphic_scalar_mul(&e, &r1, n2), &y_id_enc, n2);

    // Step 7: Z_at <- (r2 ⊙ E) ⊕ Y_at。
    let z_at = cs_homomorphic_add(&cs_homomorphic_scalar_mul(&e, &r2, n2), &y_at_enc, n2);

    // Step 8: Z_nf <- r3 ⊙ E。
    let z_nf = cs_homomorphic_scalar_mul(&e, &r3, n2);

    Ok(HecEvalOutput { z_id, z_at, z_nf })
}

/// HECdec(hecpar, d, Z) 实现。
///
/// 对应算法流程：
/// 1. parse d=(sk_E, f_{n,k}, x) 与 Z=(Z_id, Z_at, Z_nf)
/// 2. y'_id <- Dec(sk_E, Z_id)
/// 3. y'_at <- Dec(sk_E, Z_at)
/// 4. y'    <- Dec(sk_E, Z_nf)
/// 5. 若 y' != g(0)（在当前实现中即 0），返回空
/// 6. 遍历名单 x，若存在 y_id 满足 g(y_id)=y'_id，则返回 (y'_id, y'_at)
/// 7. 否则返回空
///
/// 说明：
/// 1. 当前工程取 g 为 `Z_n` 上恒等映射，因此 g(0)=0；
/// 2. 匹配时使用 `y_id mod n` 与解密结果比较，避免输入列表元素超出 n 时语义不一致；
/// 3. 若审计上下文 `fk.n` 与名单长度不一致，直接返回错误，防止上下文被错误拼接。
pub fn hec_dec(
    hecpar: &HecParams,
    d_audit: &HecAuditData,
    z: &HecEvalOutput,
) -> CryptoResult<Option<HecEvalInput>> {
    if d_audit.fk.n != d_audit.x.len() {
        return Err(CryptoError::InvalidInput("audit context fk.n must equal x.len()"));
    }

    let n = &hecpar.cs_params.n;

    // Step 2~4: 解密三项候选值。
    let y_prime_id = dec_cs(&hecpar.cs_params, &d_audit.sk_e, &z.z_id)?;
    let y_prime_at = dec_cs(&hecpar.cs_params, &d_audit.sk_e, &z.z_at)?;
    let y_prime_nf = dec_cs(&hecpar.cs_params, &d_audit.sk_e, &z.z_nf)?;

    // Step 5~6: Non-Frameability 判定（g(0) = 0）。
    if !y_prime_nf.is_zero() {
        return Ok(None);
    }

    // Step 7~9: 在名单中匹配身份。
    for yid in &d_audit.x {
        if (yid % n) == y_prime_id {
            return Ok(Some(HecEvalInput {
                y_id: y_prime_id,
                y_at: y_prime_at,
            }));
        }
    }

    // Step 10: 未匹配到合法身份，返回空。
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expand_roots_to_coefficients_mod_n_small_example() {
        let n = BigUint::from(97u32);
        let x = vec![BigUint::from(3u32), BigUint::from(5u32)];
        let s = BigUint::from(2u32);

        // 2 * (chi-3)(chi-5) = 2 * (chi^2 - 8chi + 15)
        // 在 Z_97 中：[-8 mod 97 = 89]
        // 系数（升幂）：[30, 81, 2]
        let coeffs = expand_roots_to_coefficients_mod_n(&x, &s, &n).expect("expansion should succeed");
        assert_eq!(coeffs, vec![BigUint::from(30u32), BigUint::from(81u32), BigUint::from(2u32)]);
    }

    #[test]
    fn test_hec_enc_output_shape() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 3, k: 1 };
        let x = vec![BigUint::from(4u32), BigUint::from(7u32), BigUint::from(9u32)];

        let out = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        assert_eq!(out.x_public.encrypted_coeffs.len(), x.len() + 1);
        assert_eq!(out.x_public.polynomial.len(), x.len() + 1);
        assert_eq!(out.d_audit.fk, fk);
        assert_eq!(out.d_audit.x, x);
    }

    #[test]
    fn test_hec_enc_polynomial_evaluates_to_zero_on_roots_after_decrypt() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];

        let out = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        for root in &out.d_audit.x {
            let eval_ct = out.x_public.polynomial.evaluate(root);
            let m = dec_cs(&hecpar.cs_params, &out.d_audit.sk_e, &eval_ct).expect("decrypt should succeed");
            assert_eq!(m, BigUint::zero());
        }
    }

    #[test]
    fn test_plain_p_of_chi_matches_decrypted_ciphertext_evaluate() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let (pk, sk) = keygen_cs(&hecpar.cs_params).expect("keygen should succeed");

        let roots = vec![BigUint::from(4u32), BigUint::from(7u32), BigUint::from(9u32)];
        let s = BigUint::from(13u32);
        let coeffs = expand_roots_to_coefficients_mod_n(&roots, &s, &hecpar.cs_params.n)
            .expect("expansion should succeed");

        let mut encrypted_coeffs = Vec::with_capacity(coeffs.len());
        for coeff in &coeffs {
            encrypted_coeffs.push(enc_cs(&hecpar.cs_params, &pk, coeff).expect("enc coeff should succeed"));
        }
        let poly = CiphertextPolynomial::new(encrypted_coeffs, &hecpar.cs_params.n2).expect("poly should build");

        let chis = vec![BigUint::from(2u32), BigUint::from(5u32), BigUint::from(11u32)];
        for chi in chis {
            // 明文侧：P(chi) = sum_i coeff_i * chi^i (mod n)
            let mut expected = BigUint::zero();
            let mut chi_pow = BigUint::one();
            for coeff in &coeffs {
                expected = (expected + ((coeff * &chi_pow) % &hecpar.cs_params.n)) % &hecpar.cs_params.n;
                chi_pow = (&chi_pow * &chi) % &hecpar.cs_params.n;
            }

            // 密文侧：evaluate(chi) 后解密，比较明文结果。
            let eval_ct = poly.evaluate(&chi);
            let got = dec_cs(&hecpar.cs_params, &sk, &eval_ct).expect("decrypt should succeed");
            assert_eq!(got, expected);
        }
    }

    #[test]
    fn test_hec_eval_rejects_zero_r3() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(3u32),
            y_at: BigUint::from(21u32),
        };
        let r_z = HecEvalRandomness {
            rid: BigUint::from(2u32),
            rat: BigUint::from(3u32),
            r1: BigUint::from(5u32),
            r2: BigUint::from(7u32),
            r3: BigUint::zero(),
        };

        let err = hec_eval(&hecpar, &fk, 1, &enc.x_public, &y, &r_z).expect_err("r3=0 must be rejected");
        assert_eq!(err, CryptoError::InvalidInput("r3 must be non-zero in Z_n"));
    }

    #[test]
    fn test_hec_eval_hit_case_recovers_identity_and_seed() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        // 命中名单：y_id = 5 是根，故 P(y_id)=0。
        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(42u32),
        };
        let r_z = HecEvalRandomness {
            rid: BigUint::from(13u32),
            rat: BigUint::from(17u32),
            r1: BigUint::from(19u32),
            r2: BigUint::from(23u32),
            r3: BigUint::from(29u32),
        };

        let out = hec_eval(&hecpar, &fk, 1, &enc.x_public, &y, &r_z).expect("hec eval should succeed");

        let z_id_plain = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_id).expect("decrypt zid should succeed");
        let z_at_plain = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_at).expect("decrypt zat should succeed");
        let z_nf_plain = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_nf).expect("decrypt znf should succeed");

        assert_eq!(z_id_plain, y.y_id % &hecpar.cs_params.n);
        assert_eq!(z_at_plain, y.y_at % &hecpar.cs_params.n);
        assert_eq!(z_nf_plain, BigUint::zero());
    }

    #[test]
    fn test_hec_eval_non_hit_case_matches_formula() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 3, k: 1 };
        let x = vec![BigUint::from(4u32), BigUint::from(7u32), BigUint::from(9u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        // 不命中名单：8 不在 roots 中。
        let y = HecEvalInput {
            y_id: BigUint::from(8u32),
            y_at: BigUint::from(31u32),
        };
        let r_z = HecEvalRandomness {
            rid: BigUint::from(3u32),
            rat: BigUint::from(5u32),
            r1: BigUint::from(11u32),
            r2: BigUint::from(13u32),
            r3: BigUint::from(17u32),
        };

        let out = hec_eval(&hecpar, &fk, 1, &enc.x_public, &y, &r_z).expect("hec eval should succeed");

        let n = &hecpar.cs_params.n;
        let y_id_mod = &y.y_id % n;
        let y_at_mod = &y.y_at % n;
        let r1_mod = &r_z.r1 % n;
        let r2_mod = &r_z.r2 % n;
        let r3_mod = &r_z.r3 % n;

        let poly = CiphertextPolynomial::new(enc.x_public.encrypted_coeffs.clone(), &hecpar.cs_params.n2)
            .expect("poly build should succeed");
        let e_ct = poly.evaluate(&y_id_mod);
        let e_plain = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &e_ct).expect("decrypt E should succeed");

        let expected_zid = ((&r1_mod * &e_plain) + &y_id_mod) % n;
        let expected_zat = ((&r2_mod * &e_plain) + &y_at_mod) % n;
        let expected_znf = (&r3_mod * &e_plain) % n;

        let got_zid = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_id).expect("decrypt zid should succeed");
        let got_zat = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_at).expect("decrypt zat should succeed");
        let got_znf = dec_cs(&hecpar.cs_params, &enc.d_audit.sk_e, &out.z_nf).expect("decrypt znf should succeed");

        assert_eq!(got_zid, expected_zid);
        assert_eq!(got_zat, expected_zat);
        assert_eq!(got_znf, expected_znf);
    }

    #[test]
    fn test_hec_dec_hit_returns_identity_and_seed() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(42u32),
        };
        let r_z = HecEvalRandomness {
            rid: BigUint::from(13u32),
            rat: BigUint::from(17u32),
            r1: BigUint::from(19u32),
            r2: BigUint::from(23u32),
            r3: BigUint::from(29u32),
        };
        let z = hec_eval(&hecpar, &fk, 1, &enc.x_public, &y, &r_z).expect("hec eval should succeed");

        let out = hec_dec(&hecpar, &enc.d_audit, &z).expect("hec dec should succeed");
        let recovered = out.expect("hit case should recover identity");

        assert_eq!(recovered.y_id, y.y_id % &hecpar.cs_params.n);
        assert_eq!(recovered.y_at, y.y_at % &hecpar.cs_params.n);
    }

    #[test]
    fn test_hec_dec_non_hit_returns_none() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        // y_id=8 不在名单中，理论上 Znf 解密不会是 0。
        let y = HecEvalInput {
            y_id: BigUint::from(8u32),
            y_at: BigUint::from(42u32),
        };
        let r_z = HecEvalRandomness {
            rid: BigUint::from(3u32),
            rat: BigUint::from(5u32),
            r1: BigUint::from(7u32),
            r2: BigUint::from(11u32),
            r3: BigUint::from(13u32),
        };
        let z = hec_eval(&hecpar, &fk, 1, &enc.x_public, &y, &r_z).expect("hec eval should succeed");

        let out = hec_dec(&hecpar, &enc.d_audit, &z).expect("hec dec should succeed");
        assert!(out.is_none());
    }

    #[test]
    fn test_hec_dec_returns_none_if_nf_is_zero_but_identity_not_in_list() {
        let hecpar = setup_hec(64).expect("setup hec should succeed");
        let fk = HecFunctionKey { n: 2, k: 1 };
        let x = vec![BigUint::from(5u32), BigUint::from(11u32)];
        let enc = hec_enc(&hecpar, &fk, &x).expect("hec enc should succeed");

        // 构造一个“异常但可解密”的 Z：
        // 1) Znf 明确加密 0，使第一层判定通过；
        // 2) Zid 解密为一个不在名单里的身份；
        // 3) 预期算法在 Step 7~10 返回空。
        let fake_id = BigUint::from(21u32);
        let fake_at = BigUint::from(33u32);

        let z = HecEvalOutput {
            z_id: enc_cs_with_randomness(
                &hecpar.cs_params,
                &enc.x_public.pk_ah,
                &(fake_id.clone() % &hecpar.cs_params.n),
                &BigUint::from(2u32),
            )
            .expect("zid enc should succeed"),
            z_at: enc_cs_with_randomness(
                &hecpar.cs_params,
                &enc.x_public.pk_ah,
                &(fake_at % &hecpar.cs_params.n),
                &BigUint::from(3u32),
            )
            .expect("zat enc should succeed"),
            z_nf: enc_cs_with_randomness(
                &hecpar.cs_params,
                &enc.x_public.pk_ah,
                &BigUint::zero(),
                &BigUint::from(5u32),
            )
            .expect("znf enc should succeed"),
        };

        let out = hec_dec(&hecpar, &enc.d_audit, &z).expect("hec dec should succeed");
        assert!(out.is_none());
    }
}
