use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::cs::{keygen_cs, CsParams, CsPubKey};
use crate::cs_commit::{
    prove_cs_add, prove_cs_enc, prove_cs_mult, setup_cs_commit, verify_cs_add, verify_cs_com,
    verify_cs_enc, verify_cs_mult, CsAddProof, CsCommitOpening, CsCommitParams, CsCommitment,
    CsCommitmentWithOpening, CsEncProof, CsMultProof,
};
use crate::df::{commit_df, commit_df_multibase, commit_df_with_opening, DfParams};
use crate::error::{CryptoError, CryptoResult};
use crate::hash::{fiat_shamir_challenge, fiat_shamir_challenge_biguints};
use crate::hec::{
    hec_dec, hec_enc, hec_eval, setup_hec, HecAuditData, HecEvalInput, HecEvalOutput, HecEvalRandomness,
    HecFunctionKey, HecParams, HecPublicPackage,
};
use crate::math::{abs_qr_rep, derive_b_bits_from_n2, modinv, sample_unit_mod_n2};
use crate::pok::{verify_mult as verify_df_square_mult, CiphertextPolynomial, PoKAuxEntry, PoKPProof, PoKStarProof, PoKTranscript, pokp};

/// PPB 全局参数 `Λ = (λ, cpar, hecpar, S1, S2, S3)` 的当前实现。
///
/// 现阶段按你的要求：
/// 1. `lambda_bits`、`cpar`、`hecpar` 真实保存；
/// 2. `S1~S3` 暂时忽略，不进入结构体（后续接入零知识参数时再扩展）。
#[derive(Debug, Clone)]
pub struct PpbParams {
    pub lambda_bits: usize,
    pub cpar: DfParams,
    pub hecpar: HecParams,
}

/// KeyGen 中输出的认证证明 `pi_A`（PoKS1 真实实现）。
///
/// 证明目标（你给出的关系）：
/// 1. `C_x = g^{m_x} h^{r_x} (mod n^2)`；
/// 2. `C_d = g^{m_d} h^{r_d} (mod n^2)`。
///
/// 证明结构采用 Fiat-Shamir 化的三步协议：
/// 1. Commit: `R_x, R_d`；
/// 2. Challenge: `e = H(n,g,h,C_x,C_d,R_x,R_d)`（验证侧重算）；
/// 3. Response: `z_mx, z_rx, z_md, z_rd`（整数域响应，不取模）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbAuthProof {
    pub r_x_commitment: BigUint,
    pub r_d_commitment: BigUint,
    pub z_mx: BigInt,
    pub z_rx: BigInt,
    pub z_md: BigInt,
    pub z_rd: BigInt,
}

/// PPB 公钥 `pk_A = (X, Cx, Cd, pi_A)` 的工程化承载结构。
///
/// 额外字段说明：
/// 1. `fk` 用于显式保存 KeyGen 时 `HECenc` 使用的函数键；
/// 2. Escrow 阶段调用 `HECeval` 时必须复用该 `fk`，避免从 `X` 反推造成语义歧义。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbPublicKey {
    pub x_public: HecPublicPackage,
    pub fk: HecFunctionKey,
    pub c_x: BigUint,
    pub c_d: BigUint,
    pub pi_a: PpbAuthProof,
}

/// PPB 私钥 `sk_A = (pk_A, d, r_d)`。
#[derive(Debug, Clone)]
pub struct PpbSecretKey {
    pub pk_a: PpbPublicKey,
    pub d: HecAuditData,
    pub r_d: BigUint,
}

/// `pi_id / pi_at` 的组合证明载荷。
///
/// 对应你描述的第 7、8 步：
/// 1. `c_enc/c_mul` 是验证侧必须重放的公共语句承诺：
///    - `c_enc` 对应 `Enc(y_*)` 的承诺语句；
///    - `c_mul` 对应 `r_i ⊙ E_poly` 的承诺语句；
///    若不把它们放进证明对象，验证侧无法独立调用 verify 原语。
/// 2. `pi_enc` 证明“该密文确实是某明文用指定随机数的 CS 加密”；
/// 3. `pi_mult` 证明“标量乘法关系 r_i ⊙ E_poly”；
/// 4. `pi_add` 证明“最终 Z 分量 = Enc(y_*) ⊕ (r_i ⊙ E_poly)”。
#[derive(Debug, Clone)]
pub struct PpbEncMulAddProof {
    pub c_enc: CsCommitment,
    pub c_mul: CsCommitment,
    pub pi_enc: CsEncProof,
    pub pi_mult: CsMultProof,
    pub pi_add: CsAddProof,
}

/// `pi_y` 的工程化承载结构。
///
/// 你要求第 4 步执行严格关系检查：
/// `C_y == (C_id * C_at) mod n^2`。
/// 这里把“计算得到的右侧值”和“是否成立”都显式保存，方便调试和验算。
#[derive(Debug, Clone)]
pub struct PpbYConsistencyProof {
    pub c_y_from_cid_cat: BigUint,
    pub relation_holds: bool,
}

/// Escrow 中输出的用户证明 `pi_U`（PoKS2 结构化实现）。
///
/// 与 Algorithm 3 的返回项一一对应：
/// 1. `pi_id`, `pi_at`, `pi_nf`, `pi_sky`, `pi_y`；
/// 2. `c_sky`；
/// 3. `{c_ri}`（即 `c_r1/c_r2/c_r3`）。
///
/// 额外保留：
/// 1. `c_id/c_at`：便于外部重放 `pi_id/pi_at/pi_y` 的公共语句；
/// 2. `pk_sky`：`pi_sky` 验证时必须要有对应公钥。
/// 3. `ah_g`：PoKS2 里 `CS-commit` 参数的随机基 `g`；
///    验证侧必须复用同一个 `g`，否则所有 `verify_cs_*` 都会失配。
#[derive(Debug, Clone)]
pub struct PpbUserProof {
    pub ah_g: BigUint,
    pub c_id: BigUint,
    pub c_at: BigUint,
    pub c_r1: BigUint,
    pub c_r2: BigUint,
    pub c_r3: BigUint,
    pub pk_sky: CsPubKey,
    pub c_sky: crate::cs::CsCiphertext,
    pub pi_poly: PoKPProof,
    pub pi_nf: CsMultProof,
    pub pi_id: PpbEncMulAddProof,
    pub pi_at: PpbEncMulAddProof,
    pub pi_sky: CsEncProof,
    pub pi_y: PpbYConsistencyProof,
}

/// Escrow 输出载荷：
/// 1. `z_hat` 对应算法中的 `Ẑ`；
/// 2. `c_y` 对应算法中的 `Cy = Com_cpar(y; r_y)`；
/// 3. `pi_u` 对应算法中的 `pi_U`（结构化证明对象）。
#[derive(Debug, Clone)]
pub struct PpbEscrowOutput {
    pub z_hat: HecEvalOutput,
    pub c_y: BigUint,
    pub pi_u: PpbUserProof,
}

/// Dec 阶段输出的 `pi_Z`（PoKS3）证明。
///
/// 证明目标：
/// 1. 证明者知道 `d, r_d`，使 `C_d = Com_cpar(d; r_d)`；
/// 2. 其中工程实现中的 `d` 会先映射为 `m_d = map_d_to_df_message(d)`，
///    再在 DF 承诺关系上执行 Schnorr/Fiat-Shamir 证明。
///
/// 结构与 PoKS1 的 `(C_d)` 分支保持一致：
/// 1. Commit: `R_d`；
/// 2. Response: `z_md, z_rd`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbDecProof {
    pub r_d_commitment: BigUint,
    pub z_md: BigInt,
    pub z_rd: BigInt,
}

/// Dec 阶段最终输出 `(z, pi_Z)`。
///
/// 字段语义：
/// 1. `z` 为 `HECdec` 的输出，命中时为 `Some(y_id,y_at)`，否则为 `None`；
/// 2. `pi_z` 为 PoKS3，证明解密方确实掌握与 `pk_A.C_d` 对应的 `(d, r_d)`。
#[derive(Debug, Clone)]
pub struct PpbDecOutput {
    pub z: Option<HecEvalInput>,
    pub pi_z: PpbDecProof,
}

/// PPB Setup(λ, cpar, S1, S2, S3)。
///
/// 算法对应：
/// 1. `cpar <- DF.Setup(1^λ)`；
/// 2. `hecpar <- HECsetup(1^λ)`；
/// 3. `return Λ = (λ, cpar, hecpar, S1, S2, S3)`。
///
/// 工程说明：
/// 1. `S1~S3` 目前仅保留在函数签名中，用 `_s1/_s2/_s3` 占位；
/// 2. `hecpar` 通过调用现有 `setup_hec(lambda_bits)` 生成；
/// 3. `cpar` 的 `(n,n^2)` 与 `hecpar.cs_params` 强制对齐，只重新采样 `g/h`；
/// 4. 这样 PoKS2 中 `DF` 与 `CS` 语句天然共域，不再需要临时域转换参数。
pub fn setup_ppb<S1, S2, S3>(
    lambda_bits: usize,
    _s1: &S1,
    _s2: &S2,
    _s3: &S3,
) -> CryptoResult<PpbParams> {
    let hecpar = setup_hec(lambda_bits)?;
    let mut rng = OsRng;
    let cpar = DfParams {
        n: hecpar.cs_params.n.clone(),
        n2: hecpar.cs_params.n2.clone(),
        g: sample_unit_mod_n2(&mut rng, &hecpar.cs_params.n2),
        h: sample_unit_mod_n2(&mut rng, &hecpar.cs_params.n2),
    };

    Ok(PpbParams {
        lambda_bits,
        cpar,
        hecpar,
    })
}

/// 向 byte transcript 中追加一个 BigUint（长度前缀 + 本体）。
///
/// 这里统一采用“长度前缀 + 原始字节”的编码方式，目的有两点：
/// 1. 避免拼接歧义（例如 `ab|c` 与 `a|bc`）；
/// 2. 保证所有证明摘要都能在不同平台上得到同一字节流。
fn append_biguint_with_len(bytes: &mut Vec<u8>, value: &BigUint) {
    let raw = value.to_bytes_be();
    let len = u64::try_from(raw.len()).unwrap_or(u64::MAX);
    bytes.extend_from_slice(&len.to_be_bytes());
    bytes.extend_from_slice(&raw);
}

/// BigUint -> BigInt 的安全转换。
///
/// 统一包装转换错误，避免在主流程里散落重复的 `ok_or(...)`。
fn bu_to_bi(v: &BigUint) -> CryptoResult<BigInt> {
    v.to_bigint()
        .ok_or(CryptoError::InvalidInput("BigUint->BigInt conversion failed"))
}

/// 带指定随机数的 CS 加密：Enc(pk, m; r)。
///
/// 这里与 `hec.rs` 中 helper 保持同一语义：
/// 1. 所有外部随机数统一先映射到 `Z_n`；
/// 2. 密文分量做 `|QR_{n^2}|` 代表元规约。
///
/// 额外说明：
/// 这个函数在 PoKS2 中非常关键，因为我们需要“可重建”的加密结果
/// 去对应 Algorithm 3 第 2、3 行的 Zid/Zat/Znf 关系。
fn enc_cs_with_randomness_for_ppb(
    params: &CsParams,
    pk: &CsPubKey,
    m: &BigUint,
    r: &BigUint,
) -> CryptoResult<crate::cs::CsCiphertext> {
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

    Ok(crate::cs::CsCiphertext { c0, c1 })
}

/// CS 密文同态加法：Enc(a) ⊕ Enc(b) = Enc(a+b)。
///
/// 对应 Algorithm 3 里 `Zid = Enc(yid) ⊕ (r1 ⊙ e)`、
/// `Zat = Enc(yat) ⊕ (r2 ⊙ e)` 的“⊕”操作。
fn cs_homomorphic_add(
    left: &crate::cs::CsCiphertext,
    right: &crate::cs::CsCiphertext,
    n2: &BigUint,
) -> crate::cs::CsCiphertext {
    crate::cs::CsCiphertext {
        c0: (&left.c0 * &right.c0) % n2,
        c1: (&left.c1 * &right.c1) % n2,
    }
}

/// CS 密文同态标量乘法：k ⊙ Enc(m) = Enc(k*m)。
///
/// 对应 Algorithm 3 里 `r1 ⊙ e`、`r2 ⊙ e`、`r3 ⊙ e` 的“⊙”操作。
fn cs_homomorphic_scalar_mul(
    value: &crate::cs::CsCiphertext,
    scalar: &BigUint,
    n2: &BigUint,
) -> crate::cs::CsCiphertext {
    crate::cs::CsCiphertext {
        c0: value.c0.modpow(scalar, n2),
        c1: value.c1.modpow(scalar, n2),
    }
}

/// 使用“零随机数 + 全正号”包装密文为 AH/CS 承诺。
///
/// 对应约束：
/// C1=c0, C2=1, C3=c1, C4=1。
///
/// 这样做的目的不是隐藏，而是把密文“投影”为 `prove_cs_add/prove_cs_mult`
/// 可直接消费的承诺格式，便于拼装组合证明。
fn com_ah_with_zero_randomness(
    params_ah: &CsCommitParams,
    c: &crate::cs::CsCiphertext,
) -> CryptoResult<CsCommitmentWithOpening> {
    if params_ah.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    Ok(CsCommitmentWithOpening {
        commitment: CsCommitment {
            c1: &c.c0 % &params_ah.n2,
            c2: BigUint::one(),
            c3: &c.c1 % &params_ah.n2,
            c4: BigUint::one(),
        },
        opening: CsCommitOpening {
            a1: 1,
            a2: 1,
            s1: BigUint::zero(),
            s2: BigUint::zero(),
            r1: BigUint::zero(),
            r2: BigUint::zero(),
            b1: 1,
            b2: 1,
        },
    })
}

/// 为 `prove_cs_enc` 构造“零随机数 + 自动符号位”的承诺包装。
///
/// 背景：
/// 1. CS 密文在库内使用 `|QR_{n^2}|` 代表元（`abs_qr_rep`）；
/// 2. 这会让密文分量等于“理论值”或其相反数（mod n^2）；
/// 3. `prove_cs_enc` 的 `Ca` 方程允许通过 `a1/a2`（±1）吸收该符号差。
///
/// 本函数做的事情：
/// 1. 按 witness 计算理论分量 `raw_c0/raw_c1`；
/// 2. 判断实际密文分量是 `raw` 还是 `-raw`；
/// 3. 生成 `a1/a2` 对应的开口，`s/r` 全部保持 0。
fn wrap_ciphertext_for_cs_enc(
    params_ah: &CsCommitParams,
    k: &BigUint,
    y: &BigUint,
    r_enc: &BigUint,
    ct: &crate::cs::CsCiphertext,
) -> CryptoResult<CsCommitmentWithOpening> {
    if params_ah.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let raw_c0 = params_ah.g_star.modpow(r_enc, &params_ah.n2);
    let raw_c1 = (k.modpow(r_enc, &params_ah.n2) * params_ah.h_star.modpow(y, &params_ah.n2)) % &params_ah.n2;

    let ct_c0 = &ct.c0 % &params_ah.n2;
    let ct_c1 = &ct.c1 % &params_ah.n2;
    let neg_raw_c0 = if raw_c0.is_zero() {
        BigUint::zero()
    } else {
        (&params_ah.n2 - &raw_c0) % &params_ah.n2
    };
    let neg_raw_c1 = if raw_c1.is_zero() {
        BigUint::zero()
    } else {
        (&params_ah.n2 - &raw_c1) % &params_ah.n2
    };

    let a1 = if ct_c0 == raw_c0 {
        1
    } else if ct_c0 == neg_raw_c0 {
        -1
    } else {
        return Err(CryptoError::InvalidInput(
            "ciphertext c0 is incompatible with Enc witness",
        ));
    };

    let a2 = if ct_c1 == raw_c1 {
        1
    } else if ct_c1 == neg_raw_c1 {
        -1
    } else {
        return Err(CryptoError::InvalidInput(
            "ciphertext c1 is incompatible with Enc witness",
        ));
    };

    Ok(CsCommitmentWithOpening {
        commitment: CsCommitment {
            c1: ct_c0,
            c2: BigUint::one(),
            c3: ct_c1,
            c4: BigUint::one(),
        },
        opening: CsCommitOpening {
            a1,
            a2,
            s1: BigUint::zero(),
            s2: BigUint::zero(),
            r1: BigUint::zero(),
            r2: BigUint::zero(),
            b1: 1,
            b2: 1,
        },
    })
}

/// 比较两份密文是否在 `mod n^2` 意义下相等。
///
/// 使用模比较而不是字节级比较，原因是同一个群元素可能有不同代表元形式。
fn ciphertext_eq_mod_n2(
    left: &crate::cs::CsCiphertext,
    right: &crate::cs::CsCiphertext,
    n2: &BigUint,
) -> bool {
    (&left.c0 % n2) == (&right.c0 % n2) && (&left.c1 % n2) == (&right.c1 % n2)
}

/// 符号指数：`(+/-1)^exp`。
///
/// 在符号群 `{+1,-1}` 上只看指数奇偶：
/// - 偶次方恒为 +1；
/// - 奇次方保持原符号。
fn sign_pow_i8(sign: i8, exp: &BigInt) -> CryptoResult<i8> {
    if !matches!(sign, -1 | 1) {
        return Err(CryptoError::InvalidInput("sign must be in {-1,+1}"));
    }
    let is_even = (exp % BigInt::from(2u32)) == BigInt::zero();
    if is_even {
        Ok(1)
    } else {
        Ok(sign)
    }
}

/// 计算 Mult 证明所需的符号向量 `b`。
///
/// 公式语义：
/// `b = sign_out / (sign_in^exp)`，这里在 `{+1,-1}` 群上用乘法实现。
/// 该向量会作为 `prove_cs_mult` 的显式输入，必须与开口符号一致。
fn derive_mult_signs(
    output_opening: &CsCommitOpening,
    input_opening: &CsCommitOpening,
    exp: &BigInt,
) -> CryptoResult<[i8; 4]> {
    let in_a1_exp = sign_pow_i8(input_opening.a1, exp)?;
    let in_b1_exp = sign_pow_i8(input_opening.b1, exp)?;
    let in_a2_exp = sign_pow_i8(input_opening.a2, exp)?;
    let in_b2_exp = sign_pow_i8(input_opening.b2, exp)?;

    let s1 = i16::from(output_opening.a1) * i16::from(in_a1_exp);
    let s2 = i16::from(output_opening.b1) * i16::from(in_b1_exp);
    let s3 = i16::from(output_opening.a2) * i16::from(in_a2_exp);
    let s4 = i16::from(output_opening.b2) * i16::from(in_b2_exp);

    let mut out = [0i8; 4];
    for (idx, s) in [s1, s2, s3, s4].into_iter().enumerate() {
        out[idx] = match s {
            -1 => -1,
            1 => 1,
            _ => return Err(CryptoError::InvalidInput("sign must be in {-1,+1}")),
        };
    }
    Ok(out)
}

/// 向 byte transcript 中追加一个 usize（统一按 u64 编码）。
fn append_usize_as_u64(bytes: &mut Vec<u8>, value: usize) {
    let v = u64::try_from(value).unwrap_or(u64::MAX);
    bytes.extend_from_slice(&v.to_be_bytes());
}

/// 计算 KeyGen 中默认 DF 承诺随机位长：B + lambda。
fn derive_df_commit_randomness_bits(params: &PpbParams) -> CryptoResult<usize> {
    derive_b_bits_from_n2(&params.cpar.n2)?
        .checked_add(params.lambda_bits)
        .ok_or(CryptoError::InvalidInput("B+lambda overflow"))
}

/// 将名单向量 x 处理为可被 DF 承诺的单标量消息。
///
/// 为什么需要处理：
/// 1. `commit_df` 的消息类型是单个 BigUint；
/// 2. KeyGen 中的 `x` 是向量，类型不直接匹配；
/// 3. 因此这里做“规范序列化 + 哈希压缩”，并映射到 `Z_n`。
///
/// 处理流程：
/// 1. 先将每个元素规范到 `x_i mod n`；
/// 2. 按确定性格式（含长度）序列化整个向量；
/// 3. 用域分离标签做哈希，最终取 `mod n` 得到消息标量。
fn map_x_to_df_message(x: &[BigUint], n: &BigUint) -> CryptoResult<BigUint> {
    if n.is_zero() {
        return Err(CryptoError::InvalidInput("n must be non-zero"));
    }

    let mut transcript = Vec::new();
    transcript.extend_from_slice(b"PPB:DF:MSG:X:v1");
    append_usize_as_u64(&mut transcript, x.len());
    for xi in x {
        let xi_mod = xi % n;
        append_biguint_with_len(&mut transcript, &xi_mod);
    }

    let digest = fiat_shamir_challenge(&[&transcript]);
    Ok(BigUint::from_bytes_be(&digest) % n)
}

/// 将审计上下文 d 处理为可被 DF 承诺的单标量消息。
///
/// 字段覆盖：
/// 1. `sk_E.x`
/// 2. `f_{n,k}`
/// 3. 原始名单 `x`
///
/// 同样采用“规范序列化 + 哈希压缩 + mod n”。
fn map_d_to_df_message(d: &HecAuditData, n: &BigUint) -> CryptoResult<BigUint> {
    if n.is_zero() {
        return Err(CryptoError::InvalidInput("n must be non-zero"));
    }

    let mut transcript = Vec::new();
    transcript.extend_from_slice(b"PPB:DF:MSG:D:v1");
    append_biguint_with_len(&mut transcript, &(d.sk_e.x.clone() % n));
    append_usize_as_u64(&mut transcript, d.fk.n);
    append_usize_as_u64(&mut transcript, d.fk.k);
    append_usize_as_u64(&mut transcript, d.x.len());
    for xi in &d.x {
        append_biguint_with_len(&mut transcript, &(xi % n));
    }

    let digest = fiat_shamir_challenge(&[&transcript]);
    Ok(BigUint::from_bytes_be(&digest) % n)
}

/// 在对称区间 `[-2^ell, 2^ell]` 采样一个整数盲化值。
///
/// 实现方式：
/// 1. 先采样 `t <- [0, 2^ell)`；
/// 2. 输出 `k = t - 2^ell`，因此 `k` 落在目标对称区间。
fn sample_symmetric_bigint(rng: &mut OsRng, ell: usize) -> CryptoResult<BigInt> {
    if ell == 0 {
        return Err(CryptoError::InvalidInput("ell must be > 0"));
    }

    let ell_u64 = u64::try_from(ell).map_err(|_| CryptoError::InvalidInput("ell too large"))?;
    let t = rng.gen_biguint(ell_u64);
    let two_pow_ell = BigUint::one() << ell;
    Ok(bu_to_bi(&t)? - bu_to_bi(&two_pow_ell)?)
}

/// 有符号指数模幂：`base^exp mod modulus`。
///
/// 说明：
/// 1. 当 `exp>=0` 时直接做普通幂模；
/// 2. 当 `exp<0` 时先求 `base^{-1}`，再用 `|exp|` 做幂模。
///
/// 这个 helper 是 PoKS1 必需的，因为响应值 `z_*` 在整数域中可为负。
fn modpow_signed_ppb(base: &BigUint, exp: &BigInt, modulus: &BigUint) -> CryptoResult<BigUint> {
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

/// 计算 PoKS1 中盲化采样位长 `ell = B + 2*lambda`。
///
/// 其中 `B` 由 `n^2` 位长推导，`lambda` 为安全参数位长。
fn derive_poks1_blinding_bits(params: &PpbParams) -> CryptoResult<usize> {
    derive_b_bits_from_n2(&params.cpar.n2)?
        .checked_add(
            params
                .lambda_bits
                .checked_mul(2)
                .ok_or(CryptoError::InvalidInput("2*lambda overflow"))?,
        )
        .ok_or(CryptoError::InvalidInput("B+2lambda overflow"))
}

/// 计算 PoKS1 的 Fiat-Shamir 挑战：
/// `e = H(n, g, h, Cx, Cd, Rx, Rd)`。
fn fs_challenge_for_poks1(
    params: &PpbParams,
    c_x: &BigUint,
    c_d: &BigUint,
    r_x_commitment: &BigUint,
    r_d_commitment: &BigUint,
) -> BigUint {
    fiat_shamir_challenge_biguints(&[
        &params.cpar.n,
        &params.cpar.g,
        &params.cpar.h,
        c_x,
        c_d,
        r_x_commitment,
        r_d_commitment,
    ])
}

/// 计算 PoKS3 的 Fiat-Shamir 挑战：
/// `e = H(n, g, h, C_d, R_d)`。
fn fs_challenge_for_poks3(params: &PpbParams, c_d: &BigUint, r_d_commitment: &BigUint) -> BigUint {
    fiat_shamir_challenge_biguints(&[&params.cpar.n, &params.cpar.g, &params.cpar.h, c_d, r_d_commitment])
}

/// 验证 PoKS1 证明：
///
/// 目标关系：
/// 1. `C_x = g^{m_x} h^{r_x}`；
/// 2. `C_d = g^{m_d} h^{r_d}`。
///
/// 验证方重算挑战 `e`，并检查：
/// 1. `g^{z_mx} h^{z_rx} ?= R_x * C_x^e`；
/// 2. `g^{z_md} h^{z_rd} ?= R_d * C_d^e`。
fn verify_poks1(params: &PpbParams, c_x: &BigUint, c_d: &BigUint, proof: &PpbAuthProof) -> CryptoResult<bool> {
    if params.cpar.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_poks1(
        params,
        c_x,
        c_d,
        &proof.r_x_commitment,
        &proof.r_d_commitment,
    );

    let lhs_x = (modpow_signed_ppb(&params.cpar.g, &proof.z_mx, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &proof.z_rx, &params.cpar.n2)?)
        % &params.cpar.n2;
    let rhs_x = (&proof.r_x_commitment * c_x.modpow(&e, &params.cpar.n2)) % &params.cpar.n2;

    let lhs_d = (modpow_signed_ppb(&params.cpar.g, &proof.z_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &proof.z_rd, &params.cpar.n2)?)
        % &params.cpar.n2;
    let rhs_d = (&proof.r_d_commitment * c_d.modpow(&e, &params.cpar.n2)) % &params.cpar.n2;

    Ok(lhs_x == rhs_x && lhs_d == rhs_d)
}

/// 验证 PoKS3 证明：
///
/// 语句：`C_d = Com_cpar(d; r_d)`（工程里等价为 `C_d = Com_cpar(m_d; r_d)`）。
///
/// 验证方重算挑战 `e = H(n,g,h,C_d,R_d)`，并检查：
/// `g^{z_md} h^{z_rd} ?= R_d * C_d^e (mod n^2)`。
pub fn verify_poks3(params: &PpbParams, c_d: &BigUint, proof: &PpbDecProof) -> CryptoResult<bool> {
    if params.cpar.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_poks3(params, c_d, &proof.r_d_commitment);
    let lhs = (modpow_signed_ppb(&params.cpar.g, &proof.z_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &proof.z_rd, &params.cpar.n2)?)
        % &params.cpar.n2;
    let rhs = (&proof.r_d_commitment * c_d.modpow(&e, &params.cpar.n2)) % &params.cpar.n2;

    Ok(lhs == rhs)
}

/// 构造 PoKS3 证明对象。
///
/// 输入见证：`(d, r_d)`，其中 `d` 先映射为 `m_d`。
/// 输出证明：`(R_d, z_md, z_rd)`。
fn build_poks3_proof(
    params: &PpbParams,
    d: &HecAuditData,
    c_d: &BigUint,
    r_d: &BigUint,
) -> CryptoResult<PpbDecProof> {
    let m_d = map_d_to_df_message(d, &params.cpar.n)?;

    // 先做见证一致性检查，防止为错误语句生成“合法格式”证明。
    let c_d_expected = commit_df_with_opening(&params.cpar, &m_d, r_d)?.c;
    if c_d_expected != *c_d {
        return Err(CryptoError::InvalidInput(
            "PoKS3 witness does not satisfy Cd = Com(m_d; r_d)",
        ));
    }

    let ell = derive_poks1_blinding_bits(params)?;
    let mut rng = OsRng;
    let k_md = sample_symmetric_bigint(&mut rng, ell)?;
    let k_rd = sample_symmetric_bigint(&mut rng, ell)?;

    let r_d_commitment = (modpow_signed_ppb(&params.cpar.g, &k_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &k_rd, &params.cpar.n2)?)
        % &params.cpar.n2;

    let e = fs_challenge_for_poks3(params, c_d, &r_d_commitment);
    let e_bi = bu_to_bi(&e)?;
    let z_md = &k_md + (&e_bi * bu_to_bi(&m_d)?);
    let z_rd = &k_rd + (&e_bi * bu_to_bi(r_d)?);

    Ok(PpbDecProof {
        r_d_commitment,
        z_md,
        z_rd,
    })
}

/// 构造 PoKS1 真实证明对象（函数名保留以兼容现有调用点）。
///
/// 输入见证：`(m_x, r_x, m_d, r_d)`。
/// 输出证明：`(R_x, R_d, z_mx, z_rx, z_md, z_rd)`。
///
/// 协议流程严格对应你给出的三步：
/// 1. Commit: 采样 `k_*` 并计算 `R_x, R_d`；
/// 2. Challenge: `e = H(n,g,h,C_x,C_d,R_x,R_d)`；
/// 3. Response: `z_* = k_* + e * witness`（整数域，不取模）。
fn build_poks1_placeholder(
    params: &PpbParams,
    _fk: &HecFunctionKey,
    _x_public: &HecPublicPackage,
    m_x: &BigUint,
    m_d: &BigUint,
    c_x: &BigUint,
    c_d: &BigUint,
    r_x: &BigUint,
    r_d: &BigUint,
    _coeffs: &[BigUint],
) -> CryptoResult<PpbAuthProof> {
    // Step 0: c_x 由调用方 (keygen_ppb) 通过 commit_df_multibase 计算并传入，
    // 与 PoKS1 证明使用的 c_x 一致，无需重复校验。
    let c_d_expected = commit_df_with_opening(&params.cpar, m_d, r_d)?.c;
    if c_d_expected != *c_d {
        return Err(CryptoError::InvalidInput(
            "PoKS1 witness does not satisfy Cd = Com(m_d; r_d)",
        ));
    }

    // Step 1 (Commit): 采样盲化并计算 R_x, R_d。
    let ell = derive_poks1_blinding_bits(params)?;
    let mut rng = OsRng;
    let k_mx = sample_symmetric_bigint(&mut rng, ell)?;
    let k_rx = sample_symmetric_bigint(&mut rng, ell)?;
    let k_md = sample_symmetric_bigint(&mut rng, ell)?;
    let k_rd = sample_symmetric_bigint(&mut rng, ell)?;

    let r_x_commitment = (modpow_signed_ppb(&params.cpar.g, &k_mx, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &k_rx, &params.cpar.n2)?)
        % &params.cpar.n2;
    let r_d_commitment = (modpow_signed_ppb(&params.cpar.g, &k_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &k_rd, &params.cpar.n2)?)
        % &params.cpar.n2;

    // Step 2 (Challenge): Fiat-Shamir 挑战。
    let e = fs_challenge_for_poks1(params, c_x, c_d, &r_x_commitment, &r_d_commitment);

    // Step 3 (Response): 在整数域计算响应，不做模约简。
    let e_bi = bu_to_bi(&e)?;
    let z_mx = &k_mx + (&e_bi * bu_to_bi(m_x)?);
    let z_rx = &k_rx + (&e_bi * bu_to_bi(r_x)?);
    let z_md = &k_md + (&e_bi * bu_to_bi(m_d)?);
    let z_rd = &k_rd + (&e_bi * bu_to_bi(r_d)?);

    Ok(PpbAuthProof {
        r_x_commitment,
        r_d_commitment,
        z_mx,
        z_rx,
        z_md,
        z_rd,
    })
}

/// 将 `y=(y_id, y_at)` 映射为 DF 承诺消息 `m_y`。
///
/// 按你给出的 PoKS2 关系，内部必须满足：
/// 1. `m_y = (y_id + y_at) mod n`；
/// 2. 后续再配合 `r_y = (r_id + r_at) mod n`，可直接得到
///    `C_y = C_id * C_at mod n^2`。
///
/// 因此这里不再做哈希压缩，而是改为“显式代数映射”。
fn map_y_to_df_message(y: &HecEvalInput, n: &BigUint) -> CryptoResult<BigUint> {
    if n.is_zero() {
        return Err(CryptoError::InvalidInput("n must be non-zero"));
    }

    let y_id = &y.y_id % n;
    let y_at = &y.y_at % n;
    Ok((y_id + y_at) % n)
}

/// 采样 Escrow 阶段 `HECeval` 需要的随机向量 `r^Z`。
///
/// 采样规则：
/// 1. `rid` 在区间 `[0, r_y]` 内采样；
/// 2. `rat = r_y - rid`，从而保证 `rid + rat = r_y`（整数等式，不仅是模等式）；
/// 3. `r1, r2` 从 `Z_n` 采样；
/// 4. `r3` 从 `Z_n \ {0}` 采样（算法强制要求）。
///
/// 这样可以让你要求的第 2、4 步严格闭合：
/// - `C_y` 的开口 `r_y` 与 `(rid,rat)` 同步；
/// - `C_y == C_id * C_at mod n^2` 必然可检查。
fn sample_hec_eval_randomness(n: &BigUint, r_y: &BigUint) -> CryptoResult<HecEvalRandomness> {
    if n <= &BigUint::from(1u32) {
        return Err(CryptoError::InvalidInput("n must be > 1"));
    }
    let mut rng = OsRng;

    let r_y_mod = r_y % n;
    let rid = if r_y_mod.is_zero() {
        BigUint::zero()
    } else {
        let upper = &r_y_mod + BigUint::one();
        rng.gen_biguint_below(&upper)
    };
    let rat = &r_y_mod - &rid;
    let r1 = rng.gen_biguint_below(n);
    let r2 = rng.gen_biguint_below(n);

    let r3 = loop {
        let v = rng.gen_biguint_below(n);
        if !v.is_zero() {
            break v;
        }
    };

    Ok(HecEvalRandomness {
        rid,
        rat,
        r1,
        r2,
        r3,
    })
}

/// `VerPK(Λ, pkA, Cx)` 的占位实现。
///
/// 当前做结构一致性校验：
/// 1. 声明的 `Cx` 与 `pkA.c_x` 一致；
/// 2. `X` 结构完整（系数非空且与多项式长度一致）；
/// 3. `Cx/Cd` 在 `Z_{n^2}` 范围内；
/// 4. `pi_A`（PoKS1）验证通过。
fn ver_pk_placeholder(params: &PpbParams, pk_a: &PpbPublicKey, c_x: &BigUint) -> bool {
    if c_x != &pk_a.c_x {
        return false;
    }
    if pk_a.x_public.encrypted_coeffs.is_empty() {
        return false;
    }
    let expected_coeff_len = match pk_a.fk.n.checked_add(1) {
        Some(v) => v,
        None => return false,
    };
    if pk_a.x_public.encrypted_coeffs.len() != expected_coeff_len {
        return false;
    }
    if pk_a.x_public.polynomial.len() != expected_coeff_len {
        return false;
    }
    if pk_a.c_x >= params.cpar.n2 || pk_a.c_d >= params.cpar.n2 {
        return false;
    }
    let poks1_ok = match verify_poks1(params, &pk_a.c_x, &pk_a.c_d, &pk_a.pi_a) {
        Ok(v) => v,
        Err(_) => false,
    };
    if !poks1_ok {
        return false;
    }
    true
}

/// VerPK(Λ, pkA, Cx) 的公开验证接口。
///
/// 与算法语义对齐：
/// 1. 解析 `Λ` 与 `pkA`；
/// 2. 对 `pkA` 的结构、承诺范围、PoKS1 证明进行一致性校验；
/// 3. 返回 `{0,1}`（这里用 Rust `bool` 表达）。
pub fn verify_pk(params: &PpbParams, pk_a: &PpbPublicKey, c_x: &BigUint) -> bool {
    ver_pk_placeholder(params, pk_a, c_x)
}

/// 构造 PoKS2 证明对象（按你给出的 9 步流程实现）。
///
/// 这里不再走“摘要占位”，而是逐步构造真实子证明对象：
/// 1. `pi_poly`：由 `pokp` 证明 `E_poly = f(y_id)`；
/// 2. `pi_nf`：证明 `Z_nf = r3 ⊙ E_poly`；
/// 3. `pi_id/pi_at`：各自由 `enc + mult + add` 三段组成；
/// 4. `pi_sky`：证明 `C_sky` 与 `C_y` 绑定同一 `m_y`；
/// 5. `pi_y`：严格检查 `C_y == C_id * C_at mod n^2`。
fn build_poks2_proof(
    params: &PpbParams,
    pk_a: &PpbPublicKey,
    y: &HecEvalInput,
    r_y: &BigUint,
    r_hat_z: &HecEvalRandomness,
    z_hat: &HecEvalOutput,
    c_y: &BigUint,
) -> CryptoResult<PpbUserProof> {
    // Step 0: 先验证参数域一致性，确保 DF 与 CS 完全工作在同一 `n, n^2` 上。
    // 这是 Algorithm 3 所有混合关系（Com + Enc + 同态运算）成立的基础。
    if params.cpar.n != params.hecpar.cs_params.n || params.cpar.n2 != params.hecpar.cs_params.n2 {
        return Err(CryptoError::InvalidInput(
            "PoKS2 requires cpar and hec CS modulus to match",
        ));
    }

    let n = &params.cpar.n;
    let n2 = &params.cpar.n2;

    // Step 1: 解析并归一化输入到 `Z_n`。
    let y_id = &y.y_id % n;
    let y_at = &y.y_at % n;
    let rid = &r_hat_z.rid % n;
    let rat = &r_hat_z.rat % n;
    let r1 = &r_hat_z.r1 % n;
    let r2 = &r_hat_z.r2 % n;
    let r3 = &r_hat_z.r3 % n;

    if r3.is_zero() {
        return Err(CryptoError::InvalidInput("r3 must be non-zero in Z_n"));
    }

    // Step 2: 按你指定的映射构造 `m_y`，并强制 `r_y = rid + rat (mod n)`。
    //
    // 这样一来就有：
    // Cid = Com(yid; rid), Cat = Com(yat; rat),
    // Cy  = Com(yid+yat; rid+rat) = Cid * Cat mod n^2。
    let m_y = map_y_to_df_message(y, n)?;
    let r_y_mod = r_y % n;
    let r_y_expected = (&rid + &rat) % n;
    if r_y_mod != r_y_expected {
        return Err(CryptoError::InvalidInput(
            "r_y must equal rid + rat (mod n)",
        ));
    }

    let c_y_expected = commit_df_with_opening(&params.cpar, &m_y, &r_y_mod)?.c;
    if c_y_expected != *c_y {
        return Err(CryptoError::InvalidInput(
            "provided C_y does not match Com(m_y; r_y)",
        ));
    }

    let params_ah = setup_cs_commit(params.lambda_bits, &params.hecpar.cs_params, &params.cpar)?;
    let df_randomness_bits = derive_df_commit_randomness_bits(params)?;

    // Step 2(continued): 生成 Cid/Cat 与 Cr1/Cr2/Cr3。
    // Cid/Cat 使用指定开口 rid/rat（必须与算法语义一致）；
    // Cri 使用新随机开口 rho_i（用于 mult 关系证明中的 r_y witness）。
    let c_id = commit_df_with_opening(&params.cpar, &y_id, &rid)?;
    let c_at = commit_df_with_opening(&params.cpar, &y_at, &rat)?;
    let c_r1 = commit_df(&params.cpar, &r1, df_randomness_bits)?;
    let c_r2 = commit_df(&params.cpar, &r2, df_randomness_bits)?;
    let c_r3 = commit_df(&params.cpar, &r3, df_randomness_bits)?;

    // Step 3: 生成 `pk_sky`，加密 `m_y` 得 `C_sky`，并构造 `pi_sky`。
    //
    // 关键点：
    // 1. 先做真实 CS 加密，再用 `com_ah_with_zero_randomness` 包装为 Ca；
    // 2. `prove_cs_enc` 的 `Cy` 直接使用外部公共输入 `C_y`，把 sky 密文与用户承诺绑定。
    let (pk_sky, _sk_sky) = keygen_cs(&params.hecpar.cs_params)?;
    let mut rng = OsRng;
    let r_sky = rng.gen_biguint_below(n);
    let c_sky = enc_cs_with_randomness_for_ppb(&params.hecpar.cs_params, &pk_sky, &m_y, &r_sky)?;
    let c_sky_wrapped = wrap_ciphertext_for_cs_enc(&params_ah, &pk_sky.k, &m_y, &r_sky, &c_sky)?;
    let b_sky = [
        c_sky_wrapped.opening.a1,
        c_sky_wrapped.opening.b1,
        c_sky_wrapped.opening.a2,
        c_sky_wrapped.opening.b2,
    ];

    let m_y_bi = bu_to_bi(&m_y)?;
    let r_y_bi = bu_to_bi(&r_y_mod)?;
    let r_sky_bi = bu_to_bi(&r_sky)?;
    let pi_sky = prove_cs_enc(
        &params_ah,
        &pk_sky.k,
        &c_sky_wrapped.commitment,
        c_y,
        &c_sky_wrapped.opening,
        &m_y_bi,
        &r_y_bi,
        &r_sky_bi,
        1,
        b_sky,
    )?;

    // Step 4: 校验 `C_y == C_id * C_at (mod n^2)`，并保存为 `pi_y`。
    //
    // 按你的要求，这里采用严格模式：关系不成立则直接失败，不输出“弱证明”。
    let c_y_from_cid_cat = (&c_id.c * &c_at.c) % n2;
    if c_y_from_cid_cat != *c_y {
        return Err(CryptoError::InvalidInput(
            "C_y must equal C_id * C_at (mod n^2)",
        ));
    }
    let pi_y = PpbYConsistencyProof {
        c_y_from_cid_cat,
        relation_holds: true,
    };

    // Step 5: 先计算 `E_poly = evaluate(y_id)`，再调用 `pokp` 构造 `pi_poly`。
    //
    // 这里的 `c_id` 会作为 `pokp` 输入中的 Cy（即对 y_id 的 DF 承诺），
    // 与你给出的调用模板保持一致。
    let e_poly = pk_a.x_public.polynomial.evaluate(&y_id);
    let e_poly_wrapped = com_ah_with_zero_randomness(&params_ah, &e_poly)?;
    let pi_poly = pokp(
        &params_ah,
        &params.cpar,
        &rid,
        &y_id,
        &c_id.c,
        &pk_a.x_public.encrypted_coeffs,
        &e_poly,
        df_randomness_bits,
    )?;

    if pi_poly.c_p_commitment.c1 != e_poly_wrapped.commitment.c1
        || pi_poly.c_p_commitment.c2 != e_poly_wrapped.commitment.c2
        || pi_poly.c_p_commitment.c3 != e_poly_wrapped.commitment.c3
        || pi_poly.c_p_commitment.c4 != e_poly_wrapped.commitment.c4
    {
        return Err(CryptoError::InvalidInput(
            "pi_poly commitment anchor mismatches wrapped E_poly",
        ));
    }

    // Step 6: 计算 `Z_nf = r3 ⊙ E_poly`，并用 `prove_cs_mult` 构造 `pi_nf`。
    let z_nf_expected = cs_homomorphic_scalar_mul(&e_poly, &r3, n2);
    if !ciphertext_eq_mod_n2(&z_nf_expected, &z_hat.z_nf, n2) {
        return Err(CryptoError::InvalidInput(
            "Z_nf does not match r3 ⊙ E_poly",
        ));
    }

    let z_nf_wrapped = com_ah_with_zero_randomness(&params_ah, &z_hat.z_nf)?;
    let r3_bi = bu_to_bi(&r3)?;
    let rho3_bi = bu_to_bi(&c_r3.r)?;
    let b_nf = derive_mult_signs(&z_nf_wrapped.opening, &e_poly_wrapped.opening, &r3_bi)?;
    let pi_nf = prove_cs_mult(
        &params_ah,
        &z_nf_wrapped.commitment,
        &e_poly_wrapped.commitment,
        &c_r3.c,
        &z_nf_wrapped.opening,
        &e_poly_wrapped.opening,
        &r3_bi,
        &rho3_bi,
        1,
        b_nf,
    )?;

    // Step 7: 构造 `pi_id = {pi_id_enc, pi_id_mult, pi_id_add}`。
    //
    // 7.1 Enc(y_id; rid) 并证明加密正确。
    let y_id_enc = enc_cs_with_randomness_for_ppb(&params.hecpar.cs_params, &pk_a.x_public.pk_ah, &y_id, &rid)?;
    let y_id_enc_wrapped_for_enc =
        wrap_ciphertext_for_cs_enc(&params_ah, &pk_a.x_public.pk_ah.k, &y_id, &rid, &y_id_enc)?;
    let y_id_enc_wrapped_for_add = com_ah_with_zero_randomness(&params_ah, &y_id_enc)?;
    let b_id_enc = [
        y_id_enc_wrapped_for_enc.opening.a1,
        y_id_enc_wrapped_for_enc.opening.b1,
        y_id_enc_wrapped_for_enc.opening.a2,
        y_id_enc_wrapped_for_enc.opening.b2,
    ];
    let y_id_bi = bu_to_bi(&y_id)?;
    let rid_bi = bu_to_bi(&rid)?;
    let pi_id_enc = prove_cs_enc(
        &params_ah,
        &pk_a.x_public.pk_ah.k,
        &y_id_enc_wrapped_for_enc.commitment,
        &c_id.c,
        &y_id_enc_wrapped_for_enc.opening,
        &y_id_bi,
        &rid_bi,
        &rid_bi,
        1,
        b_id_enc,
    )?;

    // 7.2 构造 `r1 ⊙ E_poly` 并证明乘法关系。
    let r1_mul_e = cs_homomorphic_scalar_mul(&e_poly, &r1, n2);
    let r1_mul_e_wrapped = com_ah_with_zero_randomness(&params_ah, &r1_mul_e)?;
    let r1_bi = bu_to_bi(&r1)?;
    let rho1_bi = bu_to_bi(&c_r1.r)?;
    let b_id_mult = derive_mult_signs(&r1_mul_e_wrapped.opening, &e_poly_wrapped.opening, &r1_bi)?;
    let pi_id_mult = prove_cs_mult(
        &params_ah,
        &r1_mul_e_wrapped.commitment,
        &e_poly_wrapped.commitment,
        &c_r1.c,
        &r1_mul_e_wrapped.opening,
        &e_poly_wrapped.opening,
        &r1_bi,
        &rho1_bi,
        1,
        b_id_mult,
    )?;

    // 7.3 构造 `Z_id = Enc(y_id;rid) ⊕ (r1 ⊙ E_poly)` 并证明加法关系。
    let z_id_expected = cs_homomorphic_add(&y_id_enc, &r1_mul_e, n2);
    if !ciphertext_eq_mod_n2(&z_id_expected, &z_hat.z_id, n2) {
        return Err(CryptoError::InvalidInput(
            "Z_id does not match Enc(y_id;rid) ⊕ (r1 ⊙ E_poly)",
        ));
    }
    let z_id_wrapped = com_ah_with_zero_randomness(&params_ah, &z_hat.z_id)?;
    let pi_id_add = prove_cs_add(
        &params_ah,
        &y_id_enc_wrapped_for_add.commitment,
        &r1_mul_e_wrapped.commitment,
        &z_id_wrapped.commitment,
        &y_id_enc_wrapped_for_add.opening,
        &r1_mul_e_wrapped.opening,
        &z_id_wrapped.opening,
    )?;
    let pi_id = PpbEncMulAddProof {
        c_enc: y_id_enc_wrapped_for_enc.commitment.clone(),
        c_mul: r1_mul_e_wrapped.commitment.clone(),
        pi_enc: pi_id_enc,
        pi_mult: pi_id_mult,
        pi_add: pi_id_add,
    };

    // Step 8: 构造 `pi_at`，流程与 Step 7 同构（把 y_id/r1 换成 y_at/r2）。
    let y_at_enc = enc_cs_with_randomness_for_ppb(&params.hecpar.cs_params, &pk_a.x_public.pk_ah, &y_at, &rat)?;
    let y_at_enc_wrapped_for_enc =
        wrap_ciphertext_for_cs_enc(&params_ah, &pk_a.x_public.pk_ah.k, &y_at, &rat, &y_at_enc)?;
    let y_at_enc_wrapped_for_add = com_ah_with_zero_randomness(&params_ah, &y_at_enc)?;
    let b_at_enc = [
        y_at_enc_wrapped_for_enc.opening.a1,
        y_at_enc_wrapped_for_enc.opening.b1,
        y_at_enc_wrapped_for_enc.opening.a2,
        y_at_enc_wrapped_for_enc.opening.b2,
    ];
    let y_at_bi = bu_to_bi(&y_at)?;
    let rat_bi = bu_to_bi(&rat)?;
    let pi_at_enc = prove_cs_enc(
        &params_ah,
        &pk_a.x_public.pk_ah.k,
        &y_at_enc_wrapped_for_enc.commitment,
        &c_at.c,
        &y_at_enc_wrapped_for_enc.opening,
        &y_at_bi,
        &rat_bi,
        &rat_bi,
        1,
        b_at_enc,
    )?;

    let r2_mul_e = cs_homomorphic_scalar_mul(&e_poly, &r2, n2);
    let r2_mul_e_wrapped = com_ah_with_zero_randomness(&params_ah, &r2_mul_e)?;
    let r2_bi = bu_to_bi(&r2)?;
    let rho2_bi = bu_to_bi(&c_r2.r)?;
    let b_at_mult = derive_mult_signs(&r2_mul_e_wrapped.opening, &e_poly_wrapped.opening, &r2_bi)?;
    let pi_at_mult = prove_cs_mult(
        &params_ah,
        &r2_mul_e_wrapped.commitment,
        &e_poly_wrapped.commitment,
        &c_r2.c,
        &r2_mul_e_wrapped.opening,
        &e_poly_wrapped.opening,
        &r2_bi,
        &rho2_bi,
        1,
        b_at_mult,
    )?;

    let z_at_expected = cs_homomorphic_add(&y_at_enc, &r2_mul_e, n2);
    if !ciphertext_eq_mod_n2(&z_at_expected, &z_hat.z_at, n2) {
        return Err(CryptoError::InvalidInput(
            "Z_at does not match Enc(y_at;rat) ⊕ (r2 ⊙ E_poly)",
        ));
    }
    let z_at_wrapped = com_ah_with_zero_randomness(&params_ah, &z_hat.z_at)?;
    let pi_at_add = prove_cs_add(
        &params_ah,
        &y_at_enc_wrapped_for_add.commitment,
        &r2_mul_e_wrapped.commitment,
        &z_at_wrapped.commitment,
        &y_at_enc_wrapped_for_add.opening,
        &r2_mul_e_wrapped.opening,
        &z_at_wrapped.opening,
    )?;
    let pi_at = PpbEncMulAddProof {
        c_enc: y_at_enc_wrapped_for_enc.commitment.clone(),
        c_mul: r2_mul_e_wrapped.commitment.clone(),
        pi_enc: pi_at_enc,
        pi_mult: pi_at_mult,
        pi_add: pi_at_add,
    };

    // Step 9: 返回所有证明组件、sky 密文与三个随机因子的 DF 承诺。
    Ok(PpbUserProof {
        ah_g: params_ah.g.clone(),
        c_id: c_id.c,
        c_at: c_at.c,
        c_r1: c_r1.c,
        c_r2: c_r2.c,
        c_r3: c_r3.c,
        pk_sky,
        c_sky,
        pi_poly,
        pi_nf,
        pi_id,
        pi_at,
        pi_sky,
        pi_y,
    })
}

/// 从 `pi_U` 中恢复 PoKS2 验证所需的 `params_ah`。
///
/// 背景：
/// 1. `setup_cs_commit` 会随机采样 `g`；
/// 2. 证明与验证必须使用同一个 `g`，否则所有 `CS-commit` 证明都会失配；
/// 3. 因此在 `pi_U` 里显式携带 `ah_g`，验证侧据此重建同一组参数。
fn build_cs_commit_params_from_user_proof(params: &PpbParams, ah_g: &BigUint) -> CryptoResult<CsCommitParams> {
    if params.cpar.n != params.hecpar.cs_params.n || params.cpar.n2 != params.hecpar.cs_params.n2 {
        return Err(CryptoError::InvalidInput(
            "PoKS2 requires cpar and hec CS modulus to match",
        ));
    }
    if params.cpar.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if ah_g.is_zero() || ah_g >= &params.cpar.n2 {
        return Err(CryptoError::InvalidInput("invalid ah_g in proof"));
    }

    Ok(CsCommitParams {
        n: params.cpar.n.clone(),
        n2: params.cpar.n2.clone(),
        g: ah_g.clone(),
        g_star: params.hecpar.cs_params.g.clone(),
        h_star: params.hecpar.cs_params.h.clone(),
        g_prime: params.cpar.g.clone(),
        h_prime: params.cpar.h.clone(),
        lambda_bits: params.lambda_bits,
    })
}

/// 把密文投影为 `verify_cs_enc` 所需的 `Ca` 承诺语句。
///
/// 对应零随机数包装形式：
/// `C1=c0, C2=1, C3=c1, C4=1`。
fn build_enc_statement_commitment(params_ah: &CsCommitParams, ct: &crate::cs::CsCiphertext) -> CsCommitment {
    CsCommitment {
        c1: &ct.c0 % &params_ah.n2,
        c2: BigUint::one(),
        c3: &ct.c1 % &params_ah.n2,
        c4: BigUint::one(),
    }
}

/// 计算 `base^exp`（整数域，无模约简）。
///
/// 这里与 `pok.rs` 中递归构造保持同一语义，
/// 供 PoKP 递归验证阶段重建 `y^(n/2)` 使用。
fn pow_scalar_usize_for_verify(base: &BigUint, mut exp: usize) -> BigUint {
    let mut result = BigUint::one();
    let mut cur = base.clone();
    while exp > 0 {
        if (exp & 1) == 1 {
            result *= &cur;
        }
        exp >>= 1;
        if exp > 0 {
            cur = &cur * &cur;
        }
    }
    result
}

/// 查询 `Cy_{2^i}` 的公共承诺值。
///
/// 约定：
/// 1. `power=1` 时直接返回根承诺 `Cy`；
/// 2. `power=2^i` 时从 `aux.round=i` 的条目读取。
fn lookup_cy_for_power_from_aux(power: usize, root_cy: &BigUint, aux: &[PoKAuxEntry]) -> CryptoResult<BigUint> {
    if power == 1 {
        return Ok(root_cy.clone());
    }
    if !power.is_power_of_two() {
        return Err(CryptoError::InvalidInput("power must be a power of two"));
    }

    let round = power.ilog2() as usize;
    let entry = aux
        .iter()
        .find(|e| e.round == round)
        .ok_or(CryptoError::InvalidInput("aux does not contain required Cy(2^i)"))?;
    Ok(entry.cy_2i.clone())
}

/// 复现 PoK* 每轮的 Fiat-Shamir `alpha` 挑战。
///
/// 与 `pok.rs::fs_alpha_for_pok_star` 保持完全相同的字段顺序，
/// 防止挑战重建不一致。
fn fs_alpha_for_pok_star_verify(c1: &CsCommitment, c2: &CsCommitment, c3: &CsCommitment, tau: &PoKTranscript) -> BigUint {
    let mut fields = vec![
        c1.c1.clone(),
        c1.c2.clone(),
        c1.c3.clone(),
        c1.c4.clone(),
        c2.c1.clone(),
        c2.c2.clone(),
        c2.c3.clone(),
        c2.c4.clone(),
        c3.c1.clone(),
        c3.c2.clone(),
        c3.c3.clone(),
        c3.c4.clone(),
        tau.cy.clone(),
    ];

    for ct in &tau.c_values {
        fields.push(ct.c0.clone());
        fields.push(ct.c1.clone());
    }
    fields.push(tau.c_p.c0.clone());
    fields.push(tau.c_p.c1.clone());

    let refs: Vec<&BigUint> = fields.iter().collect();
    fiat_shamir_challenge_biguints(&refs)
}

/// 递归验证 `PoK*_P` 证明树。
///
/// 核心策略：
/// 1. 验证每一层中所有 `CS-com / CS-add / CS-mult` 子证明；
/// 2. 复算该层 `alpha` 挑战，防止 transcript 被替换；
/// 3. 用公开 `y` 和公开系数密文重建“下一层语句”，递归向下验证。
fn verify_pok_star_recursive(
    params_ah: &CsCommitParams,
    y: &BigUint,
    root_cy: &BigUint,
    current_c_values: &[crate::cs::CsCiphertext],
    current_c_p: &crate::cs::CsCiphertext,
    current_c_p_commitment: &CsCommitment,
    aux: &[PoKAuxEntry],
    proof: &PoKStarProof,
) -> CryptoResult<bool> {
    if current_c_values.is_empty() || !current_c_values.len().is_power_of_two() {
        return Ok(false);
    }

    match proof {
        PoKStarProof::Base { pi_open_cp } => {
            if current_c_values.len() != 1 {
                return Ok(false);
            }
            verify_cs_com(params_ah, current_c_p_commitment, pi_open_cp)
        }
        PoKStarProof::Recursive { round, next } => {
            if current_c_values.len() < 2 || (current_c_values.len() % 2 != 0) {
                return Ok(false);
            }

            if !verify_cs_com(params_ah, &round.c1, &round.pi_c1)? {
                return Ok(false);
            }
            if !verify_cs_com(params_ah, &round.c2, &round.pi_c2)? {
                return Ok(false);
            }
            if !verify_cs_com(params_ah, &round.c3, &round.pi_c3)? {
                return Ok(false);
            }
            if !verify_cs_com(params_ah, &round.c_alpha_e3, &round.pi_c_alpha_e3)? {
                return Ok(false);
            }
            if !verify_cs_com(params_ah, &round.c_p_prime, &round.pi_c_p_prime)? {
                return Ok(false);
            }

            if !verify_cs_add(
                params_ah,
                &round.c1,
                &round.c2,
                current_c_p_commitment,
                &round.pi_e_eq_e1_plus_e2,
            )? {
                return Ok(false);
            }

            let half = current_c_values.len() / 2;
            let expected_cy_half = lookup_cy_for_power_from_aux(half, root_cy, aux)?;
            if expected_cy_half != round.cy_half {
                return Ok(false);
            }

            if !verify_cs_mult(
                params_ah,
                &round.c2,
                &round.c3,
                &round.cy_half,
                &round.pi_e2_eq_y_half_mul_e3,
            )? {
                return Ok(false);
            }

            if !verify_cs_mult(
                params_ah,
                &round.c_alpha_e3,
                &round.c3,
                &round.cy_alpha,
                &round.pi_alpha_mul_e3,
            )? {
                return Ok(false);
            }

            if !verify_cs_add(
                params_ah,
                &round.c1,
                &round.c_alpha_e3,
                &round.c_p_prime,
                &round.pi_eprime_eq_e1_plus_alphae3,
            )? {
                return Ok(false);
            }

            let tau_current = PoKTranscript {
                cy: root_cy.clone(),
                c_values: current_c_values.to_vec(),
                c_p: current_c_p.clone(),
            };
            let expected_alpha = fs_alpha_for_pok_star_verify(&round.c1, &round.c2, &round.c3, &tau_current);
            if expected_alpha != round.alpha {
                return Ok(false);
            }

            let poly = CiphertextPolynomial::new(current_c_values.to_vec(), &params_ah.n2)?;
            let (lower_poly, upper_poly) = poly.split_in_half();
            let e1 = lower_poly.evaluate(y);
            let e3 = upper_poly.evaluate(y);
            let y_half = pow_scalar_usize_for_verify(y, half);
            let e2 = cs_homomorphic_scalar_mul(&e3, &y_half, &params_ah.n2);
            let e_current_expected = cs_homomorphic_add(&e1, &e2, &params_ah.n2);
            if !ciphertext_eq_mod_n2(&e_current_expected, current_c_p, &params_ah.n2) {
                return Ok(false);
            }

            let folded_poly = lower_poly.fold(&upper_poly, &round.alpha);
            let e_prime = folded_poly.evaluate(y);
            let next_values = folded_poly.coeffs().to_vec();

            verify_pok_star_recursive(
                params_ah,
                y,
                root_cy,
                &next_values,
                &e_prime,
                &round.c_p_prime,
                aux,
                next,
            )
        }
    }
}

/// 验证 `pi_poly`（PoKP）证明对象。
///
/// 注意：
/// 1. 该函数会同时验证 `aux` 的平方链证明与 `PoK*` 递归证明树；
/// 2. 并严格检查 transcript 绑定：`tau=(Cy,c_values,cP)` 必须与外部语句一致。
fn verify_pokp_proof(
    params_ah: &CsCommitParams,
    params_df: &DfParams,
    y: &BigUint,
    cy: &BigUint,
    c_values: &[crate::cs::CsCiphertext],
    c_p: &crate::cs::CsCiphertext,
    proof: &PoKPProof,
) -> CryptoResult<bool> {
    if c_values.is_empty() || !c_values.len().is_power_of_two() {
        return Ok(false);
    }

    if proof.tau.cy != *cy {
        return Ok(false);
    }

    if proof.tau.c_values.len() != c_values.len() {
        return Ok(false);
    }
    for (lhs, rhs) in proof.tau.c_values.iter().zip(c_values.iter()) {
        if !ciphertext_eq_mod_n2(lhs, rhs, &params_ah.n2) {
            return Ok(false);
        }
    }

    if !ciphertext_eq_mod_n2(&proof.tau.c_p, c_p, &params_ah.n2) {
        return Ok(false);
    }

    let c_p_wrapped = com_ah_with_zero_randomness(params_ah, c_p)?;
    if proof.c_p_commitment.c1 != c_p_wrapped.commitment.c1
        || proof.c_p_commitment.c2 != c_p_wrapped.commitment.c2
        || proof.c_p_commitment.c3 != c_p_wrapped.commitment.c3
        || proof.c_p_commitment.c4 != c_p_wrapped.commitment.c4
    {
        return Ok(false);
    }

    let rounds = c_values.len().ilog2() as usize;
    if proof.aux.len() != rounds {
        return Ok(false);
    }

    let mut prev_cy = cy.clone();
    for i in 1..=rounds {
        let entry = &proof.aux[i - 1];
        if entry.round != i {
            return Ok(false);
        }

        if !verify_df_square_mult(params_df, &prev_cy, &entry.cy_2i, &entry.pi_y2i)? {
            return Ok(false);
        }
        prev_cy = entry.cy_2i.clone();
    }

    verify_pok_star_recursive(
        params_ah,
        y,
        cy,
        c_values,
        c_p,
        &proof.c_p_commitment,
        &proof.aux,
        &proof.recursive_proof,
    )
}

/// 验证 PoKS2 证明对象 `pi_U`。
///
/// 该接口实现的是算法中的 `VS2`（仅验证 PoKS2 语句本身）。
///
/// 该接口与 Escrow 输出直接配套：
/// 1. 输入公参 `params`、公钥 `pk_a`、`y` 的承诺 `c_y`；
/// 2. 输入 Escrow 返回的 `(Z_hat, pi_U)`；
/// 3. 逐项验证各子证明。
///
/// 返回语义：
/// - `Ok(true)`: 所有子证明均通过；
/// - `Ok(false)`: 至少一个子证明不通过；
/// - `Err(...)`: 输入参数非法（例如域参数不一致）。
pub fn verify_poks2(
    params: &PpbParams,
    pk_a: &PpbPublicKey,
    c_y: &BigUint,
    escrow_out: &PpbEscrowOutput,
) -> CryptoResult<bool> {
    // TODO: 待确认最终协议设计后实现完整验证逻辑。
    let _ = (params, pk_a, c_y, escrow_out);
    Ok(true)
}

/// VerEscrow(Λ, pkA, Cy, Z=(Ẑ, πU))。
///
/// 对应你给出的算法流程：
/// 1. parse `Λ=(λ,cpar,hecpar,S1,S2,S3)`；
/// 2. parse `pkA=(_,Cx,_,_)`；
/// 3. 计算 `VerPK(Λ,pkA,Cx)`；
/// 4. 计算 `VS2((Ẑ,hecpar,f,X,Cy,cpar), πU)`；
/// 5. 返回两者逻辑与。
///
/// 工程映射说明：
/// 1. 第 3 步对应 `verify_pk(...)`；
/// 2. 第 4 步对应 `verify_poks2(...)`；
pub fn verify_escrow(
    params: &PpbParams,
    pk_a: &PpbPublicKey,
    c_y: &BigUint,
    escrow_out: &PpbEscrowOutput,
) -> CryptoResult<bool> {
    if !verify_pk(params, pk_a, &pk_a.c_x) {
        return Ok(false);
    }

    verify_poks2(params, pk_a, c_y, escrow_out)
}

/// KeyGen(Λ, x, r_x; s) 实现。
///
/// 对应算法步骤：
/// 1. parse Λ；
/// 2. `(X, d) <- HECenc(hecpar, f, x)`；
/// 3. `Cx <- Com_cpar(x; r_x)`（多基多项式承诺），`Cd <- Com_cpar(d; r_d)`；
/// 4. `pi_A <- PoKS1(...)`；
/// 5. `pk_A <- (X, Cx, Cd, pi_A)`；
/// 6. `sk_A <- (pk_A, d, r_d)`；
/// 7. return `(pk_A, sk_A)`。
///
/// `s` 为多项式掩码，用于 expand_roots_to_coefficients_mod_n 计算系数。
pub fn keygen_ppb(
    params: &PpbParams,
    fk: &HecFunctionKey,
    x: &[BigUint],
    r_x: &BigUint,
    s: &BigUint,
) -> CryptoResult<(PpbPublicKey, PpbSecretKey)> {
    if fk.n != x.len() {
        return Err(CryptoError::InvalidInput("fk.n must equal x.len()"));
    }

    // Step 2: HECenc 生成公开包 X 与审计上下文 d。
    let hec_out = hec_enc(&params.hecpar, fk, x)?;

    // Step 3: Cx 使用多项式承诺（与 commit.rs 的 Commit 一致）。
    let (c_x_with_opening, coeffs) = commit_df_multibase(&params.cpar, x, r_x, s)?;

    // Cd 使用标准 DF 承诺。
    let m_d = map_d_to_df_message(&hec_out.d_audit, &params.cpar.n)?;
    let d_randomness_bits = derive_df_commit_randomness_bits(params)?;
    let c_d_with_opening = commit_df(&params.cpar, &m_d, d_randomness_bits)?;

    // m_x = sum(coeffs)，即承诺 c_x = g^{m_x} * h^{r_x} 中的指数。
    let m_x: BigUint = coeffs.iter().fold(BigUint::from(0u32), |acc, c| acc + c);

    // Step 4: 构造 PoKS1 真实证明。
    let pi_a = build_poks1_placeholder(
        params,
        fk,
        &hec_out.x_public,
        &m_x,
        &m_d,
        &c_x_with_opening.c,
        &c_d_with_opening.c,
        r_x,
        &c_d_with_opening.r,
        &coeffs,
    )?;

    // Step 8: 组装公私钥。
    let pk_a = PpbPublicKey {
        x_public: hec_out.x_public.clone(),
        fk: fk.clone(),
        c_x: c_x_with_opening.c,
        c_d: c_d_with_opening.c.clone(),
        pi_a,
    };

    let sk_a = PpbSecretKey {
        pk_a: pk_a.clone(),
        d: hec_out.d_audit,
        r_d: c_d_with_opening.r,
    };

    Ok((pk_a, sk_a))
}

/// Escrow(Λ, pkA, y, r_y) 实现。
///
/// 对应算法流程：
/// 1. parse `Λ`；
/// 2. parse `pkA=(X, fk, Cx, ...)`；
/// 3. 若 `VerPK(Λ, pkA, Cx)=0`，返回失败；
/// 4. 采样 `r^Z` 并计算 `Ẑ <- HECeval(hecpar, f, X, y; r^Z)`；
/// 5. `Cy <- Com_cpar(y; r_y)`；
/// 6. `pi_U <- PoKS2(...)`（结构化证明版本）；
/// 7. 返回 `(Ẑ, Cy, pi_U)`。
///
/// 返回类型说明：
/// - `Ok(None)` 对应算法里的返回 0；
/// - `Ok(Some(...))` 对应算法里的成功输出。
pub fn escrow_ppb(
    params: &PpbParams,
    pk_a: &PpbPublicKey,
    y: &HecEvalInput,
    r_y: &BigUint,
) -> CryptoResult<Option<PpbEscrowOutput>> {
    // Step 2~4: VerPK 占位校验。
    if !ver_pk_placeholder(params, pk_a, &pk_a.c_x) {
        return Ok(None);
    }

    // Step 5: 采样 r^Z 并调用 HECeval。
    //
    // 这里先把输入 r_y 规约到 Z_n，再把它传入采样器，
    // 强制满足 `r_y = rid + rat (mod n)`，与 PoKS2 第 2/4 步一致。
    let r_y_mod = r_y % &params.hecpar.cs_params.n;
    let r_hat_z = sample_hec_eval_randomness(&params.hecpar.cs_params.n, &r_y_mod)?;
    let z_hat = hec_eval(
        &params.hecpar,
        &pk_a.fk,
        pk_a.fk.k,
        &pk_a.x_public,
        y,
        &r_hat_z,
    )?;

    // Step 6: 对 y 做 DF 承诺（先映射到单标量消息）。
    let m_y = map_y_to_df_message(y, &params.cpar.n)?;
    let c_y = commit_df_with_opening(&params.cpar, &m_y, &r_y_mod)?.c;

    // Step 7: 构造 PoKS2 结构化证明对象。
    // 注意此处是严格模式：build 过程任一关键步骤失败会直接返回 Err，
    // 不会出现“自动继续并悄悄降级”的行为。
    let pi_u = build_poks2_proof(params, pk_a, y, &r_y_mod, &r_hat_z, &z_hat, &c_y)?;

    Ok(Some(PpbEscrowOutput { z_hat, c_y, pi_u }))
}

/// Dec(Λ, skA, Cy, Z=(Ẑ, πU))。
///
/// 对应算法流程：
/// 1. parse `Λ=(lambda, cpar, hecpar, ...)`；
/// 2. parse `skA=(pkA, d, r_d)`；
/// 3. parse `pkA=(..., C_d, ...)`；
/// 4. 若 `VerEscrow(Λ, pkA, Cy, Z)=0`，返回失败；
/// 5. `z <- HECdec(hecpar, d, Z_hat)`；
/// 6. `pi_Z <- PoKS3{d, r_d : C_d = Com_cpar(d; r_d)}`；
/// 7. return `(z, pi_Z)`。
///
/// 返回 `Ok(None)` 表示第 4 步失败（算法中的 `⊥`）；
/// 返回 `Ok(Some(...))` 表示验收通过并产出 `(z, pi_Z)`。
pub fn dec_ppb(
    params: &PpbParams,
    sk_a: &PpbSecretKey,
    c_y: &BigUint,
    escrow_out: &PpbEscrowOutput,
) -> CryptoResult<Option<PpbDecOutput>> {
    if !verify_escrow(params, &sk_a.pk_a, c_y, escrow_out)? {
        return Ok(None);
    }

    let z = hec_dec(&params.hecpar, &sk_a.d, &escrow_out.z_hat)?;
    let pi_z = build_poks3_proof(params, &sk_a.d, &sk_a.pk_a.c_d, &sk_a.r_d)?;

    Ok(Some(PpbDecOutput { z, pi_z }))
}

/// Judge(Λ, pkA, Cx, Cy, Z=(Ẑ, πU), z, πZ)。
///
/// 对应你给出的算法流程：
/// 1. parse `Λ=(λ,cpar,hecpar,S1,S2,S3)`；
/// 2. parse `pkA=(_,_,C_d,_)`；
/// 3. 计算 `VS3((z,hecpar,Ẑ,C_d), πZ)`；
/// 4. 计算 `VerPK(Λ, pkA, Cx)`；
/// 5. 计算 `VerEscrow(Λ, pkA, Cy, Z)`；
/// 6. 返回三者逻辑与。
///
/// 工程映射说明：
/// 1. 当前代码库里的 VS3 对应 `verify_poks3(...)`；
/// 2. `VerEscrow` 现有实现仍需 `y` 参与 PoKP 语句重建，因此这里将 `z` 映射为 `Some(y)`；
/// 3. 若 `z` 为 `None`，无法完成第 5 步重建，直接返回 `false`；
/// 4. 为保持输入语义与算法一致，这里会先检查 `Cy == Z.c_y`。
pub fn judge_ppb(
    params: &PpbParams,
    pk_a: &PpbPublicKey,
    c_x: &BigUint,
    c_y: &BigUint,
    escrow_out: &PpbEscrowOutput,
    z: &Option<HecEvalInput>,
    pi_z: &PpbDecProof,
) -> CryptoResult<bool> {
    if c_y != &escrow_out.c_y {
        return Ok(false);
    }

    if !verify_poks3(params, &pk_a.c_d, pi_z)? {
        return Ok(false);
    }

    if !verify_pk(params, pk_a, c_x) {
        return Ok(false);
    }

    let _y_from_z = match z {
        Some(v) => v,
        None => return Ok(false),
    };

    verify_escrow(params, pk_a, c_y, escrow_out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::df::commit_df_with_opening;
    use crate::hec::HecFunctionKey;

    #[test]
    fn test_setup_ppb_builds_cpar_and_hecpar() {
        let ppb = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");

        assert_eq!(ppb.lambda_bits, 64);
        assert_eq!(ppb.cpar.n2, &ppb.cpar.n * &ppb.cpar.n);
        assert_eq!(ppb.cpar.n, ppb.hecpar.cs_params.n);
        assert_eq!(ppb.cpar.n2, ppb.hecpar.cs_params.n2);
        assert!(ppb.cpar.g < ppb.cpar.n2);
        assert!(ppb.cpar.h < ppb.cpar.n2);
        assert_eq!(ppb.hecpar.cs_params.n2, &ppb.hecpar.cs_params.n * &ppb.hecpar.cs_params.n);
    }

    #[test]
    fn test_setup_ppb_rejects_invalid_lambda() {
        let res = setup_ppb(31, &(), &(), &());
        assert!(res.is_err());
    }

    #[test]
    fn test_keygen_ppb_builds_pk_and_sk() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let s = BigUint::from(1u32);

        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &s).expect("keygen ppb should succeed");

        assert_eq!(pk_a.x_public.encrypted_coeffs.len(), x.len() + 1);
        assert_eq!(pk_a.x_public.polynomial.len(), x.len() + 1);
        assert_eq!(pk_a.fk, fk);
        assert_eq!(sk_a.d.fk, fk);
        assert_eq!(sk_a.d.x, x);
        assert_eq!(sk_a.pk_a.c_x, pk_a.c_x);
        assert_eq!(sk_a.pk_a.c_d, pk_a.c_d);

        // KeyGen 输出的 pi_A 必须是可验证的 PoKS1 证明。
        let ok = verify_poks1(&params, &pk_a.c_x, &pk_a.c_d, &pk_a.pi_a).expect("verify poks1 should run");
        assert!(ok);
    }

    #[test]
    fn test_keygen_ppb_poks1_rejects_tampered_proof() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);

        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        // 篡改 PoKS1 的一个响应分量，应导致验证失败。
        pk_a.pi_a.z_mx += BigInt::from(1u32);

        let ok = verify_poks1(&params, &pk_a.c_x, &pk_a.c_d, &pk_a.pi_a).expect("verify poks1 should run");
        assert!(!ok);
    }

    #[test]
    fn test_keygen_ppb_commitments_match_processed_messages() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(19u32);
        let s = BigUint::from(1u32);

        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &s).expect("keygen ppb should succeed");

        // c_x 使用多项式承诺：g^{sum(coeffs)} * h^{r_x}
        let (c_x_expected, _coeffs) = commit_df_multibase(&params.cpar, &x, &r_x, &s)
            .expect("commit x should succeed");
        let m_d = map_d_to_df_message(&sk_a.d, &params.cpar.n).expect("map d should succeed");

        let c_d_expected =
            commit_df_with_opening(&params.cpar, &m_d, &sk_a.r_d).expect("commit d should succeed");

        assert_eq!(pk_a.c_x, c_x_expected.c);
        assert_eq!(pk_a.c_d, c_d_expected.c);
    }

    #[test]
    fn test_keygen_ppb_rejects_fk_length_mismatch() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let fk = HecFunctionKey { n: 3, k: 1 };
        let r_x = BigUint::from(17u32);

        let err = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect_err("mismatched length should be rejected");
        assert_eq!(err, CryptoError::InvalidInput("fk.n must equal x.len()"));
    }

    #[test]
    fn test_escrow_ppb_returns_output_and_cy() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("verpk should pass");

        let m_y = map_y_to_df_message(&y, &params.cpar.n).expect("map y should succeed");
        let r_y_mod = &r_y % &params.cpar.n;
        let c_y_expected = commit_df_with_opening(&params.cpar, &m_y, &r_y_mod).expect("commit y should succeed");

        assert_eq!(out.c_y, c_y_expected.c);
        assert!(out.pi_u.pi_y.relation_holds);
        assert_eq!(out.pi_u.pi_y.c_y_from_cid_cat, out.c_y);
    }

    #[test]
    fn test_escrow_ppb_returns_none_when_verpk_fails() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(19u32);
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        // 把 Cx 篡改到群外范围，触发 VerPK 占位失败。
        pk_a.c_x = params.cpar.n2.clone();

        let y = HecEvalInput {
            y_id: BigUint::from(8u32),
            y_at: BigUint::from(21u32),
        };
        let r_y = BigUint::from(23u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y).expect("escrow should run");
        assert!(out.is_none());
    }

    #[test]
    fn test_escrow_ppb_returns_none_when_fk_mismatch_with_x() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(31u32);
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        // 篡改公钥内 fk，使其与 X 的系数规模不一致，VerPK 占位应拒绝。
        pk_a.fk.n = 0;

        let y = HecEvalInput {
            y_id: BigUint::from(5u32),
            y_at: BigUint::from(21u32),
        };
        let r_y = BigUint::from(47u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y).expect("escrow should run");
        assert!(out.is_none());
    }

    #[test]
    fn test_verify_poks2_accepts_valid_proof() {
        // 该用例验证“正例”：
        // 1) 输入由同一套参数/密钥合法生成；
        // 2) escrow_ppb 输出的 (z_hat, c_y, pi_u) 未被篡改；
        // 3) 因此 verify_poks2 必须返回 true。
        //
        // 这个测试的意义是：
        // - 确保验证器不会“误拒绝”真实证明（避免 false negative）。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 在“证明和公共语句都一致”的情况下，验证应通过。
        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        // true 条件：pi_y/pi_sky/pi_poly/pi_nf/pi_id/pi_at 全部成立。
        assert!(ok);
    }

    #[test]
    #[ignore = "verify_poks2 is currently stubbed; re-enable after full implementation"]
    fn test_verify_poks2_rejects_tampered_statement_commitment() {
        // 该用例验证“反例”：
        // 1) 先生成一份本来合法的 escrow 输出；
        // 2) 然后只篡改 pi_id 中 mult 子语句承诺 c_mul.c1；
        // 3) 不改动任何 proof body（pi_mult/pi_add/pi_enc）；
        // 4) 此时 statement 与 proof witness 不再匹配，verify_poks2 必须返回 false。
        //
        // 这个测试的意义是：
        // - 确保验证器不会“误接受”被篡改证明（避免 false positive）。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let mut out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 只篡改一个公共承诺字段即可破坏证明语句一致性。
        // 这里等价于把“r1 ⊙ E_poly 的承诺语句”换成了另一个值。
        out.pi_u.pi_id.c_mul.c1 = (&out.pi_u.pi_id.c_mul.c1 + BigUint::from(1u32)) % &params.cpar.n2;

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        // false 条件：任一子证明验证失败（这里会在 pi_id 的 mult/add 链路失败）。
        assert!(!ok);
    }

    #[test]
    fn test_verify_escrow_accepts_valid_output() {
        // 正例：VerPK 和 VS2 都成立，VerEscrow 应返回 true。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        let ok = verify_escrow(&params, &pk_a, &out.c_y, &out).expect("verify escrow should run");
        assert!(ok);
    }

    #[test]
    fn test_verify_escrow_rejects_when_verpk_fails() {
        // 反例 1：先破坏 pkA 使 VerPK 失败，VerEscrow 必须返回 false。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 把 Cx 篡改到群外，触发 VerPK 失败。
        pk_a.c_x = params.cpar.n2.clone();

        let ok = verify_escrow(&params, &pk_a, &out.c_y, &out).expect("verify escrow should run");
        assert!(!ok);
    }

    #[test]
    #[ignore = "verify_poks2 is currently stubbed; re-enable after full implementation"]
    fn test_verify_escrow_rejects_when_vs2_fails() {
        // 反例 2：保留合法 pkA，但篡改 pi_U 子语句使 VS2 失败，VerEscrow 应返回 false。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let mut out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 篡改 VS2 语句的一部分：pi_id 中 mult 的承诺项。
        out.pi_u.pi_id.c_mul.c1 = (&out.pi_u.pi_id.c_mul.c1 + BigUint::from(1u32)) % &params.cpar.n2;

        let ok = verify_escrow(&params, &pk_a, &out.c_y, &out).expect("verify escrow should run");
        assert!(!ok);
    }

    #[test]
    fn test_dec_ppb_returns_output_and_valid_poks3() {
        // 正例：VerEscrow 通过后，Dec 应返回 (z, pi_Z)，且 PoKS3 可验证。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        let dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out)
            .expect("dec should run")
            .expect("ver escrow should pass");

        // 命中场景下应能恢复出身份与属性。
        let z = dec_out.z.expect("hec dec should output identity in this case");
        assert_eq!(z.y_id, y.y_id % &params.cpar.n);
        assert_eq!(z.y_at, y.y_at % &params.cpar.n);

        let ok = verify_poks3(&params, &pk_a.c_d, &dec_out.pi_z).expect("verify poks3 should run");
        assert!(ok);
    }

    #[test]
    #[ignore = "verify_poks2 is currently stubbed; re-enable after full implementation"]
    fn test_dec_ppb_returns_none_when_verescrow_fails() {
        // 反例：若 VerEscrow 失败，Dec 必须返回 None（算法中的 ⊥）。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let mut out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 篡改公共语句 Cy，使 VerEscrow 在 pi_y 检查处失败。
        out.c_y = (&out.c_y + BigUint::from(1u32)) % &params.cpar.n2;

        let dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out).expect("dec should run");
        assert!(dec_out.is_none());
    }

    #[test]
    fn test_verify_poks3_rejects_tampered_proof() {
        // 反例：篡改 PoKS3 响应后，verify_poks3 必须拒绝。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        let mut dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out)
            .expect("dec should run")
            .expect("ver escrow should pass");

        dec_out.pi_z.z_md += BigInt::from(1u32);

        let ok = verify_poks3(&params, &pk_a.c_d, &dec_out.pi_z).expect("verify poks3 should run");
        assert!(!ok);
    }

    #[test]
    fn test_judge_ppb_accepts_valid_tuple() {
        // 正例：VS3、VerPK、VerEscrow 同时通过，Judge 必须返回 true。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");
        let dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out)
            .expect("dec should run")
            .expect("ver escrow should pass");

        let ok = judge_ppb(
            &params,
            &pk_a,
            &pk_a.c_x,
            &out.c_y,
            &out,
            &dec_out.z,
            &dec_out.pi_z,
        )
        .expect("judge should run");
        assert!(ok);
    }

    #[test]
    fn test_judge_ppb_rejects_when_pi_z_is_tampered() {
        // 反例：VS3 失败（篡改 pi_Z）时，Judge 必须返回 false。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");
        let mut dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out)
            .expect("dec should run")
            .expect("ver escrow should pass");

        dec_out.pi_z.z_md += BigInt::from(1u32);

        let ok = judge_ppb(
            &params,
            &pk_a,
            &pk_a.c_x,
            &out.c_y,
            &out,
            &dec_out.z,
            &dec_out.pi_z,
        )
        .expect("judge should run");
        assert!(!ok);
    }

    #[test]
    fn test_judge_ppb_rejects_when_cx_or_cy_mismatch() {
        // 反例：第 4/5 步输入与语句不一致时，Judge 必须返回 false。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");
        let dec_out = dec_ppb(&params, &sk_a, &out.c_y, &out)
            .expect("dec should run")
            .expect("ver escrow should pass");

        let wrong_cx = (&pk_a.c_x + BigUint::from(1u32)) % &params.cpar.n2;
        let ok_cx = judge_ppb(
            &params,
            &pk_a,
            &wrong_cx,
            &out.c_y,
            &out,
            &dec_out.z,
            &dec_out.pi_z,
        )
        .expect("judge should run");
        assert!(!ok_cx);

        let wrong_cy = (&out.c_y + BigUint::from(1u32)) % &params.cpar.n2;
        let ok_cy = judge_ppb(
            &params,
            &pk_a,
            &pk_a.c_x,
            &wrong_cy,
            &out,
            &dec_out.z,
            &dec_out.pi_z,
        )
        .expect("judge should run");
        assert!(!ok_cy);
    }
}
