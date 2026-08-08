use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::cs::{CsPubKey, enc_cs_with_randomness, keygen_cs};
use crate::cs_commit::{
    CsAddProof, CsComProof, CsCommitOpening, CsCommitParams, CsCommitment, CsCommitmentWithOpening,
    CsEncProof, CsMultProof, prove_cs_add, prove_cs_enc, prove_cs_mult, setup_cs_commit,
    verify_cs_add, verify_cs_com, verify_cs_com_ciphertext, verify_cs_enc, verify_cs_mult,
};
use crate::df::{DfParams, commit_df, commit_df_with_opening};
use crate::error::{CryptoError, CryptoResult};
use crate::hash::{fiat_shamir_challenge, fiat_shamir_challenge_biguints};
use crate::hec::{
    HecAuditData, HecEvalInput, HecEvalOutput, HecEvalRandomness, HecFunctionKey, HecParams,
    HecPublicPackage, hec_dec, hec_enc_with_mask, hec_eval, setup_hec,
};
use crate::math::{abs_qr_rep, derive_b_bits_from_n2, gcd, modinv, sample_unit_mod_n2};
use crate::pok::{
    CiphertextPolynomial, PoKAuxEntry, PoKPProof, PoKStarProof, PoKTranscript, pokp,
    verify_df_open_public_scalar, verify_mult as verify_df_square_mult,
};

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
    /// “天上的公钥” pk_sky（对应论文 Thm 9 / g*-BB-PSL 中 setup S2 生成的
    /// 固定公钥）。
    ///
    /// 作用：Ψ2 证明要求 prover 把 y 用【这把固定公钥】g-半加密，安全归约里的
    /// 直线抽取器以其对应私钥为陷门直线抽取 g(y)。
    ///
    /// 关键：pk_sky 必须由 setup 固定、脱离 prover 控制。若像旧实现那样让 prover
    /// 每次自造并丢弃私钥，则无人持有陷门，直线可提取性（Blueprint-Hiding /
    /// Privacy 归约所依赖）名存实亡。对应私钥 sk_sky 只是安全证明中的陷门，
    /// 诚实各方无需使用，故在具体实现里 setup 生成后即丢弃即可。
    pub sky_pk: CsPubKey,
}

/// PoKS1 折叠证明中的一轮 `(L_j, R_j)`。
///
/// 方案 A 中，PoKS1 的 `Cx` 不再承诺原始名单 roots，而是承诺 HECenc
/// 实际加密的多项式系数向量 `P_i`。公开密文 `A_i` 正好对应 PDF 里的
/// `c_i`，折叠过程证明同一个隐藏向量同时打开 `Cx` 并被 `A_i` 加密。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbS1FoldRound {
    pub l: BigUint,
    pub r: BigUint,
}

/// PoKS1 折叠后的最终 Σ/Fiat-Shamir 证明。
///
/// 折叠把向量关系压成单个标量关系后，最终证明同时绑定五件事：
/// 1. `C* = (g*)^{x*} h^{r_x*}`，即折叠后的向量承诺仍可打开；
/// 2. `Cd = g^{m_d} h^{r_d}`，沿用当前工程对审计上下文 `d` 的绑定；
/// 3. `pkAH = |g_cs^{sk_E}|`，证明 HEC 公钥和审计私钥匹配；
/// 4. `A* . c0 = |g_cs^{rho*}|`；
/// 5. `A* . c1 = |pkAH^{rho*} h_cs^{x*}|`。
///
/// 最后两条就是折叠后密文 `A* = Enc_pkAH(x*; rho*)`。验证时统一平方，
/// 用来消除 Camenisch-Shoup 绝对值代表元带来的 ± 符号差异。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbS1FinalProof {
    pub r_cx: BigUint,
    pub r_cd: BigUint,
    pub r_pk: BigUint,
    pub r_u: BigUint,
    pub r_v: BigUint,
    pub z_x: BigUint,
    pub z_rx: BigUint,
    pub z_md: BigUint,
    pub z_rd: BigUint,
    pub z_sk: BigUint,
    pub z_rho: BigUint,
}

/// KeyGen 中输出的认证证明 `pi_A`（PoKS1）。
///
/// 当前实现按“方案 A”解释论文中的 `x`：PoKS1 证明的是 HECenc 输出
/// `X=(pkAH,A_i)` 与一个系数向量承诺 `Cx` 一致。原始名单 roots 到系数
/// 的正确展开不在本证明内处理，这是后续更强 PoKS1 的扩展点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbAuthProof {
    pub rounds: Vec<PpbS1FoldRound>,
    pub final_proof: PpbS1FinalProof,
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

/// Dec 阶段输出的 `pi_Z`（PoKS3/S3）证明。
///
/// 证明目标：
/// 1. 兼容当前 KeyGen/S1：证明者知道 `m_d, r_d`，使
///    `C_d = Com_cpar(m_d; r_d)`；
/// 2. 证明者知道同一个 `sk_E`，使 `pkAH = |g_enc^{sk_E}|`；
/// 3. 证明 `Z_id/Z_at/Z_nf` 分别解密为公开的 `z.y_id/z.y_at/0`。
///
/// CS 密文和公钥使用绝对值代表元，因此第 2、3 条在平方后的群关系中验证。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PpbDecProof {
    pub r_d_commitment: BigUint,
    pub r_pk_commitment: BigUint,
    pub r_z_id: BigUint,
    pub r_z_at: BigUint,
    pub r_z_nf: BigUint,
    pub z_md: BigInt,
    pub z_rd: BigInt,
    pub z_sk: BigInt,
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

    // 生成固定的“天上的公钥” pk_sky（论文 setup S2）。
    // sk_sky 是安全归约里直线抽取器的陷门，诚实流程用不到，这里直接丢弃；
    // 真实部署若需要可提取性归约成立，应由 setup 方在受控环境下保管 sk_sky。
    let (sky_pk, _sky_sk) = keygen_cs(&hecpar.cs_params)?;

    Ok(PpbParams {
        lambda_bits,
        cpar,
        hecpar,
        sky_pk,
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
    v.to_bigint().ok_or(CryptoError::InvalidInput(
        "BigUint->BigInt conversion failed",
    ))
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
    let raw_c1 = (k.modpow(r_enc, &params_ah.n2) * params_ah.h_star.modpow(y, &params_ah.n2))
        % &params_ah.n2;

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
    if is_even { Ok(1) } else { Ok(sign) }
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
        let exp_u = exp.to_biguint().ok_or(CryptoError::InvalidInput(
            "non-negative exponent conversion failed",
        ))?;
        return Ok(base.modpow(&exp_u, modulus));
    }

    let inv = modinv(base, modulus)?;
    let abs_exp = (-exp).to_biguint().ok_or(CryptoError::InvalidInput(
        "negative exponent abs conversion failed",
    ))?;
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

/// 把 Fiat-Shamir 输出规约为 `Z_n` 中的非零挑战。
///
/// S1 折叠只需要挑战是公开且不可预测的整数；把它限制到 `Z_n`
/// 可以避免每轮指数和 witness 过快膨胀。若哈希值碰巧为 0，则映射到 1，
/// 这只影响一个可忽略事件，并能保证折叠不会退化成“丢掉左半边”。
fn nonzero_challenge_mod_n(raw: BigUint, n: &BigUint) -> BigUint {
    let challenge = raw % n;
    if challenge.is_zero() {
        BigUint::one()
    } else {
        challenge
    }
}

/// 为 S1 向量承诺派生第 `i` 个基。
///
/// PDF 中的 `cpar=(g_1,...,g_n,h)` 需要一组向量基。当前项目的 `DfParams`
/// 只有 `(g,h)`，因此这里从公共参数和下标确定性派生 `g_i`。验证方可重算
/// 同一组基，不需要把它们额外放进公钥。
///
/// 派生时先哈希到 `Z*_{N^2}`，再取 `candidate^N` 并规约为绝对值代表元，
/// 使基落入与现有 DF/CS 参数一致的 `|QR_{N^2}|` 语义。
fn derive_s1_bases(params: &PpbParams, len: usize) -> CryptoResult<Vec<BigUint>> {
    crate::df::derive_df_vector_bases(&params.cpar, len)
}

/// 计算 S1 向量承诺：
///
/// `C = prod_i bases_i^{values_i} * h^{opening} (mod n^2)`。
fn commit_s1_vector_with_bases(
    params: &PpbParams,
    bases: &[BigUint],
    values: &[BigUint],
    opening: &BigUint,
) -> CryptoResult<BigUint> {
    Ok(crate::df::commit_df_vector_with_bases(&params.cpar, bases, values, opening)?.c)
}

/// 使用确定性派生的 S1 基计算向量承诺。
fn commit_s1_vector(
    params: &PpbParams,
    values: &[BigUint],
    opening: &BigUint,
) -> CryptoResult<BigUint> {
    let bases = derive_s1_bases(params, values.len())?;
    commit_s1_vector_with_bases(params, &bases, values, opening)
}

/// S1 折叠里的密文线性组合：
///
/// `beta ⊙ c_left ⊕ c_right`，即分量级 `c_left^beta * c_right`。
fn fold_s1_ciphertexts(
    left: &crate::cs::CsCiphertext,
    right: &crate::cs::CsCiphertext,
    beta: &BigUint,
    n2: &BigUint,
) -> crate::cs::CsCiphertext {
    let scaled_left = cs_homomorphic_scalar_mul(left, beta, n2);
    cs_homomorphic_add(&scaled_left, right, n2)
}

/// S1 折叠轮次的 Fiat-Shamir 挑战。
///
/// transcript 绑定完整公开语句、当前轮承诺 `C(j)`、当前基/密文向量以及
/// prover 给出的 `(L_j,R_j)`，防止把某轮证明挪到另一条语句中复用。
fn fs_challenge_for_s1_round(
    params: &PpbParams,
    pk: &CsPubKey,
    c_x: &BigUint,
    c_d: &BigUint,
    current_c: &BigUint,
    bases: &[BigUint],
    ciphertexts: &[crate::cs::CsCiphertext],
    l: &BigUint,
    r: &BigUint,
) -> BigUint {
    let mut fields = vec![
        params.cpar.n.clone(),
        params.cpar.n2.clone(),
        params.cpar.g.clone(),
        params.cpar.h.clone(),
        params.hecpar.cs_params.g.clone(),
        params.hecpar.cs_params.h.clone(),
        pk.k.clone(),
        c_x.clone(),
        c_d.clone(),
        current_c.clone(),
        BigUint::from(u64::try_from(bases.len()).unwrap_or(u64::MAX)),
    ];
    for base in bases {
        fields.push(base.clone());
    }
    for ct in ciphertexts {
        fields.push(ct.c0.clone());
        fields.push(ct.c1.clone());
    }
    fields.push(l.clone());
    fields.push(r.clone());

    let refs: Vec<&BigUint> = fields.iter().collect();
    nonzero_challenge_mod_n(fiat_shamir_challenge_biguints(&refs), &params.cpar.n)
}

/// S1 最终证明的 Fiat-Shamir 挑战。
fn fs_challenge_for_s1_final(
    params: &PpbParams,
    pk: &CsPubKey,
    c_x: &BigUint,
    c_d: &BigUint,
    c_star: &BigUint,
    g_star: &BigUint,
    a_star: &crate::cs::CsCiphertext,
    proof: &PpbS1FinalProof,
) -> BigUint {
    fiat_shamir_challenge_biguints(&[
        &params.cpar.n,
        &params.cpar.n2,
        &params.cpar.g,
        &params.cpar.h,
        &params.hecpar.cs_params.g,
        &params.hecpar.cs_params.h,
        &pk.k,
        c_x,
        c_d,
        c_star,
        g_star,
        &a_star.c0,
        &a_star.c1,
        &proof.r_cx,
        &proof.r_cd,
        &proof.r_pk,
        &proof.r_u,
        &proof.r_v,
    ])
}

/// 构造 S1 折叠后的最终证明。
fn build_s1_final_proof(
    params: &PpbParams,
    pk: &CsPubKey,
    c_x: &BigUint,
    c_d: &BigUint,
    c_star: &BigUint,
    g_star: &BigUint,
    a_star: &crate::cs::CsCiphertext,
    x_star: &BigUint,
    r_x_star: &BigUint,
    m_d: &BigUint,
    r_d: &BigUint,
    sk: &BigUint,
    rho_star: &BigUint,
) -> CryptoResult<PpbS1FinalProof> {
    let blind_bits = derive_poks1_blinding_bits(params)?;
    let blind_bits_u64 = u64::try_from(blind_bits)
        .map_err(|_| CryptoError::InvalidInput("S1 blind bits too large"))?;
    let mut rng = OsRng;

    let k_x = rng.gen_biguint(blind_bits_u64);
    let k_rx = rng.gen_biguint(blind_bits_u64);
    let k_md = rng.gen_biguint(blind_bits_u64);
    let k_rd = rng.gen_biguint(blind_bits_u64);
    let k_sk = rng.gen_biguint(blind_bits_u64);
    let k_rho = rng.gen_biguint(blind_bits_u64);

    let r_cx = (g_star.modpow(&k_x, &params.cpar.n2)
        * params.cpar.h.modpow(&k_rx, &params.cpar.n2))
        % &params.cpar.n2;
    let r_cd = (params.cpar.g.modpow(&k_md, &params.cpar.n2)
        * params.cpar.h.modpow(&k_rd, &params.cpar.n2))
        % &params.cpar.n2;
    let r_pk = params.hecpar.cs_params.g.modpow(&k_sk, &params.cpar.n2);
    let r_u = params.hecpar.cs_params.g.modpow(&k_rho, &params.cpar.n2);
    let r_v = (pk.k.modpow(&k_rho, &params.cpar.n2)
        * params.hecpar.cs_params.h.modpow(&k_x, &params.cpar.n2))
        % &params.cpar.n2;

    let mut proof = PpbS1FinalProof {
        r_cx,
        r_cd,
        r_pk,
        r_u,
        r_v,
        z_x: BigUint::zero(),
        z_rx: BigUint::zero(),
        z_md: BigUint::zero(),
        z_rd: BigUint::zero(),
        z_sk: BigUint::zero(),
        z_rho: BigUint::zero(),
    };

    let e = fs_challenge_for_s1_final(params, pk, c_x, c_d, c_star, g_star, a_star, &proof);
    proof.z_x = &k_x + (&e * x_star);
    proof.z_rx = &k_rx + (&e * r_x_star);
    proof.z_md = &k_md + (&e * m_d);
    proof.z_rd = &k_rd + (&e * r_d);
    proof.z_sk = &k_sk + (&e * sk);
    proof.z_rho = &k_rho + (&e * rho_star);

    Ok(proof)
}

/// 验证 S1 折叠后的最终证明。
fn verify_s1_final_proof(
    params: &PpbParams,
    pk: &CsPubKey,
    c_x: &BigUint,
    c_d: &BigUint,
    c_star: &BigUint,
    g_star: &BigUint,
    a_star: &crate::cs::CsCiphertext,
    proof: &PpbS1FinalProof,
) -> CryptoResult<bool> {
    if params.cpar.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if &proof.r_cx >= &params.cpar.n2
        || &proof.r_cd >= &params.cpar.n2
        || &proof.r_pk >= &params.cpar.n2
        || &proof.r_u >= &params.cpar.n2
        || &proof.r_v >= &params.cpar.n2
    {
        return Ok(false);
    }

    let e = fs_challenge_for_s1_final(params, pk, c_x, c_d, c_star, g_star, a_star, proof);
    let two = BigUint::from(2u32);
    let two_e = &two * &e;

    // 1) C* = (g*)^x h^rx。平方不是数学上必需的，但让所有最终等式
    // 使用同一形式，也能和 CS 绝对值代表元的处理保持一致。
    let lhs_cx = (g_star.modpow(&(&two * &proof.z_x), &params.cpar.n2)
        * params.cpar.h.modpow(&(&two * &proof.z_rx), &params.cpar.n2))
        % &params.cpar.n2;
    let rhs_cx = (proof.r_cx.modpow(&two, &params.cpar.n2)
        * c_star.modpow(&two_e, &params.cpar.n2))
        % &params.cpar.n2;

    // 2) Cd = g^{m_d} h^{r_d}，沿用当前工程对 d 的哈希承诺。
    let lhs_cd = (params.cpar.g.modpow(&(&two * &proof.z_md), &params.cpar.n2)
        * params.cpar.h.modpow(&(&two * &proof.z_rd), &params.cpar.n2))
        % &params.cpar.n2;
    let rhs_cd = (proof.r_cd.modpow(&two, &params.cpar.n2) * c_d.modpow(&two_e, &params.cpar.n2))
        % &params.cpar.n2;

    // 3) pkAH = |g_cs^sk|。`pkAH` 使用绝对值代表元，因此验证平方关系。
    let lhs_pk = params
        .hecpar
        .cs_params
        .g
        .modpow(&(&two * &proof.z_sk), &params.cpar.n2);
    let rhs_pk = (proof.r_pk.modpow(&two, &params.cpar.n2) * pk.k.modpow(&two_e, &params.cpar.n2))
        % &params.cpar.n2;

    // 4) A*.c0 = |g_cs^rho|。
    let lhs_u = params
        .hecpar
        .cs_params
        .g
        .modpow(&(&two * &proof.z_rho), &params.cpar.n2);
    let rhs_u = (proof.r_u.modpow(&two, &params.cpar.n2)
        * a_star.c0.modpow(&two_e, &params.cpar.n2))
        % &params.cpar.n2;

    // 5) A*.c1 = |pkAH^rho h_cs^x|。
    let lhs_v = (pk.k.modpow(&(&two * &proof.z_rho), &params.cpar.n2)
        * params
            .hecpar
            .cs_params
            .h
            .modpow(&(&two * &proof.z_x), &params.cpar.n2))
        % &params.cpar.n2;
    let rhs_v = (proof.r_v.modpow(&two, &params.cpar.n2)
        * a_star.c1.modpow(&two_e, &params.cpar.n2))
        % &params.cpar.n2;

    Ok(
        lhs_cx == rhs_cx
            && lhs_cd == rhs_cd
            && lhs_pk == rhs_pk
            && lhs_u == rhs_u
            && lhs_v == rhs_v,
    )
}

/// 验证 PoKS1 证明。
///
/// 验证方只使用公开值：`X=(pkAH,A_i)`、`Cx`、`Cd` 和 `pi_A`。
/// 它重放所有折叠轮次，得到 `(g*, C*, A*)`，再验证最终证明。
fn verify_poks1(params: &PpbParams, pk_a: &PpbPublicKey, c_x: &BigUint) -> CryptoResult<bool> {
    if c_x != &pk_a.c_x {
        return Ok(false);
    }
    if params.cpar.n != params.hecpar.cs_params.n || params.cpar.n2 != params.hecpar.cs_params.n2 {
        return Err(CryptoError::InvalidInput(
            "PoKS1 requires cpar and HEC modulus to match",
        ));
    }
    if pk_a.x_public.encrypted_coeffs.is_empty() {
        return Ok(false);
    }
    if &pk_a.x_public.pk_ah.k >= &params.cpar.n2
        || &pk_a.c_x >= &params.cpar.n2
        || &pk_a.c_d >= &params.cpar.n2
    {
        return Ok(false);
    }
    for ct in &pk_a.x_public.encrypted_coeffs {
        if &ct.c0 >= &params.cpar.n2 || &ct.c1 >= &params.cpar.n2 {
            return Ok(false);
        }
    }

    let original_len = pk_a.x_public.encrypted_coeffs.len();
    let padded_len = original_len.next_power_of_two();
    if pk_a.pi_a.rounds.len() != padded_len.ilog2() as usize {
        return Ok(false);
    }

    let mut bases = derive_s1_bases(params, padded_len)?;
    let mut ciphertexts = pk_a.x_public.encrypted_coeffs.clone();
    while ciphertexts.len() < padded_len {
        ciphertexts.push(crate::cs::CsCiphertext {
            c0: BigUint::one(),
            c1: BigUint::one(),
        });
    }

    let mut current_c = pk_a.c_x.clone();
    for round in &pk_a.pi_a.rounds {
        if &round.l >= &params.cpar.n2 || &round.r >= &params.cpar.n2 {
            return Ok(false);
        }

        let m = bases.len();
        if m < 2 || m % 2 != 0 || ciphertexts.len() != m {
            return Ok(false);
        }

        let beta = fs_challenge_for_s1_round(
            params,
            &pk_a.x_public.pk_ah,
            &pk_a.c_x,
            &pk_a.c_d,
            &current_c,
            &bases,
            &ciphertexts,
            &round.l,
            &round.r,
        );
        let beta_sq = &beta * &beta;
        let half = m / 2;

        let mut next_bases = Vec::with_capacity(half);
        let mut next_ciphertexts = Vec::with_capacity(half);
        for i in 0..half {
            let folded_base =
                (&bases[i] * bases[i + half].modpow(&beta, &params.cpar.n2)) % &params.cpar.n2;
            let folded_ct = fold_s1_ciphertexts(
                &ciphertexts[i],
                &ciphertexts[i + half],
                &beta,
                &params.cpar.n2,
            );
            next_bases.push(folded_base);
            next_ciphertexts.push(folded_ct);
        }

        current_c = (current_c.modpow(&beta, &params.cpar.n2)
            * round.l.modpow(&beta_sq, &params.cpar.n2)
            * &round.r)
            % &params.cpar.n2;
        bases = next_bases;
        ciphertexts = next_ciphertexts;
    }

    if bases.len() != 1 || ciphertexts.len() != 1 {
        return Ok(false);
    }

    verify_s1_final_proof(
        params,
        &pk_a.x_public.pk_ah,
        &pk_a.c_x,
        &pk_a.c_d,
        &current_c,
        &bases[0],
        &ciphertexts[0],
        &pk_a.pi_a.final_proof,
    )
}

fn is_unit_mod_n2(value: &BigUint, n2: &BigUint) -> bool {
    !value.is_zero() && value < n2 && gcd(value.clone(), n2.clone()) == BigUint::one()
}

fn poks3_ciphertext_in_group(ct: &crate::cs::CsCiphertext, n2: &BigUint) -> bool {
    is_unit_mod_n2(&ct.c0, n2) && is_unit_mod_n2(&ct.c1, n2)
}

/// 计算 PoKS3/S3 的 Fiat-Shamir 挑战。
///
/// transcript 绑定完整公开语句 `(pkAH, C_d, Z_hat, z)` 与所有承诺项。
fn fs_challenge_for_poks3(
    params: &PpbParams,
    pk_ah: &CsPubKey,
    c_d: &BigUint,
    z_hat: &HecEvalOutput,
    z: &HecEvalInput,
    proof: &PpbDecProof,
) -> BigUint {
    let fields = vec![
        BigUint::from(0x5333u32),
        params.cpar.n.clone(),
        params.cpar.n2.clone(),
        params.cpar.g.clone(),
        params.cpar.h.clone(),
        params.hecpar.cs_params.n.clone(),
        params.hecpar.cs_params.n2.clone(),
        params.hecpar.cs_params.g.clone(),
        params.hecpar.cs_params.h.clone(),
        pk_ah.k.clone(),
        c_d.clone(),
        z_hat.z_id.c0.clone(),
        z_hat.z_id.c1.clone(),
        z_hat.z_at.c0.clone(),
        z_hat.z_at.c1.clone(),
        z_hat.z_nf.c0.clone(),
        z_hat.z_nf.c1.clone(),
        z.y_id.clone(),
        z.y_at.clone(),
        proof.r_d_commitment.clone(),
        proof.r_pk_commitment.clone(),
        proof.r_z_id.clone(),
        proof.r_z_at.clone(),
        proof.r_z_nf.clone(),
    ];
    let refs: Vec<&BigUint> = fields.iter().collect();
    fiat_shamir_challenge_biguints(&refs)
}

fn poks3_decryption_relation_parts(
    params: &PpbParams,
    ct: &crate::cs::CsCiphertext,
    plaintext: &BigUint,
) -> CryptoResult<(BigUint, BigUint)> {
    let cs_params = &params.hecpar.cs_params;
    if cs_params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if plaintext >= &cs_params.n {
        return Err(CryptoError::InvalidInput("PoKS3 plaintext must be in Z_n"));
    }

    let two = BigUint::from(2u32);
    let two_m = plaintext * &two;
    let base = ct.c0.modpow(&two, &cs_params.n2);
    let h_to_2m = cs_params.h.modpow(&two_m, &cs_params.n2);
    let h_to_2m_inv = modinv(&h_to_2m, &cs_params.n2)?;
    let target = (ct.c1.modpow(&two, &cs_params.n2) * h_to_2m_inv) % &cs_params.n2;

    Ok((base, target))
}

fn poks3_decryption_witness_holds(
    params: &PpbParams,
    d: &HecAuditData,
    ct: &crate::cs::CsCiphertext,
    plaintext: &BigUint,
) -> CryptoResult<bool> {
    let (base, target) = poks3_decryption_relation_parts(params, ct, plaintext)?;
    Ok(base.modpow(&d.sk_e.x, &params.hecpar.cs_params.n2) == target)
}

fn verify_poks3_decryption_equation(
    params: &PpbParams,
    ct: &crate::cs::CsCiphertext,
    plaintext: &BigUint,
    commitment: &BigUint,
    z_sk: &BigInt,
    e: &BigUint,
) -> CryptoResult<bool> {
    let (base, target) = poks3_decryption_relation_parts(params, ct, plaintext)?;
    let lhs = modpow_signed_ppb(&base, z_sk, &params.hecpar.cs_params.n2)?;
    let rhs =
        (commitment * target.modpow(e, &params.hecpar.cs_params.n2)) % &params.hecpar.cs_params.n2;
    Ok(lhs == rhs)
}

/// 验证 PoKS3/S3 证明：
///
/// 1. `C_d = Com_cpar(m_d; r_d)`；
/// 2. `pkAH = |g_enc^{sk_E}|`；
/// 3. `Z_id/Z_at/Z_nf` 分别解密到公开的 `z.y_id/z.y_at/0`。
pub fn verify_poks3(
    params: &PpbParams,
    pk_ah: &CsPubKey,
    c_d: &BigUint,
    z_hat: &HecEvalOutput,
    z: &HecEvalInput,
    proof: &PpbDecProof,
) -> CryptoResult<bool> {
    if params.cpar.n2.is_zero() || params.hecpar.cs_params.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if &params.cpar.n != &params.hecpar.cs_params.n
        || &params.cpar.n2 != &params.hecpar.cs_params.n2
    {
        return Err(CryptoError::InvalidInput(
            "PoKS3 requires cpar and HEC modulus to match",
        ));
    }

    let n = &params.hecpar.cs_params.n;
    let n2 = &params.hecpar.cs_params.n2;
    if &z.y_id >= n || &z.y_at >= n {
        return Ok(false);
    }
    if !is_unit_mod_n2(c_d, n2)
        || !is_unit_mod_n2(&pk_ah.k, n2)
        || !is_unit_mod_n2(&proof.r_d_commitment, n2)
        || !is_unit_mod_n2(&proof.r_pk_commitment, n2)
        || !is_unit_mod_n2(&proof.r_z_id, n2)
        || !is_unit_mod_n2(&proof.r_z_at, n2)
        || !is_unit_mod_n2(&proof.r_z_nf, n2)
        || !poks3_ciphertext_in_group(&z_hat.z_id, n2)
        || !poks3_ciphertext_in_group(&z_hat.z_at, n2)
        || !poks3_ciphertext_in_group(&z_hat.z_nf, n2)
    {
        return Ok(false);
    }

    let e = fs_challenge_for_poks3(params, pk_ah, c_d, z_hat, z, proof);
    let two = BigUint::from(2u32);
    let two_bi = BigInt::from(2u32);
    let two_e = &two * &e;

    let lhs_d = (modpow_signed_ppb(&params.cpar.g, &proof.z_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &proof.z_rd, &params.cpar.n2)?)
        % &params.cpar.n2;
    let rhs_d = (&proof.r_d_commitment * c_d.modpow(&e, &params.cpar.n2)) % &params.cpar.n2;
    if lhs_d != rhs_d {
        return Ok(false);
    }

    let lhs_pk = modpow_signed_ppb(
        &params.hecpar.cs_params.g,
        &(&proof.z_sk * &two_bi),
        &params.hecpar.cs_params.n2,
    )?;
    let rhs_pk = (&proof.r_pk_commitment * pk_ah.k.modpow(&two_e, &params.hecpar.cs_params.n2))
        % &params.hecpar.cs_params.n2;
    if lhs_pk != rhs_pk {
        return Ok(false);
    }

    if !verify_poks3_decryption_equation(
        params,
        &z_hat.z_id,
        &z.y_id,
        &proof.r_z_id,
        &proof.z_sk,
        &e,
    )? {
        return Ok(false);
    }
    if !verify_poks3_decryption_equation(
        params,
        &z_hat.z_at,
        &z.y_at,
        &proof.r_z_at,
        &proof.z_sk,
        &e,
    )? {
        return Ok(false);
    }
    verify_poks3_decryption_equation(
        params,
        &z_hat.z_nf,
        &BigUint::zero(),
        &proof.r_z_nf,
        &proof.z_sk,
        &e,
    )
}

/// 构造 PoKS3/S3 证明对象。
fn build_poks3_proof(
    params: &PpbParams,
    pk_ah: &CsPubKey,
    d: &HecAuditData,
    c_d: &BigUint,
    r_d: &BigUint,
    z_hat: &HecEvalOutput,
    z: &HecEvalInput,
) -> CryptoResult<PpbDecProof> {
    if &params.cpar.n != &params.hecpar.cs_params.n
        || &params.cpar.n2 != &params.hecpar.cs_params.n2
    {
        return Err(CryptoError::InvalidInput(
            "PoKS3 requires cpar and HEC modulus to match",
        ));
    }
    if &z.y_id >= &params.hecpar.cs_params.n || &z.y_at >= &params.hecpar.cs_params.n {
        return Err(CryptoError::InvalidInput("PoKS3 plaintext must be in Z_n"));
    }

    let m_d = map_d_to_df_message(d, &params.cpar.n)?;

    let c_d_expected = commit_df_with_opening(&params.cpar, &m_d, r_d)?.c;
    if c_d_expected != *c_d {
        return Err(CryptoError::InvalidInput(
            "PoKS3 witness does not satisfy Cd = Com(m_d; r_d)",
        ));
    }

    let pk_expected = abs_qr_rep(
        &params
            .hecpar
            .cs_params
            .g
            .modpow(&d.sk_e.x, &params.hecpar.cs_params.n2),
        &params.hecpar.cs_params.n2,
    );
    if &pk_expected != &pk_ah.k {
        return Err(CryptoError::InvalidInput(
            "PoKS3 witness does not match pkAH",
        ));
    }

    if !poks3_decryption_witness_holds(params, d, &z_hat.z_id, &z.y_id)?
        || !poks3_decryption_witness_holds(params, d, &z_hat.z_at, &z.y_at)?
        || !poks3_decryption_witness_holds(params, d, &z_hat.z_nf, &BigUint::zero())?
    {
        return Err(CryptoError::InvalidInput(
            "PoKS3 witness does not decrypt Z_hat to z",
        ));
    }

    let ell = derive_poks1_blinding_bits(params)?;
    let mut rng = OsRng;
    let k_md = sample_symmetric_bigint(&mut rng, ell)?;
    let k_rd = sample_symmetric_bigint(&mut rng, ell)?;
    let k_sk = sample_symmetric_bigint(&mut rng, ell)?;

    let r_d_commitment = (modpow_signed_ppb(&params.cpar.g, &k_md, &params.cpar.n2)?
        * modpow_signed_ppb(&params.cpar.h, &k_rd, &params.cpar.n2)?)
        % &params.cpar.n2;

    let two_bi = BigInt::from(2u32);
    let r_pk_commitment = modpow_signed_ppb(
        &params.hecpar.cs_params.g,
        &(&k_sk * &two_bi),
        &params.hecpar.cs_params.n2,
    )?;
    let (base_id, _) = poks3_decryption_relation_parts(params, &z_hat.z_id, &z.y_id)?;
    let (base_at, _) = poks3_decryption_relation_parts(params, &z_hat.z_at, &z.y_at)?;
    let (base_nf, _) = poks3_decryption_relation_parts(params, &z_hat.z_nf, &BigUint::zero())?;
    let r_z_id = modpow_signed_ppb(&base_id, &k_sk, &params.hecpar.cs_params.n2)?;
    let r_z_at = modpow_signed_ppb(&base_at, &k_sk, &params.hecpar.cs_params.n2)?;
    let r_z_nf = modpow_signed_ppb(&base_nf, &k_sk, &params.hecpar.cs_params.n2)?;

    let mut proof = PpbDecProof {
        r_d_commitment,
        r_pk_commitment,
        r_z_id,
        r_z_at,
        r_z_nf,
        z_md: BigInt::zero(),
        z_rd: BigInt::zero(),
        z_sk: BigInt::zero(),
    };

    let e = fs_challenge_for_poks3(params, pk_ah, c_d, z_hat, z, &proof);
    let e_bi = bu_to_bi(&e)?;
    proof.z_md = &k_md + (&e_bi * bu_to_bi(&m_d)?);
    proof.z_rd = &k_rd + (&e_bi * bu_to_bi(r_d)?);
    proof.z_sk = &k_sk + (&e_bi * bu_to_bi(&d.sk_e.x)?);

    Ok(proof)
}

/// 构造 PoKS1 折叠证明对象。
///
/// 方案 A 的 witness 是 HECenc 真实使用的系数向量 `P_i` 与加密随机数
/// `rho_i`。证明目标不是重新证明 roots 到 coefficients 的展开，而是证明：
///
/// 1. `Cx = Com_vec(P_0,...,P_n; r_x)`；
/// 2. `A_i = Enc_pkAH(P_i; rho_i)`；
/// 3. `Cd = Com(map(d); r_d)`；
/// 4. `pkAH = |g_cs^{sk_E}|`。
///
/// 前两条通过对数折叠压缩成最终单点关系；后两条放入最终证明。
fn build_poks1_proof(
    params: &PpbParams,
    x_public: &HecPublicPackage,
    m_d: &BigUint,
    c_x: &BigUint,
    c_d: &BigUint,
    r_x: &BigUint,
    r_d: &BigUint,
    sk: &BigUint,
    coeffs: &[BigUint],
    coeff_randomness: &[BigUint],
) -> CryptoResult<PpbAuthProof> {
    if params.cpar.n != params.hecpar.cs_params.n || params.cpar.n2 != params.hecpar.cs_params.n2 {
        return Err(CryptoError::InvalidInput(
            "PoKS1 requires cpar and HEC modulus to match",
        ));
    }
    if coeffs.is_empty() {
        return Err(CryptoError::InvalidInput(
            "PoKS1 coefficient vector must be non-empty",
        ));
    }
    if coeffs.len() != x_public.encrypted_coeffs.len() || coeffs.len() != coeff_randomness.len() {
        return Err(CryptoError::InvalidInput(
            "PoKS1 coefficient/randomness length mismatch",
        ));
    }

    // Step 0.1: 检查 Cx 是否确实是系数向量承诺。这样可以避免 prover
    // 对错误语句生成“格式合法”的证明。
    let c_x_expected = commit_s1_vector(params, coeffs, r_x)?;
    if c_x_expected != *c_x {
        return Err(CryptoError::InvalidInput(
            "PoKS1 witness does not satisfy vector Cx",
        ));
    }

    // Step 0.2: 检查公开的每个 A_i 是否由保存的 rho_i 加密对应 P_i。
    for ((coeff, rho), ct) in coeffs
        .iter()
        .zip(coeff_randomness.iter())
        .zip(x_public.encrypted_coeffs.iter())
    {
        let expected =
            enc_cs_with_randomness(&params.hecpar.cs_params, &x_public.pk_ah, coeff, rho)?;
        if !ciphertext_eq_mod_n2(&expected, ct, &params.cpar.n2) {
            return Err(CryptoError::InvalidInput(
                "PoKS1 witness does not satisfy A_i encryption",
            ));
        }
    }

    let c_d_expected = commit_df_with_opening(&params.cpar, m_d, r_d)?.c;
    if c_d_expected != *c_d {
        return Err(CryptoError::InvalidInput(
            "PoKS1 witness does not satisfy Cd = Com(m_d; r_d)",
        ));
    }

    // Step 1: 为折叠补齐到 2 的幂。补零项不会改变 Cx，因为指数为 0；
    // 对应的密文使用 Enc(0;0)=(1,1)，验证方也可以确定性补齐。
    let padded_len = coeffs.len().next_power_of_two();
    let mut bases = derive_s1_bases(params, padded_len)?;
    let mut values = coeffs.to_vec();
    let mut rhos = coeff_randomness.to_vec();
    let mut ciphertexts = x_public.encrypted_coeffs.clone();
    while values.len() < padded_len {
        values.push(BigUint::zero());
        rhos.push(BigUint::zero());
        ciphertexts.push(crate::cs::CsCiphertext {
            c0: BigUint::one(),
            c1: BigUint::one(),
        });
    }

    let blind_bits = derive_poks1_blinding_bits(params)?;
    let blind_bits_u64 = u64::try_from(blind_bits)
        .map_err(|_| CryptoError::InvalidInput("S1 blind bits too large"))?;
    let mut rng = OsRng;
    let mut current_c = c_x.clone();
    let mut current_rx = r_x.clone();
    let mut rounds = Vec::with_capacity(padded_len.ilog2() as usize);

    // Step 2: 对数折叠。为了在当前 DF 群中保持精确等式，本实现使用
    // `g'_i = g_L,i * g_R,i^beta` 与 `x'_i = beta*x_L,i + x_R,i`。
    // 它和 PDF 的折叠思想相同，但避免了 `beta^{-1}` 在未知群阶指数里
    // 可能造成的工程化歧义。
    while values.len() > 1 {
        let m = values.len();
        let half = m / 2;

        let lambda = rng.gen_biguint(blind_bits_u64);
        let mu = rng.gen_biguint(blind_bits_u64);

        let l = commit_s1_vector_with_bases(params, &bases[half..], &values[..half], &lambda)?;
        let r = commit_s1_vector_with_bases(params, &bases[..half], &values[half..], &mu)?;
        let beta = fs_challenge_for_s1_round(
            params,
            &x_public.pk_ah,
            c_x,
            c_d,
            &current_c,
            &bases,
            &ciphertexts,
            &l,
            &r,
        );
        let beta_sq = &beta * &beta;

        let mut next_bases = Vec::with_capacity(half);
        let mut next_values = Vec::with_capacity(half);
        let mut next_rhos = Vec::with_capacity(half);
        let mut next_ciphertexts = Vec::with_capacity(half);
        for i in 0..half {
            next_bases.push(
                (&bases[i] * bases[i + half].modpow(&beta, &params.cpar.n2)) % &params.cpar.n2,
            );
            next_values.push((&beta * &values[i]) + &values[i + half]);
            next_rhos.push((&beta * &rhos[i]) + &rhos[i + half]);
            next_ciphertexts.push(fold_s1_ciphertexts(
                &ciphertexts[i],
                &ciphertexts[i + half],
                &beta,
                &params.cpar.n2,
            ));
        }

        current_c =
            (current_c.modpow(&beta, &params.cpar.n2) * l.modpow(&beta_sq, &params.cpar.n2) * &r)
                % &params.cpar.n2;
        current_rx = (&beta * &current_rx) + (&beta_sq * &lambda) + &mu;

        rounds.push(PpbS1FoldRound { l, r });
        bases = next_bases;
        values = next_values;
        rhos = next_rhos;
        ciphertexts = next_ciphertexts;
    }

    let final_proof = build_s1_final_proof(
        params,
        &x_public.pk_ah,
        c_x,
        c_d,
        &current_c,
        &bases[0],
        &ciphertexts[0],
        &values[0],
        &current_rx,
        m_d,
        r_d,
        sk,
        &rhos[0],
    )?;

    Ok(PpbAuthProof {
        rounds,
        final_proof,
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

/// `VerPK(Λ, pkA, Cx)` 的内部实现。
///
/// 当前做结构一致性校验：
/// 1. 声明的 `Cx` 与 `pkA.c_x` 一致；
/// 2. `X` 结构完整（系数非空且与多项式长度一致）；
/// 3. `Cx/Cd` 在 `Z_{n^2}` 范围内；
/// 4. `pi_A`（PoKS1）验证通过。
fn verify_pk_inner(params: &PpbParams, pk_a: &PpbPublicKey, c_x: &BigUint) -> bool {
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
    if &pk_a.c_x >= &params.cpar.n2 || &pk_a.c_d >= &params.cpar.n2 {
        return false;
    }
    let poks1_ok = match verify_poks1(params, pk_a, c_x) {
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
    verify_pk_inner(params, pk_a, c_x)
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

    // Step 3: 用【setup 固定的】 pk_sky 加密 `m_y` 得 `C_sky`，并构造 `pi_sky`。
    //
    // 关键点：
    // 1. pk_sky 必须取自公共参数 `params.sky_pk`，【不能】由 prover 现场生成；
    //    否则无人持有陷门私钥，直线可提取性失效（见 PpbParams.sky_pk 说明）。
    // 2. 先做真实 CS 加密，再用 `com_ah_with_zero_randomness` 包装为 Ca；
    // 3. `prove_cs_enc` 的 `Cy` 直接使用外部公共输入 `C_y`，把 sky 密文与用户承诺绑定。
    let pk_sky = params.sky_pk.clone();
    let mut rng = OsRng;
    let r_sky = rng.gen_biguint_below(n);
    let c_sky = enc_cs_with_randomness(&params.hecpar.cs_params, &pk_sky, &m_y, &r_sky)?;
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
    // 必须与 PoKP 递归用的是同一套折叠求值（见 CiphertextPolynomial::evaluate_with_powers）。
    let e_poly = pk_a.x_public.polynomial.evaluate_mod_n(&y_id, n)?;
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
        return Err(CryptoError::InvalidInput("Z_nf does not match r3 ⊙ E_poly"));
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
    let y_id_enc =
        enc_cs_with_randomness(&params.hecpar.cs_params, &pk_a.x_public.pk_ah, &y_id, &rid)?;
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
    let y_at_enc =
        enc_cs_with_randomness(&params.hecpar.cs_params, &pk_a.x_public.pk_ah, &y_at, &rat)?;
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
fn build_cs_commit_params_from_user_proof(
    params: &PpbParams,
    ah_g: &BigUint,
) -> CryptoResult<CsCommitParams> {
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
fn build_enc_statement_commitment(
    params_ah: &CsCommitParams,
    ct: &crate::cs::CsCiphertext,
) -> CsCommitment {
    CsCommitment {
        c1: &ct.c0 % &params_ah.n2,
        c2: BigUint::one(),
        c3: &ct.c1 % &params_ah.n2,
        c4: BigUint::one(),
    }
}

/// 查询 `Cy_{2^i}` 的公共承诺值。
///
/// 约定：
/// 1. `power=1` 时直接返回根承诺 `Cy`；
/// 2. `power=2^i` 时从 `aux.round=i` 的条目读取。
fn lookup_cy_for_power_from_aux(
    power: usize,
    root_cy: &BigUint,
    aux: &[PoKAuxEntry],
) -> CryptoResult<BigUint> {
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
        .ok_or(CryptoError::InvalidInput(
            "aux does not contain required Cy(2^i)",
        ))?;
    Ok(entry.cy_2i.clone())
}

/// 复现 PoK* 每轮的 Fiat-Shamir `alpha` 挑战。
///
/// 与 `pok.rs::fs_alpha_for_pok_star` 保持完全相同的字段顺序，
/// 防止挑战重建不一致。
fn fs_alpha_for_pok_star_verify(
    c1: &CsCommitment,
    c2: &CsCommitment,
    c3: &CsCommitment,
    tau: &PoKTranscript,
) -> BigUint {
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
    fields.extend(tau.history.iter().cloned());

    let refs: Vec<&BigUint> = fields.iter().collect();
    fiat_shamir_challenge_biguints(&refs)
}

fn bigint_to_transcript_uint_ppb(value: &BigInt) -> BigUint {
    if value >= &BigInt::zero() {
        let mut out = value.to_biguint().unwrap_or_else(BigUint::zero);
        out <<= 1usize;
        out += BigUint::one();
        return out;
    }

    let abs = (-value).to_biguint().unwrap_or_else(BigUint::zero);
    abs << 1usize
}

fn append_commitment_fields_for_pok_star(fields: &mut Vec<BigUint>, commitment: &CsCommitment) {
    fields.push(commitment.c1.clone());
    fields.push(commitment.c2.clone());
    fields.push(commitment.c3.clone());
    fields.push(commitment.c4.clone());
}

fn append_cs_com_proof_fields_for_pok_star(fields: &mut Vec<BigUint>, proof: &CsComProof) {
    fields.push(proof.r2.clone());
    fields.push(proof.r4.clone());
    fields.push(proof.z_s1.clone());
    fields.push(proof.z_r1.clone());
    fields.push(proof.z_s2.clone());
    fields.push(proof.z_r2.clone());
}

fn append_cs_add_proof_fields_for_pok_star(fields: &mut Vec<BigUint>, proof: &CsAddProof) {
    fields.push(proof.e.clone());
    fields.push(bigint_to_transcript_uint_ppb(&proof.z1));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z2));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z3));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z4));
}

fn append_cs_mult_proof_fields_for_pok_star(fields: &mut Vec<BigUint>, proof: &CsMultProof) {
    fields.push(proof.r_y.clone());
    fields.push(proof.r1.clone());
    fields.push(proof.r2.clone());
    fields.push(proof.r3.clone());
    fields.push(proof.r4.clone());
    fields.push(bigint_to_transcript_uint_ppb(&proof.z_y));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z_ry));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z1));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z2));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z3));
    fields.push(bigint_to_transcript_uint_ppb(&proof.z4));
}

fn append_round_to_tau_for_pok_star(
    tau: &PoKTranscript,
    round: &crate::pok::PoKStarRoundProof,
) -> PoKTranscript {
    let mut history = tau.history.clone();
    append_commitment_fields_for_pok_star(&mut history, &round.c1);
    append_commitment_fields_for_pok_star(&mut history, &round.c2);
    append_commitment_fields_for_pok_star(&mut history, &round.c3);
    append_commitment_fields_for_pok_star(&mut history, &round.c_alpha_e3);
    append_commitment_fields_for_pok_star(&mut history, &round.c_p_prime);
    history.push(round.alpha.clone());
    history.push(round.cy_half.clone());
    history.push(round.cy_alpha.clone());
    history.push(round.pi_cy_alpha.r_commitment.clone());
    history.push(round.pi_cy_alpha.z_r.clone());
    append_cs_com_proof_fields_for_pok_star(&mut history, &round.pi_c1);
    append_cs_com_proof_fields_for_pok_star(&mut history, &round.pi_c2);
    append_cs_com_proof_fields_for_pok_star(&mut history, &round.pi_c3);
    append_cs_com_proof_fields_for_pok_star(&mut history, &round.pi_c_alpha_e3);
    append_cs_com_proof_fields_for_pok_star(&mut history, &round.pi_c_p_prime);
    append_cs_add_proof_fields_for_pok_star(&mut history, &round.pi_e_eq_e1_plus_e2);
    append_cs_mult_proof_fields_for_pok_star(&mut history, &round.pi_e2_eq_y_half_mul_e3);
    append_cs_mult_proof_fields_for_pok_star(&mut history, &round.pi_alpha_mul_e3);
    append_cs_add_proof_fields_for_pok_star(&mut history, &round.pi_eprime_eq_e1_plus_alphae3);

    PoKTranscript {
        cy: tau.cy.clone(),
        c_values: tau.c_values.clone(),
        c_p: tau.c_p.clone(),
        history,
    }
}

/// 验证当前 `PoKPProof` 格式中 verifier 可独立检查的公共部分。
///
/// 递归时按 `tau'=(pi,tau)` 追加公开轮次字段，因此每一层的 Fiat-Shamir
/// `alpha` 都能由 verifier 重建，同时 `Cy_alpha` 必须证明其确实打开到该公开挑战。
fn verify_pok_star_public_shell(
    params_ah: &CsCommitParams,
    params_df_for_alpha: &DfParams,
    root_cy: &BigUint,
    current_c_values: &[crate::cs::CsCiphertext],
    current_c_p_commitment: &CsCommitment,
    aux: &[PoKAuxEntry],
    proof: &PoKStarProof,
    tau: &PoKTranscript,
) -> CryptoResult<bool> {
    if current_c_values.is_empty() || !current_c_values.len().is_power_of_two() {
        return Ok(false);
    }

    match proof {
        PoKStarProof::Base { pi_open_cp } => {
            if current_c_values.len() != 1 {
                return Ok(false);
            }
            // 关键锚定（论文 Alg.2 基例 π1）：验证 CP 打开到【公开】的折叠输入
            // 密文 current_c_values[0]，而不是只验证“存在某个开口”。
            // 该公开值由验证方自己从公开密文 A_i 逐层折叠得到，完全脱离 prover
            // 控制，因此堵住了“prover 任意伪造 E”的可靠性缺口。
            verify_cs_com_ciphertext(
                params_ah,
                current_c_p_commitment,
                &current_c_values[0],
                pi_open_cp,
            )
        }
        PoKStarProof::Recursive { round, next } => {
            if current_c_values.len() < 2 || current_c_values.len() % 2 != 0 {
                return Ok(false);
            }

            if !verify_cs_com(params_ah, &round.c1, &round.pi_c1)?
                || !verify_cs_com(params_ah, &round.c2, &round.pi_c2)?
                || !verify_cs_com(params_ah, &round.c3, &round.pi_c3)?
                || !verify_cs_com(params_ah, &round.c_alpha_e3, &round.pi_c_alpha_e3)?
                || !verify_cs_com(params_ah, &round.c_p_prime, &round.pi_c_p_prime)?
            {
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

            if !verify_df_open_public_scalar(
                params_df_for_alpha,
                &round.cy_alpha,
                &round.alpha,
                &round.pi_cy_alpha,
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

            let expected_alpha = fs_alpha_for_pok_star_verify(&round.c1, &round.c2, &round.c3, tau);
            if expected_alpha != round.alpha {
                return Ok(false);
            }
            let tau_next = append_round_to_tau_for_pok_star(tau, round);

            let poly = CiphertextPolynomial::new(current_c_values.to_vec(), &params_ah.n2)?;
            let (lower_poly, upper_poly) = poly.split_in_half();
            let folded_poly = lower_poly.fold(&upper_poly, &round.alpha);
            let next_values = folded_poly.coeffs().to_vec();

            verify_pok_star_public_shell(
                params_ah,
                params_df_for_alpha,
                root_cy,
                &next_values,
                &round.c_p_prime,
                aux,
                next,
                &tau_next,
            )
        }
    }
}

fn verify_pokp_public_components(
    params_ah: &CsCommitParams,
    params_df: &DfParams,
    cy: &BigUint,
    c_values: &[crate::cs::CsCiphertext],
    proof: &PoKPProof,
) -> CryptoResult<Option<crate::cs::CsCiphertext>> {
    if c_values.is_empty() || !c_values.len().is_power_of_two() {
        return Ok(None);
    }
    if proof.tau.cy != *cy || proof.tau.c_values.len() != c_values.len() {
        return Ok(None);
    }
    if !proof.tau.history.is_empty() {
        return Ok(None);
    }
    for (lhs, rhs) in proof.tau.c_values.iter().zip(c_values.iter()) {
        if !ciphertext_eq_mod_n2(lhs, rhs, &params_ah.n2) {
            return Ok(None);
        }
    }

    let e_poly = proof.tau.c_p.clone();
    let c_p_wrapped = com_ah_with_zero_randomness(params_ah, &e_poly)?;
    if proof.c_p_commitment.c1 != c_p_wrapped.commitment.c1
        || proof.c_p_commitment.c2 != c_p_wrapped.commitment.c2
        || proof.c_p_commitment.c3 != c_p_wrapped.commitment.c3
        || proof.c_p_commitment.c4 != c_p_wrapped.commitment.c4
    {
        return Ok(None);
    }

    // aux 链只需覆盖到 round = rounds-1：最高层的 half = len/2 = 2^{rounds-1}。
    let rounds = c_values.len().ilog2() as usize;
    let aux_rounds = rounds.saturating_sub(1);
    if proof.aux.len() != aux_rounds {
        return Ok(None);
    }

    let mut prev_cy = cy.clone();
    for i in 1..=aux_rounds {
        let entry = &proof.aux[i - 1];
        if entry.round != i {
            return Ok(None);
        }
        if &entry.cy_2i >= &params_df.n2 || &entry.c_w >= &params_df.n2 || &entry.c_k >= &params_df.n2
        {
            return Ok(None);
        }

        // (1) C_w 承诺的是上一轮标量的**整数**平方。
        if !verify_df_square_mult(params_df, &prev_cy, &entry.c_w, &entry.pi_y2i)? {
            return Ok(None);
        }

        // (2) 论文 Remark 1 的模 n 归约检查：C_w == C_{ŝ_i} · C_k^n (mod n²)。
        // 它把 `ŝ_{i-1}^2 = ŝ_i + k·n` 钉死，从而保证进入下一轮（以及被
        // verify_cs_mult 消费）的标量始终是 Z_n 中的约简值，
        // 承诺见证不会随轮次按 2^i 膨胀。
        let reduced_rhs =
            (&entry.cy_2i * entry.c_k.modpow(&params_df.n, &params_df.n2)) % &params_df.n2;
        if reduced_rhs != entry.c_w {
            return Ok(None);
        }

        prev_cy = entry.cy_2i.clone();
    }

    let params_df_for_alpha = DfParams {
        n: params_ah.n.clone(),
        n2: params_ah.n2.clone(),
        g: params_ah.g_prime.clone(),
        h: params_ah.h_prime.clone(),
    };

    if !verify_pok_star_public_shell(
        params_ah,
        &params_df_for_alpha,
        cy,
        c_values,
        &proof.c_p_commitment,
        &proof.aux,
        &proof.recursive_proof,
        &proof.tau,
    )? {
        return Ok(None);
    }

    Ok(Some(e_poly))
}


fn verify_enc_mul_add_component(
    params_ah: &CsCommitParams,
    pk_ah: &CsPubKey,
    c_plain: &BigUint,
    c_scalar: &BigUint,
    e_commitment: &CsCommitment,
    z_component: &crate::cs::CsCiphertext,
    proof: &PpbEncMulAddProof,
) -> CryptoResult<bool> {
    if !verify_cs_enc(params_ah, &pk_ah.k, &proof.c_enc, c_plain, &proof.pi_enc)? {
        return Ok(false);
    }
    if !verify_cs_mult(
        params_ah,
        &proof.c_mul,
        e_commitment,
        c_scalar,
        &proof.pi_mult,
    )? {
        return Ok(false);
    }

    let z_commitment = build_enc_statement_commitment(params_ah, z_component);
    verify_cs_add(
        params_ah,
        &proof.c_enc,
        &proof.c_mul,
        &z_commitment,
        &proof.pi_add,
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
    if c_y != &escrow_out.c_y {
        return Ok(false);
    }

    let proof = &escrow_out.pi_u;
    let params_ah = build_cs_commit_params_from_user_proof(params, &proof.ah_g)?;
    let n2 = &params.cpar.n2;

    if &proof.c_id >= n2
        || &proof.c_at >= n2
        || &proof.c_r1 >= n2
        || &proof.c_r2 >= n2
        || &proof.c_r3 >= n2
    {
        return Ok(false);
    }

    let c_y_from_cid_cat = (&proof.c_id * &proof.c_at) % n2;
    if !proof.pi_y.relation_holds || proof.pi_y.c_y_from_cid_cat != *c_y || c_y_from_cid_cat != *c_y
    {
        return Ok(false);
    }

    // sky 加密必须在【setup 固定的】 pk_sky 下完成：拒绝任何 prover 自带的
    // pk_sky，否则直线可提取性失效（陷门无人持有）。
    if proof.pk_sky != params.sky_pk {
        return Ok(false);
    }
    let c_sky_statement = build_enc_statement_commitment(&params_ah, &proof.c_sky);
    if !verify_cs_enc(
        &params_ah,
        &params.sky_pk.k,
        &c_sky_statement,
        c_y,
        &proof.pi_sky,
    )? {
        return Ok(false);
    }

    let Some(e_poly) = verify_pokp_public_components(
        &params_ah,
        &params.cpar,
        &proof.c_id,
        &pk_a.x_public.encrypted_coeffs,
        &proof.pi_poly,
    )?
    else {
        return Ok(false);
    };
    let e_commitment = build_enc_statement_commitment(&params_ah, &e_poly);

    // pi_nf 证明 Z_nf = E_poly ⊙ r3（r3 承诺于 c_r3）。结合修复后的 pi_poly
    // （E_poly 已被基例锚定为真正的 Enc(P(y_id))），Dec(Z_nf)=0 等价于
    // r3·P(y_id) ≡ 0 (mod n)。
    //
    // ⚠️ 残留缺口（非可框架性）：此处【未】证明 r3 在 mod n 下可逆（等价地
    // r3 ≠ 0）。若恶意用户取 r3=0，则 Z_nf=Enc(0) 恒解密为 0，绕过 watchlist
    // 门；在 Soundness 游戏中（敌手自选 x，故知道名单）可配合 r1 令 Z_id 命中
    // 某个名单项，从而对一个非成员 y 得到 Dec≠⊥=f(x,y)，违反非可框架性。
    //
    // 正确修复需要证明 gcd(r3,n)=1（论文 Fig D.3 HECeval 把“r3=0⟹⊥”并入被证
    // 关系；实现层对应论文 Remark 1 的 eqrep-n* 模 n 乘法证明：附带 C_{r3inv}
    // 并证明 r3·r3inv ≡ 1 (mod n)）。该证明的可靠性依赖 DF 承诺基 (g,h) 的
    // Paillier 结构（例如 h 取 n 次剩余以消去 (1+n)-分量），而当前 setup_ppb 里
    // g,h 是无约束单位元，直接手搓会不可靠。故此处暂以断言/文档标注，
    // 不落地一个可能不可靠的证明。TODO(non-frameability): 落地 r3 可逆证明
    // 并相应约束 cpar 的 (g,h) 生成。
    let z_nf_commitment = build_enc_statement_commitment(&params_ah, &escrow_out.z_hat.z_nf);
    if !verify_cs_mult(
        &params_ah,
        &z_nf_commitment,
        &e_commitment,
        &proof.c_r3,
        &proof.pi_nf,
    )? {
        return Ok(false);
    }

    if !verify_enc_mul_add_component(
        &params_ah,
        &pk_a.x_public.pk_ah,
        &proof.c_id,
        &proof.c_r1,
        &e_commitment,
        &escrow_out.z_hat.z_id,
        &proof.pi_id,
    )? {
        return Ok(false);
    }

    verify_enc_mul_add_component(
        &params_ah,
        &pk_a.x_public.pk_ah,
        &proof.c_at,
        &proof.c_r2,
        &e_commitment,
        &escrow_out.z_hat.z_at,
        &proof.pi_at,
    )
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
/// 3. `Cx <- Com_cpar(P_0,...,P_n; r_x)`（方案 A：承诺 HEC 系数向量），`Cd <- Com_cpar(d; r_d)`；
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
    //
    // 这里必须使用 KeyGen 入参 `s` 作为 HEC 多项式掩码；否则 PoKS1
    // 证明的系数向量和公开的 `A_i` 不是同一份 HECenc 随机性下的输出。
    let hec_out = hec_enc_with_mask(&params.hecpar, fk, x, s)?;

    // Step 3: 方案 A 下，Cx 承诺的是 HECenc 实际加密的系数向量 P_i。
    // 这使 PDF/S1 折叠中的 `c_i` 可以直接对应当前代码里的 `A_i`。
    let c_x = commit_s1_vector(params, &hec_out.enc_witness.masked_coeffs, r_x)?;

    // Cd 使用标准 DF 承诺。
    let m_d = map_d_to_df_message(&hec_out.d_audit, &params.cpar.n)?;
    let d_randomness_bits = derive_df_commit_randomness_bits(params)?;
    let c_d_with_opening = commit_df(&params.cpar, &m_d, d_randomness_bits)?;

    // Step 4: 构造 PoKS1 折叠证明。
    let pi_a = build_poks1_proof(
        params,
        &hec_out.x_public,
        &m_d,
        &c_x,
        &c_d_with_opening.c,
        r_x,
        &c_d_with_opening.r,
        &hec_out.d_audit.sk_e.x,
        &hec_out.enc_witness.masked_coeffs,
        &hec_out.enc_witness.encryption_randomness,
    )?;

    // Step 5~6: 组装公私钥。
    let pk_a = PpbPublicKey {
        x_public: hec_out.x_public.clone(),
        fk: fk.clone(),
        c_x,
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
    // Step 2~4: VerPK 校验。
    if !verify_pk_inner(params, pk_a, &pk_a.c_x) {
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
/// 6. 若 `z` 为空，返回失败；否则构造 S3，证明 `Z_hat` 正确解密为 `z`；
/// 7. return `(z, pi_Z)`。
///
/// 返回 `Ok(None)` 表示第 4 步失败或 HECdec 未得到具体公开 `z`（算法中的 `⊥`）；
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
    let Some(z_value) = z.as_ref() else {
        return Ok(None);
    };
    let pi_z = build_poks3_proof(
        params,
        &sk_a.pk_a.x_public.pk_ah,
        &sk_a.d,
        &sk_a.pk_a.c_d,
        &sk_a.r_d,
        &escrow_out.z_hat,
        z_value,
    )?;

    Ok(Some(PpbDecOutput { z, pi_z }))
}

/// Judge(Λ, pkA, Cx, Cy, Z=(Ẑ, πU), z, πZ)。
///
/// 对应你给出的算法流程：
/// 1. parse `Λ=(λ,cpar,hecpar,S1,S2,S3)`；
/// 2. parse `pkA=(_,_,C_d,_)`；
/// 3. 计算 `VS3((z,hecpar,pkAH,Ẑ,C_d), πZ)`；
/// 4. 计算 `VerPK(Λ, pkA, Cx)`；
/// 5. 计算 `VerEscrow(Λ, pkA, Cy, Z)`；
/// 6. 返回三者逻辑与。
///
/// 工程映射说明：
/// 1. 当前代码库里的 VS3 对应 `verify_poks3(...)`；
/// 2. 若 `z` 为 `None`，S3 没有公开解密值可绑定，直接返回 `false`；
/// 3. 为保持输入语义与算法一致，这里会先检查 `Cy == Z.c_y`。
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

    let z_value = match z {
        Some(v) => v,
        None => return Ok(false),
    };

    if !verify_poks3(
        params,
        &pk_a.x_public.pk_ah,
        &pk_a.c_d,
        &escrow_out.z_hat,
        z_value,
        pi_z,
    )? {
        return Ok(false);
    }

    if !verify_pk(params, pk_a, c_x) {
        return Ok(false);
    }

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
        assert_eq!(
            ppb.hecpar.cs_params.n2,
            &ppb.hecpar.cs_params.n * &ppb.hecpar.cs_params.n
        );
    }

    #[test]
    fn test_setup_ppb_rejects_invalid_lambda() {
        let res = setup_ppb(31, &(), &(), &());
        assert!(res.is_err());
    }

    #[test]
    fn test_keygen_ppb_builds_pk_and_sk() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let s = BigUint::from(1u32);

        let (pk_a, sk_a) =
            keygen_ppb(&params, &fk, &x, &r_x, &s).expect("keygen ppb should succeed");

        assert_eq!(pk_a.x_public.encrypted_coeffs.len(), x.len() + 1);
        assert_eq!(pk_a.x_public.polynomial.len(), x.len() + 1);
        assert_eq!(pk_a.fk, fk);
        assert_eq!(sk_a.d.fk, fk);
        assert_eq!(sk_a.d.x, x);
        assert_eq!(sk_a.pk_a.c_x, pk_a.c_x);
        assert_eq!(sk_a.pk_a.c_d, pk_a.c_d);

        // KeyGen 输出的 pi_A 必须是可验证的 PoKS1 证明。
        let ok = verify_poks1(&params, &pk_a, &pk_a.c_x).expect("verify poks1 should run");
        assert!(ok);
    }

    #[test]
    fn test_keygen_ppb_poks1_rejects_tampered_proof() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);

        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

        // 篡改 PoKS1 最终 Schnorr 响应中的一个分量，应导致验证失败。
        pk_a.pi_a.final_proof.z_x += BigUint::from(1u32);

        let ok = verify_poks1(&params, &pk_a, &pk_a.c_x).expect("verify poks1 should run");
        assert!(!ok);
    }

    #[test]
    fn test_keygen_ppb_commitments_match_processed_messages() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(19u32);
        let s = BigUint::from(1u32);

        let (pk_a, sk_a) =
            keygen_ppb(&params, &fk, &x, &r_x, &s).expect("keygen ppb should succeed");

        // 方案 A 中，c_x 承诺的是 HECenc 实际加密的掩码多项式系数。
        // 这些系数不再等同于原始 roots，因此这里用 PoKS1 验证公开承诺
        // 与公开密文包 X 的一致性，而不是按旧的 roots 承诺公式重算。
        let poks1_ok = verify_poks1(&params, &pk_a, &pk_a.c_x).expect("verify poks1 should run");
        let m_d = map_d_to_df_message(&sk_a.d, &params.cpar.n).expect("map d should succeed");

        let c_d_expected =
            commit_df_with_opening(&params.cpar, &m_d, &sk_a.r_d).expect("commit d should succeed");

        assert!(poks1_ok);
        assert_eq!(pk_a.c_d, c_d_expected.c);
    }

    #[test]
    fn test_keygen_ppb_rejects_fk_length_mismatch() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![BigUint::from(3u32), BigUint::from(8u32)];
        let fk = HecFunctionKey { n: 3, k: 1 };
        let r_x = BigUint::from(17u32);

        let err = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect_err("mismatched length should be rejected");
        assert_eq!(err, CryptoError::InvalidInput("fk.n must equal x.len()"));
    }

    #[test]
    fn test_escrow_ppb_returns_output_and_cy() {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let c_y_expected =
            commit_df_with_opening(&params.cpar, &m_y, &r_y_mod).expect("commit y should succeed");

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
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

        // 把 Cx 篡改到群外范围，触发 VerPK 失败。
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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(31u32);
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

        // 篡改公钥内 fk，使其与 X 的系数规模不一致，VerPK 应拒绝。
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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        out.pi_u.pi_id.c_mul.c1 =
            (&out.pi_u.pi_id.c_mul.c1 + BigUint::from(1u32)) % &params.cpar.n2;

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        // false 条件：任一子证明验证失败（这里会在 pi_id 的 mult/add 链路失败）。
        assert!(!ok);
    }

    fn valid_poks2_fixture() -> (PpbParams, PpbPublicKey, PpbEscrowOutput) {
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);
        let out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        (params, pk_a, out)
    }

    #[test]
    fn test_verify_poks2_rejects_tampered_pi_sky() {
        let (params, pk_a, mut out) = valid_poks2_fixture();
        out.pi_u.pi_sky.z_y += BigInt::from(1u32);

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    /// 修复2回归测试：sky 公钥必须等于 setup 固定的 params.sky_pk。
    /// 若 prover 自带另一把 pk_sky（旧实现允许，导致直线可提取性失效），
    /// verify_poks2 必须直接拒绝。
    #[test]
    fn test_verify_poks2_rejects_prover_supplied_sky_pk() {
        let (params, pk_a, mut out) = valid_poks2_fixture();

        // 用一把与 params.sky_pk 不同的公钥替换证明里的 pk_sky。
        let (other_pk, _other_sk) =
            keygen_cs(&params.hecpar.cs_params).expect("keygen should succeed");
        assert_ne!(other_pk, params.sky_pk);
        out.pi_u.pk_sky = other_pk;

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_verify_poks2_rejects_tampered_pi_nf() {
        let (params, pk_a, mut out) = valid_poks2_fixture();
        out.pi_u.pi_nf.z1 += BigInt::from(1u32);

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_verify_poks2_rejects_tampered_pi_poly_anchor() {
        let (params, pk_a, mut out) = valid_poks2_fixture();
        out.pi_u.pi_poly.c_p_commitment.c1 =
            (&out.pi_u.pi_poly.c_p_commitment.c1 + BigUint::from(1u32)) % &params.cpar.n2;

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_verify_poks2_rejects_tampered_pi_poly_cy_alpha() {
        let (params, pk_a, mut out) = valid_poks2_fixture();
        match &mut out.pi_u.pi_poly.recursive_proof {
            PoKStarProof::Recursive { round, .. } => {
                round.cy_alpha = (&round.cy_alpha + BigUint::from(1u32)) % &params.cpar.n2;
            }
            PoKStarProof::Base { .. } => panic!("fixture should produce a recursive PoK* proof"),
        }

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_verify_poks2_rejects_tampered_pi_poly_cy_alpha_opening() {
        let (params, pk_a, mut out) = valid_poks2_fixture();
        match &mut out.pi_u.pi_poly.recursive_proof {
            PoKStarProof::Recursive { round, .. } => {
                round.pi_cy_alpha.z_r += BigUint::from(1u32);
            }
            PoKStarProof::Base { .. } => panic!("fixture should produce a recursive PoK* proof"),
        }

        let ok = verify_poks2(&params, &pk_a, &out.c_y, &out).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_verify_escrow_accepts_valid_output() {
        // 正例：VerPK 和 VS2 都成立，VerEscrow 应返回 true。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (mut pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
    fn test_verify_escrow_rejects_when_vs2_fails() {
        // 反例 2：保留合法 pkA，但篡改 pi_U 子语句使 VS2 失败，VerEscrow 应返回 false。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, _sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

        let y = HecEvalInput {
            y_id: BigUint::from(11u32),
            y_at: BigUint::from(29u32),
        };
        let r_y = BigUint::from(41u32);

        let mut out = escrow_ppb(&params, &pk_a, &y, &r_y)
            .expect("escrow should run")
            .expect("escrow output should exist");

        // 篡改 VS2 语句的一部分：pi_id 中 mult 的承诺项。
        out.pi_u.pi_id.c_mul.c1 =
            (&out.pi_u.pi_id.c_mul.c1 + BigUint::from(1u32)) % &params.cpar.n2;

        let ok = verify_escrow(&params, &pk_a, &out.c_y, &out).expect("verify escrow should run");
        assert!(!ok);
    }

    #[test]
    fn test_dec_ppb_returns_output_and_valid_poks3() {
        // 正例：VerEscrow 通过后，Dec 应返回 (z, pi_Z)，且 PoKS3 可验证。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let z = dec_out
            .z
            .expect("hec dec should output identity in this case");
        assert_eq!(z.y_id, y.y_id % &params.cpar.n);
        assert_eq!(z.y_at, y.y_at % &params.cpar.n);

        let ok = verify_poks3(
            &params,
            &pk_a.x_public.pk_ah,
            &pk_a.c_d,
            &out.z_hat,
            &z,
            &dec_out.pi_z,
        )
        .expect("verify poks3 should run");
        assert!(ok);
    }

    #[test]
    fn test_dec_ppb_returns_none_when_verescrow_fails() {
        // 反例：若 VerEscrow 失败，Dec 必须返回 None（算法中的 ⊥）。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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

        let z = dec_out
            .z
            .as_ref()
            .expect("hec dec should output identity in this case");
        let ok = verify_poks3(
            &params,
            &pk_a.x_public.pk_ah,
            &pk_a.c_d,
            &out.z_hat,
            z,
            &dec_out.pi_z,
        )
        .expect("verify poks3 should run");
        assert!(!ok);
    }

    #[test]
    fn test_judge_ppb_accepts_valid_tuple() {
        // 正例：VS3、VerPK、VerEscrow 同时通过，Judge 必须返回 true。
        let params = setup_ppb(64, &(), &(), &()).expect("setup ppb should succeed");
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
        let x = vec![
            BigUint::from(5u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
        ];
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = BigUint::from(37u32);
        let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32))
            .expect("keygen ppb should succeed");

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
