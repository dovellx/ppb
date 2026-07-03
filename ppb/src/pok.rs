use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::rngs::OsRng;

use crate::cs::CsCiphertext;
use crate::cs_commit::{
    commit_cs, prove_cs_add, prove_cs_com, prove_cs_com_ciphertext, prove_cs_mult, CsAddProof,
    CsComCtProof, CsComProof, CsCommitOpening, CsCommitParams, CsCommitment,
    CsCommitmentWithOpening, CsMultProof,
};
use crate::df::{commit_df, DfParams};
use crate::error::{CryptoError, CryptoResult};
use crate::hash::fiat_shamir_challenge_biguints;
use crate::math::{derive_b_bits_from_n2, modinv};

/// 与论文记号对齐的类型别名：
/// - `Scalar` 对应标量 y、alpha、y^(2^i) 等指数值；
/// - `CamenischShoupCiphertext` 对应 CS 密文 xi。
pub type Scalar = BigUint;
pub type CamenischShoupCiphertext = CsCiphertext;

/// 密文多项式封装：f(X) = sum_{i=0}^{n-1} coeffs[i] * X^i。
///
/// 设计目标：
/// 1. 将多项式层面的操作（求值、劈裂、折叠）封装成固定 API；
/// 2. 后续 `pok_star_p` 只通过该结构体方法操作多项式，避免散落逻辑；
/// 3. `n2` 内置到结构体中，确保同态运算始终在同一模数下执行。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CiphertextPolynomial {
    coeffs: Vec<CamenischShoupCiphertext>,
    n2: BigUint,
}

impl CiphertextPolynomial {
    /// 从系数向量创建密文多项式。
    ///
    /// 约束：
    /// 1. `coeffs` 不可为空；
    /// 2. `n2` 必须非零。
    pub fn new(coeffs: Vec<CamenischShoupCiphertext>, n2: &BigUint) -> CryptoResult<Self> {
        if coeffs.is_empty() {
            return Err(CryptoError::InvalidInput("ciphertext polynomial must be non-empty"));
        }
        if n2.is_zero() {
            return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
        }
        Ok(Self {
            coeffs,
            n2: n2.clone(),
        })
    }

    /// 返回多项式系数切片（只读）。
    pub fn coeffs(&self) -> &[CamenischShoupCiphertext] {
        &self.coeffs
    }

    /// 返回当前多项式的项数 n。
    pub fn len(&self) -> usize {
        self.coeffs.len()
    }

    /// CS 密文同态加法：Enc(m1) ⊕ Enc(m2) = Enc(m1 + m2)。
    fn homomorphic_add(
        left: &CamenischShoupCiphertext,
        right: &CamenischShoupCiphertext,
        n2: &BigUint,
    ) -> CamenischShoupCiphertext {
        CamenischShoupCiphertext {
            c0: (&left.c0 * &right.c0) % n2,
            c1: (&left.c1 * &right.c1) % n2,
        }
    }

    /// CS 密文同态标量乘法：k ⊙ Enc(m) = Enc(k * m)。
    fn homomorphic_scalar_mul(
        value: &CamenischShoupCiphertext,
        scalar: &Scalar,
        n2: &BigUint,
    ) -> CamenischShoupCiphertext {
        CamenischShoupCiphertext {
            c0: value.c0.modpow(scalar, n2),
            c1: value.c1.modpow(scalar, n2),
        }
    }

    /// 利用密文同态加法和标量乘法求多项式在 y 处的值。
    ///
    /// 实现采用 Horner 形式：
    /// f(y) = (...((x_{n-1} * y + x_{n-2}) * y + ...) * y + x_0)
    ///
    /// 优点：
    /// 1. 避免显式维护 y^i；
    /// 2. 运算次数为 O(n) 且逻辑清晰；
    /// 3. 每步都只调用“密文加法 + 标量乘法”两种基础同态操作。
    pub fn evaluate(&self, y: &Scalar) -> CamenischShoupCiphertext {
        let mut iter = self.coeffs.iter().rev();
        let Some(last) = iter.next() else {
            return CamenischShoupCiphertext {
                c0: BigUint::one(),
                c1: BigUint::one(),
            };
        };

        let mut acc = last.clone();
        for coeff in iter {
            acc = Self::homomorphic_scalar_mul(&acc, y, &self.n2);
            acc = Self::homomorphic_add(coeff, &acc, &self.n2);
        }
        acc
    }

    /// 把多项式按项数一分为二，返回 (lower, upper)。
    ///
    /// lower = [x0, ..., x_{n/2-1}]
    /// upper = [x_{n/2}, ..., x_{n-1}]
    ///
    /// 该方法要求项数为偶数；Algorithm 2 递归过程本身依赖这一条件。
    pub fn split_in_half(&self) -> (CiphertextPolynomial, CiphertextPolynomial) {
        assert!(
            self.coeffs.len() >= 2 && self.coeffs.len() % 2 == 0,
            "split_in_half requires even polynomial length >= 2"
        );

        let mid = self.coeffs.len() / 2;
        (
            CiphertextPolynomial {
                coeffs: self.coeffs[..mid].to_vec(),
                n2: self.n2.clone(),
            },
            CiphertextPolynomial {
                coeffs: self.coeffs[mid..].to_vec(),
                n2: self.n2.clone(),
            },
        )
    }

    /// 执行对应项密文折叠：x'_i = x_i ⊕ (x_{i+n/2} ⊙ alpha)。
    ///
    /// 注意：
    /// 1. `self` 视为 lower half；`upper_poly` 视为 upper half；
    /// 2. 两者长度必须一致，且共享同一 `n2`；
    /// 3. 返回新的“降阶后”多项式，长度减半。
    pub fn fold(&self, upper_poly: &CiphertextPolynomial, alpha: &Scalar) -> CiphertextPolynomial {
        assert_eq!(
            self.coeffs.len(),
            upper_poly.coeffs.len(),
            "fold requires equal lower/upper lengths"
        );
        assert_eq!(self.n2, upper_poly.n2, "fold requires identical n^2");

        let mut folded = Vec::with_capacity(self.coeffs.len());
        for i in 0..self.coeffs.len() {
            let upper_scaled = Self::homomorphic_scalar_mul(&upper_poly.coeffs[i], alpha, &self.n2);
            folded.push(Self::homomorphic_add(&self.coeffs[i], &upper_scaled, &self.n2));
        }

        CiphertextPolynomial {
            coeffs: folded,
            n2: self.n2.clone(),
        }
    }
}

/// 单轮 y^(2^i) 承诺辅助数据。
///
/// 字段说明：
/// 1. round: 当前轮次 i（从 1 开始）
/// 2. cy_2i: 对 y^(2^i) 的 DF 承诺值
/// 3. pi_y2i: 连接前一轮与当前轮的平方关系 NIZK 证明
#[derive(Debug, Clone)]
pub struct PoKAuxEntry {
    pub round: usize,
    pub cy_2i: BigUint,
    pub pi_y2i: ProveMultProof,
}

/// prover 内部保存的 aux 开口；不会进入公开证明对象。
#[derive(Debug, Clone)]
struct PoKAuxOpeningEntry {
    round: usize,
    cy_2i: BigUint,
    r_i: BigUint,
}

/// 算法中的公共 transcript: tau = (Cy, c0, ..., c_{n-1}, cP)
#[derive(Debug, Clone)]
pub struct PoKTranscript {
    pub cy: BigUint,
    pub c_values: Vec<CsCiphertext>,
    pub c_p: CsCiphertext,
    pub history: Vec<BigUint>,
}

/// ProveMult 的标准证明对象。
///
/// 证明格式：
/// pi = (R1, R2, z_z, z_rin, z_gamma)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProveMultProof {
    pub r1: BigUint,
    pub r2: BigUint,
    pub z_z: BigInt,
    pub z_rin: BigInt,
    pub z_gamma: BigInt,
}

/// DF 承诺对公开消息的开口证明。
///
/// 用于绑定 `Cy_alpha` 确实承诺 Fiat-Shamir 得到的公开 alpha，而不是另一个标量。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DfOpenProof {
    pub r_commitment: BigUint,
    pub z_r: BigUint,
}

/// 一层递归证明节点的公共输出。
///
/// 对应 Algorithm 2 中单轮 `pi = (C1, C2, C3, C'_P, pi_alpha)`，
/// 这里将 `pi_alpha` 展开为当前工程里可用的 NIZK 原语组合。
#[derive(Debug, Clone)]
pub struct PoKStarRoundProof {
    pub c1: CsCommitment,
    pub c2: CsCommitment,
    pub c3: CsCommitment,
    pub c_alpha_e3: CsCommitment,
    pub c_p_prime: CsCommitment,
    pub alpha: BigUint,
    pub cy_half: BigUint,
    pub cy_alpha: BigUint,
    pub pi_cy_alpha: DfOpenProof,
    pub pi_c1: CsComProof,
    pub pi_c2: CsComProof,
    pub pi_c3: CsComProof,
    pub pi_c_alpha_e3: CsComProof,
    pub pi_c_p_prime: CsComProof,
    pub pi_e_eq_e1_plus_e2: CsAddProof,
    pub pi_e2_eq_y_half_mul_e3: CsMultProof,
    pub pi_alpha_mul_e3: CsMultProof,
    pub pi_eprime_eq_e1_plus_alphae3: CsAddProof,
}

/// PoK*_P 递归证明对象。
///
/// - `Base`: n=1 时只需证明 CP 打开正确；
/// - `Recursive`: 记录当前轮证明并携带下一轮子证明。
#[derive(Debug, Clone)]
pub enum PoKStarProof {
    /// 递归基例（n=1）：对应论文 Alg.2 line 1 的
    ///   π1 = NIZK[r : Com_AH(⌊x0⌋, r) = CP]。
    ///
    /// 这里必须用 `CsComCtProof`（“对公开密文 x0 开口”），而不是旧的
    /// `CsComProof`（只证“知道某个开口”）。后者不把 CP 绑定到那个公开的、
    /// 折叠后的输入密文 x0，会让简洁求值证明的可靠性被击穿。
    Base { pi_open_cp: CsComCtProof },
    Recursive {
        round: PoKStarRoundProof,
        next: Box<PoKStarProof>,
    },
}

/// Algorithm 1 的最终输出。
///
/// 输出形式对应：
/// return aux, PoK*_P(...)
#[derive(Debug, Clone)]
pub struct PoKPProof {
    pub aux: Vec<PoKAuxEntry>,
    pub tau: PoKTranscript,
    pub c_p_commitment: CsCommitment,
    pub recursive_proof: PoKStarProof,
}

/// 使用 AH/CS 承诺语义对 cP 进行“零随机数”包装：CP <- Com_AH(cP; 0)
///
/// 结合现有 CS 承诺定义：
/// C = (C1, C2, C3, C4)
/// C1 = a1 * c0 * g^{s1}, C2 = b1 * (g')^{s1}(h')^{r1}
/// C3 = a2 * c1 * g^{s2}, C4 = b2 * (g')^{s2}(h')^{r2}
///
/// 当开口固定为：
/// a1=a2=b1=b2=+1, s1=s2=r1=r2=0
/// 可得：
/// C1=c0, C2=1, C3=c1, C4=1
fn com_ah_with_zero_randomness(
    params_ah: &CsCommitParams,
    c_p: &CsCiphertext,
) -> CryptoResult<CsCommitmentWithOpening> {
    if params_ah.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let commitment = CsCommitment {
        c1: &c_p.c0 % &params_ah.n2,
        c2: BigUint::one(),
        c3: &c_p.c1 % &params_ah.n2,
        c4: BigUint::one(),
    };

    let opening = CsCommitOpening {
        a1: 1,
        a2: 1,
        s1: BigUint::zero(),
        s2: BigUint::zero(),
        r1: BigUint::zero(),
        r2: BigUint::zero(),
        b1: 1,
        b2: 1,
    };

    Ok(CsCommitmentWithOpening { commitment, opening })
}

/// 计算默认的 AH/CS 承诺随机位长。
///
/// 统一口径：B + lambda。
fn default_cs_commit_randomness_bits(params_ah: &CsCommitParams) -> CryptoResult<usize> {
    derive_b_bits_from_n2(&params_ah.n2)?
        .checked_add(params_ah.lambda_bits)
        .ok_or(CryptoError::InvalidInput("B+lambda overflow"))
}

/// 计算默认的 DF 承诺随机位长。
///
/// 统一口径：B + lambda。
fn default_df_randomness_bits(params_ah: &CsCommitParams) -> CryptoResult<usize> {
    default_cs_commit_randomness_bits(params_ah)
}

/// 把 AH 参数中的 (n, g', h') 映射为 DF 参数结构。
fn df_params_from_ah(params_ah: &CsCommitParams) -> DfParams {
    DfParams {
        n: params_ah.n.clone(),
        n2: params_ah.n2.clone(),
        g: params_ah.g_prime.clone(),
        h: params_ah.h_prime.clone(),
    }
}

/// 在整数域计算 base^exp（exp 为 usize）。
fn pow_scalar_usize(base: &Scalar, mut exp: usize) -> Scalar {
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

/// 查询 `y^(power)` 的 DF 承诺与开口随机数。
///
/// 映射规则：
/// - power = 1 时，直接使用 (Cy, r_y)；
/// - power = 2^i (i>=1) 时，来自 `aux` 中 round=i 的条目。
fn lookup_cy_for_power(
    power: usize,
    cy: &BigUint,
    r_y: &BigUint,
    aux_openings: &[PoKAuxOpeningEntry],
) -> CryptoResult<(BigUint, BigUint)> {
    if power == 1 {
        return Ok((cy.clone(), r_y.clone()));
    }
    if !power.is_power_of_two() {
        return Err(CryptoError::InvalidInput("power must be a power of two"));
    }

    let round = power.ilog2() as usize;
    if round == 0 {
        return Ok((cy.clone(), r_y.clone()));
    }

    let entry = aux_openings
        .iter()
        .find(|e| e.round == round)
        .ok_or(CryptoError::InvalidInput("aux does not contain required y^(2^i) commitment"))?;
    Ok((entry.cy_2i.clone(), entry.r_i.clone()))
}

fn append_commitment_fields(fields: &mut Vec<BigUint>, commitment: &CsCommitment) {
    fields.push(commitment.c1.clone());
    fields.push(commitment.c2.clone());
    fields.push(commitment.c3.clone());
    fields.push(commitment.c4.clone());
}

fn append_cs_com_proof_fields(fields: &mut Vec<BigUint>, proof: &CsComProof) {
    fields.push(proof.r2.clone());
    fields.push(proof.r4.clone());
    fields.push(proof.z_s1.clone());
    fields.push(proof.z_r1.clone());
    fields.push(proof.z_s2.clone());
    fields.push(proof.z_r2.clone());
}

fn append_cs_add_proof_fields(fields: &mut Vec<BigUint>, proof: &CsAddProof) {
    fields.push(proof.e.clone());
    fields.push(bigint_to_transcript_uint(&proof.z1));
    fields.push(bigint_to_transcript_uint(&proof.z2));
    fields.push(bigint_to_transcript_uint(&proof.z3));
    fields.push(bigint_to_transcript_uint(&proof.z4));
}

fn append_cs_mult_proof_fields(fields: &mut Vec<BigUint>, proof: &CsMultProof) {
    fields.push(proof.r_y.clone());
    fields.push(proof.r1.clone());
    fields.push(proof.r2.clone());
    fields.push(proof.r3.clone());
    fields.push(proof.r4.clone());
    fields.push(bigint_to_transcript_uint(&proof.z_y));
    fields.push(bigint_to_transcript_uint(&proof.z_ry));
    fields.push(bigint_to_transcript_uint(&proof.z1));
    fields.push(bigint_to_transcript_uint(&proof.z2));
    fields.push(bigint_to_transcript_uint(&proof.z3));
    fields.push(bigint_to_transcript_uint(&proof.z4));
}

fn bigint_to_transcript_uint(value: &BigInt) -> BigUint {
    if value >= &BigInt::zero() {
        let mut out = value.to_biguint().unwrap_or_else(BigUint::zero);
        out <<= 1usize;
        out += BigUint::one();
        return out;
    }

    let abs = (-value).to_biguint().unwrap_or_else(BigUint::zero);
    abs << 1usize
}

fn append_round_to_tau(tau: &PoKTranscript, round: &PoKStarRoundProof) -> PoKTranscript {
    let mut history = tau.history.clone();
    append_commitment_fields(&mut history, &round.c1);
    append_commitment_fields(&mut history, &round.c2);
    append_commitment_fields(&mut history, &round.c3);
    append_commitment_fields(&mut history, &round.c_alpha_e3);
    append_commitment_fields(&mut history, &round.c_p_prime);
    history.push(round.alpha.clone());
    history.push(round.cy_half.clone());
    history.push(round.cy_alpha.clone());
    history.push(round.pi_cy_alpha.r_commitment.clone());
    history.push(round.pi_cy_alpha.z_r.clone());
    append_cs_com_proof_fields(&mut history, &round.pi_c1);
    append_cs_com_proof_fields(&mut history, &round.pi_c2);
    append_cs_com_proof_fields(&mut history, &round.pi_c3);
    append_cs_com_proof_fields(&mut history, &round.pi_c_alpha_e3);
    append_cs_com_proof_fields(&mut history, &round.pi_c_p_prime);
    append_cs_add_proof_fields(&mut history, &round.pi_e_eq_e1_plus_e2);
    append_cs_mult_proof_fields(&mut history, &round.pi_e2_eq_y_half_mul_e3);
    append_cs_mult_proof_fields(&mut history, &round.pi_alpha_mul_e3);
    append_cs_add_proof_fields(&mut history, &round.pi_eprime_eq_e1_plus_alphae3);

    PoKTranscript {
        cy: tau.cy.clone(),
        c_values: tau.c_values.clone(),
        c_p: tau.c_p.clone(),
        history,
    }
}

/// 计算输出/输入开口符号的“商”向量（在 {-1,+1} 上与乘法等价）。
fn derive_mult_signs(
    output_opening: &CsCommitOpening,
    input_opening: &CsCommitOpening,
    exp: &BigInt,
) -> CryptoResult<[i8; 4]> {
    let exp_is_even = (exp % BigInt::from(2u32)) == BigInt::zero();
    let in_a1_exp = if exp_is_even { 1i16 } else { i16::from(input_opening.a1) };
    let in_b1_exp = if exp_is_even { 1i16 } else { i16::from(input_opening.b1) };
    let in_a2_exp = if exp_is_even { 1i16 } else { i16::from(input_opening.a2) };
    let in_b2_exp = if exp_is_even { 1i16 } else { i16::from(input_opening.b2) };

    let s1 = i16::from(output_opening.a1) * in_a1_exp;
    let s2 = i16::from(output_opening.b1) * in_b1_exp;
    let s3 = i16::from(output_opening.a2) * in_a2_exp;
    let s4 = i16::from(output_opening.b2) * in_b2_exp;

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

/// 计算 Algorithm 2 中每轮折叠挑战 alpha。
///
/// 公式对应：
/// alpha <- H(C1, C2, C3, tau)
///
/// 这里的 tau 采用工程转写：
/// tau = (Cy, c0, ..., c_{n-1}, cP)。
fn fs_alpha_for_pok_star(c1: &CsCommitment, c2: &CsCommitment, c3: &CsCommitment, tau: &PoKTranscript) -> BigUint {
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

fn fs_challenge_for_df_open_public_scalar(
    params_df: &DfParams,
    commitment: &BigUint,
    message: &BigUint,
    r_commitment: &BigUint,
) -> BigUint {
    fiat_shamir_challenge_biguints(&[
        &params_df.n,
        &params_df.g,
        &params_df.h,
        commitment,
        message,
        r_commitment,
    ])
}

/// 计算平方关系证明的 Fiat-Shamir 挑战：
/// e <- Hash(n, g', h', C_in, C_out, R1, R2)
fn fs_challenge_for_square_df(
    params_df: &DfParams,
    c_in: &BigUint,
    c_out: &BigUint,
    r1: &BigUint,
    r2: &BigUint,
) -> BigUint {
    fiat_shamir_challenge_biguints(&[&params_df.n, &params_df.g, &params_df.h, c_in, c_out, r1, r2])
}

/// BigUint -> BigInt 的安全转换辅助。
fn bu_to_bi(v: &BigUint) -> CryptoResult<BigInt> {
    v.to_bigint()
        .ok_or(CryptoError::InvalidInput("BigUint->BigInt conversion failed"))
}

/// 有符号指数模幂：base^exp mod modulus。
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

/// 证明 Cy2i-1 与 Cy2i 之间满足 z -> z^2 的关系。
///
/// 目标关系：
/// Cy_prev = Com(z; r_prev)
/// Cy_next = Com(z^2; r_next)
///
/// 算法细节对应你给出的流程：
/// 1. 在整数域计算 gamma = r_out - z * r_in（可为负）；
/// 2. 按位长上界采样盲化值 k_z, k_rin, k_gamma；
/// 3. 计算 R1, R2，使用 Fiat-Shamir 生成挑战 e；
/// 4. 输出响应 z_z, z_rin, z_gamma。
pub fn prove_mult(
    params_df: &DfParams,
    cy_prev: &BigUint,
    r_prev: &BigUint,
    cy_next: &BigUint,
    r_next: &BigUint,
    z: &BigUint,
) -> CryptoResult<ProveMultProof> {
    // 对外接口保留原签名，用于兼容已有调用点。
    // 这里把 lambda 的来源显式写清楚：
    // 1) 在 PoKP 主流程中，我们会走 prove_mult_with_lambda(..., params_ah.lambda_bits)；
    // 2) 若调用方单独直接使用 prove_mult，则降级为“按 n 位长估计 lambda”；
    // 3) 这样既不破坏接口，又把协议主路径保持为“显式安全参数输入”。
    let default_lambda_bits = usize::try_from(params_df.n.bits())
        .map_err(|_| CryptoError::InvalidInput("n bit length too large"))?;
    prove_mult_with_lambda(
        params_df,
        cy_prev,
        r_prev,
        cy_next,
        r_next,
        z,
        default_lambda_bits,
    )
}

/// `prove_mult` 的内部实现：显式接收安全参数 lambda 位长。
fn prove_mult_with_lambda(
    params_df: &DfParams,
    cy_prev: &BigUint,
    r_prev: &BigUint,
    cy_next: &BigUint,
    r_next: &BigUint,
    z: &BigUint,
    lambda_bits: usize,
) -> CryptoResult<ProveMultProof> {
    if params_df.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if lambda_bits == 0 {
        return Err(CryptoError::InvalidInput("lambda_bits must be > 0"));
    }

    // 先检查 witness 与公共输入是否一致，避免对错误实例出证明。
    let expected_in = (params_df.g.modpow(z, &params_df.n2) * params_df.h.modpow(r_prev, &params_df.n2)) % &params_df.n2;
    if &expected_in != cy_prev {
        return Err(CryptoError::InvalidInput("witness does not satisfy C_in commitment equation"));
    }

    let z_sq = z * z;
    let expected_out = (params_df.g.modpow(&z_sq, &params_df.n2) * params_df.h.modpow(r_next, &params_df.n2)) % &params_df.n2;
    if &expected_out != cy_next {
        return Err(CryptoError::InvalidInput("witness does not satisfy C_out commitment equation"));
    }

    // gamma = r_out - z * r_in（整数域，可为负）。
    let r_out_bi = bu_to_bi(r_next)?;
    let z_bi = bu_to_bi(z)?;
    let r_in_bi = bu_to_bi(r_prev)?;
    let gamma = r_out_bi - (&z_bi * &r_in_bi);

    // 与现有实现统一：B 由 n^2 位长近似推导，lambda 由上层传入。
    let b_bits = derive_b_bits_from_n2(&params_df.n2)?;

    let k_z_bits = b_bits
        .checked_add(
            lambda_bits
                .checked_mul(2)
                .ok_or(CryptoError::InvalidInput("2*lambda overflow"))?,
        )
        .ok_or(CryptoError::InvalidInput("B+2lambda overflow"))?;
    let k_rin_bits = k_z_bits;
    let k_gamma_bits = b_bits
        .checked_mul(2)
        .and_then(|v| v.checked_add(lambda_bits.checked_mul(2)?))
        .ok_or(CryptoError::InvalidInput("2B+2lambda overflow"))?;

    let k_z_bits_u64 = u64::try_from(k_z_bits).map_err(|_| CryptoError::InvalidInput("B+2lambda too large"))?;
    let k_rin_bits_u64 = u64::try_from(k_rin_bits).map_err(|_| CryptoError::InvalidInput("B+2lambda too large"))?;
    let k_gamma_bits_u64 = u64::try_from(k_gamma_bits).map_err(|_| CryptoError::InvalidInput("2B+2lambda too large"))?;

    let mut rng = OsRng;
    let k_z = rng.gen_biguint(k_z_bits_u64);
    let k_rin = rng.gen_biguint(k_rin_bits_u64);
    let k_gamma = rng.gen_biguint(k_gamma_bits_u64);

    // Commit 阶段。
    let r1 = (params_df.g.modpow(&k_z, &params_df.n2) * params_df.h.modpow(&k_rin, &params_df.n2)) % &params_df.n2;
    let r2 = (cy_prev.modpow(&k_z, &params_df.n2) * params_df.h.modpow(&k_gamma, &params_df.n2)) % &params_df.n2;

    // Challenge 阶段。
    let e = fs_challenge_for_square_df(params_df, cy_prev, cy_next, &r1, &r2);
    let e_bi = bu_to_bi(&e)?;

    // Response 阶段（整数域线性组合）。
    let z_z = bu_to_bi(&k_z)? + (&e_bi * &z_bi);
    let z_rin = bu_to_bi(&k_rin)? + (&e_bi * &r_in_bi);
    let z_gamma = bu_to_bi(&k_gamma)? + (&e_bi * &gamma);

    Ok(ProveMultProof {
        r1,
        r2,
        z_z,
        z_rin,
        z_gamma,
    })
}

/// 验证平方关系证明：
/// 1) g'^z_z * h'^z_rin ?= R1 * C_in^e
/// 2) C_in^z_z * h'^z_gamma ?= R2 * C_out^e
pub fn verify_mult(
    params_df: &DfParams,
    cy_prev: &BigUint,
    cy_next: &BigUint,
    proof: &ProveMultProof,
) -> CryptoResult<bool> {
    if params_df.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let e = fs_challenge_for_square_df(params_df, cy_prev, cy_next, &proof.r1, &proof.r2);

    let lhs_1 = (modpow_signed(&params_df.g, &proof.z_z, &params_df.n2)?
        * modpow_signed(&params_df.h, &proof.z_rin, &params_df.n2)?)
        % &params_df.n2;
    let rhs_1 = (&proof.r1 * cy_prev.modpow(&e, &params_df.n2)) % &params_df.n2;

    let lhs_2 = (modpow_signed(cy_prev, &proof.z_z, &params_df.n2)?
        * modpow_signed(&params_df.h, &proof.z_gamma, &params_df.n2)?)
        % &params_df.n2;
    let rhs_2 = (&proof.r2 * cy_next.modpow(&e, &params_df.n2)) % &params_df.n2;

    Ok(lhs_1 == rhs_1 && lhs_2 == rhs_2)
}

/// 证明 DF 承诺 `commitment = g^message h^r` 打开到公开消息 `message`。
pub fn prove_df_open_public_scalar(
    params_df: &DfParams,
    commitment: &BigUint,
    message: &BigUint,
    r: &BigUint,
    lambda_bits: usize,
) -> CryptoResult<DfOpenProof> {
    if params_df.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }
    if lambda_bits == 0 {
        return Err(CryptoError::InvalidInput("lambda_bits must be > 0"));
    }

    let expected = (params_df.g.modpow(message, &params_df.n2) * params_df.h.modpow(r, &params_df.n2)) % &params_df.n2;
    if &expected != commitment {
        return Err(CryptoError::InvalidInput("DF opening witness does not match commitment"));
    }

    let blind_bits = derive_b_bits_from_n2(&params_df.n2)?
        .checked_add(
            lambda_bits
                .checked_mul(2)
                .ok_or(CryptoError::InvalidInput("2*lambda overflow"))?,
        )
        .ok_or(CryptoError::InvalidInput("B+2lambda overflow"))?;
    let blind_bits_u64 = u64::try_from(blind_bits).map_err(|_| CryptoError::InvalidInput("B+2lambda too large"))?;

    let mut rng = OsRng;
    let k_r = rng.gen_biguint(blind_bits_u64);
    let r_commitment = params_df.h.modpow(&k_r, &params_df.n2);
    let e = fs_challenge_for_df_open_public_scalar(params_df, commitment, message, &r_commitment);
    let z_r = k_r + (&e * r);

    Ok(DfOpenProof { r_commitment, z_r })
}

/// 验证 DF 承诺 `commitment` 打开到公开消息 `message`。
pub fn verify_df_open_public_scalar(
    params_df: &DfParams,
    commitment: &BigUint,
    message: &BigUint,
    proof: &DfOpenProof,
) -> CryptoResult<bool> {
    if params_df.n2.is_zero() {
        return Err(CryptoError::InvalidInput("n^2 must be non-zero"));
    }

    let g_m = params_df.g.modpow(message, &params_df.n2);
    let g_m_inv = modinv(&g_m, &params_df.n2)?;
    let h_r = (commitment * g_m_inv) % &params_df.n2;
    let e = fs_challenge_for_df_open_public_scalar(params_df, commitment, message, &proof.r_commitment);
    let lhs = params_df.h.modpow(&proof.z_r, &params_df.n2);
    let rhs = (&proof.r_commitment * h_r.modpow(&e, &params_df.n2)) % &params_df.n2;

    Ok(lhs == rhs)
}

/// 递归实现 Algorithm 2 的内部函数。
///
/// 该函数只依赖 `CiphertextPolynomial` 的 `evaluate/split_in_half/fold` 三个方法
/// 完成多项式层面的变换，确保“多项式语义”集中管理在一个结构体里。
fn pok_star_recursive(
    params_ah: &CsCommitParams,
    params_df_for_alpha: &DfParams,
    r_y: &BigUint,
    y: &BigUint,
    c_p: &CsCiphertext,
    r_p: &CsCommitOpening,
    cy: &BigUint,
    poly: &CiphertextPolynomial,
    c_p_commitment: &CsCommitment,
    aux_openings: &[PoKAuxOpeningEntry],
    tau: &PoKTranscript,
) -> CryptoResult<PoKStarProof> {
    // Base case: n=1。
    //
    // 论文要求这里证明的是“CP 打开到那个【公开】的折叠输入密文 x0”，
    // 而不是“CP 存在某个开口”。此时 poly 只剩一个系数，且 c_p 恰好等于
    // 该系数（单系数多项式的 Horner 求值就是它本身），因此 x0 = c_p。
    // 用 prove_cs_com_ciphertext 把 CP 锚定到 c_p，堵住基例可靠性缺口。
    if poly.len() == 1 {
        let pi_open_cp = prove_cs_com_ciphertext(params_ah, c_p_commitment, c_p, r_p)?;
        return Ok(PoKStarProof::Base { pi_open_cp });
    }

    // 约束当前层必须可二分。
    if poly.len() % 2 != 0 {
        return Err(CryptoError::InvalidInput(
            "polynomial length must be even in recursive PoK*_P",
        ));
    }

    // 1) 二分多项式：x = [x_low | x_up]
    let (lower_poly, upper_poly) = poly.split_in_half();

    // 2) 计算三组关键中间密文值：
    //    e1 = sum x_i * y^i (lower)
    //    e3 = sum x_{i+n/2} * y^i (upper lowered)
    //    e2 = y^(n/2) ⊙ e3
    let e1 = lower_poly.evaluate(y);
    let e3 = upper_poly.evaluate(y);

    let half = poly.len() / 2;
    let y_half = pow_scalar_usize(y, half);
    let e2 = CiphertextPolynomial::homomorphic_scalar_mul(&e3, &y_half, &params_ah.n2);

    // 用当前层语句检查 e = e1 ⊕ e2 是否匹配，避免“错误实例”继续递归。
    let e_expected = CiphertextPolynomial::homomorphic_add(&e1, &e2, &params_ah.n2);
    if (e_expected.c0 % &params_ah.n2) != (&c_p.c0 % &params_ah.n2)
        || (e_expected.c1 % &params_ah.n2) != (&c_p.c1 % &params_ah.n2)
    {
        return Err(CryptoError::InvalidInput(
            "current statement does not satisfy e = e1 + e2",
        ));
    }

    // 3) 对 e1/e2/e3 做 AH 承诺并输出 opening 见证。
    let cs_rand_bits = default_cs_commit_randomness_bits(params_ah)?;
    let c1_with_open = commit_cs(params_ah, &e1, cs_rand_bits)?;
    let c2_with_open = commit_cs(params_ah, &e2, cs_rand_bits)?;
    let c3_with_open = commit_cs(params_ah, &e3, cs_rand_bits)?;

    // 4) 分别证明这些新承诺可正确打开。
    let pi_c1 = prove_cs_com(params_ah, &c1_with_open.commitment, &c1_with_open.opening)?;
    let pi_c2 = prove_cs_com(params_ah, &c2_with_open.commitment, &c2_with_open.opening)?;
    let pi_c3 = prove_cs_com(params_ah, &c3_with_open.commitment, &c3_with_open.opening)?;

    // 5) Fiat-Shamir 折叠挑战 alpha。
    let alpha = fs_alpha_for_pok_star(
        &c1_with_open.commitment,
        &c2_with_open.commitment,
        &c3_with_open.commitment,
        tau,
    );

    // 6) 构造降阶后的折叠多项式并求其值 e'。
    let folded_poly = lower_poly.fold(&upper_poly, &alpha);
    let e_prime = folded_poly.evaluate(y);

    // 7) 对 e' 承诺，得到 C'_P。
    let c_p_prime_with_open = commit_cs(params_ah, &e_prime, cs_rand_bits)?;
    let pi_c_p_prime = prove_cs_com(
        params_ah,
        &c_p_prime_with_open.commitment,
        &c_p_prime_with_open.opening,
    )?;

    // 8) 证明 e = e1 ⊕ e2。
    let pi_e_eq_e1_plus_e2 = prove_cs_add(
        params_ah,
        &c1_with_open.commitment,
        &c2_with_open.commitment,
        c_p_commitment,
        &c1_with_open.opening,
        &c2_with_open.opening,
        r_p,
    )?;

    // 9) 证明 e2 = y^(n/2) ⊙ e3（相对 Cy_{n/2}）。
    let (cy_half, r_half) = lookup_cy_for_power(half, cy, r_y, aux_openings)?;
    let y_half_bi = bu_to_bi(&y_half)?;
    let r_half_bi = bu_to_bi(&r_half)?;
    let b_half = derive_mult_signs(&c2_with_open.opening, &c3_with_open.opening, &y_half_bi)?;
    let pi_e2_eq_y_half_mul_e3 = prove_cs_mult(
        params_ah,
        &c2_with_open.commitment,
        &c3_with_open.commitment,
        &cy_half,
        &c2_with_open.opening,
        &c3_with_open.opening,
        &y_half_bi,
        &r_half_bi,
        1,
        b_half,
    )?;

    // 10) 构造 alpha ⊙ e3，对其承诺并证明可打开。
    let alpha_e3 = CiphertextPolynomial::homomorphic_scalar_mul(&e3, &alpha, &params_ah.n2);
    let c_alpha_e3_with_open = commit_cs(params_ah, &alpha_e3, cs_rand_bits)?;
    let pi_c_alpha_e3 = prove_cs_com(
        params_ah,
        &c_alpha_e3_with_open.commitment,
        &c_alpha_e3_with_open.opening,
    )?;

    // 11) 对 alpha 做 DF 承诺，随后证明 alpha ⊙ e3 关系。
    let df_rand_bits = default_df_randomness_bits(params_ah)?;
    let cy_alpha_with_open = commit_df(params_df_for_alpha, &alpha, df_rand_bits)?;
    let pi_cy_alpha = prove_df_open_public_scalar(
        params_df_for_alpha,
        &cy_alpha_with_open.c,
        &alpha,
        &cy_alpha_with_open.r,
        params_ah.lambda_bits,
    )?;
    let alpha_bi = bu_to_bi(&alpha)?;
    let r_alpha_bi = bu_to_bi(&cy_alpha_with_open.r)?;
    let b_alpha = derive_mult_signs(&c_alpha_e3_with_open.opening, &c3_with_open.opening, &alpha_bi)?;
    let pi_alpha_mul_e3 = prove_cs_mult(
        params_ah,
        &c_alpha_e3_with_open.commitment,
        &c3_with_open.commitment,
        &cy_alpha_with_open.c,
        &c_alpha_e3_with_open.opening,
        &c3_with_open.opening,
        &alpha_bi,
        &r_alpha_bi,
        1,
        b_alpha,
    )?;

    // 12) 证明 e' = e1 ⊕ (alpha ⊙ e3)。
    let pi_eprime_eq_e1_plus_alphae3 = prove_cs_add(
        params_ah,
        &c1_with_open.commitment,
        &c_alpha_e3_with_open.commitment,
        &c_p_prime_with_open.commitment,
        &c1_with_open.opening,
        &c_alpha_e3_with_open.opening,
        &c_p_prime_with_open.opening,
    )?;

    let round_proof = PoKStarRoundProof {
        c1: c1_with_open.commitment,
        c2: c2_with_open.commitment,
        c3: c3_with_open.commitment,
        c_alpha_e3: c_alpha_e3_with_open.commitment,
        c_p_prime: c_p_prime_with_open.commitment.clone(),
        alpha,
        cy_half,
        cy_alpha: cy_alpha_with_open.c,
        pi_cy_alpha,
        pi_c1,
        pi_c2,
        pi_c3,
        pi_c_alpha_e3,
        pi_c_p_prime,
        pi_e_eq_e1_plus_e2,
        pi_e2_eq_y_half_mul_e3,
        pi_alpha_mul_e3,
        pi_eprime_eq_e1_plus_alphae3,
    };

    // 13) 更新递归 transcript：对应论文中的 tau' = (pi, tau)。
    let tau_next = append_round_to_tau(tau, &round_proof);

    // 14) 进入下一层递归。
    let next = pok_star_recursive(
        params_ah,
        params_df_for_alpha,
        r_y,
        y,
        &e_prime,
        &c_p_prime_with_open.opening,
        cy,
        &folded_poly,
        &c_p_prime_with_open.commitment,
        aux_openings,
        &tau_next,
    )?;

    Ok(PoKStarProof::Recursive {
        round: round_proof,
        next: Box::new(next),
    })
}

/// 递归核心证明 PoK*_P。
///
/// 该函数是 Algorithm 2 的入口包装：
/// 1. 构造密文多项式对象；
/// 2. 调用递归核心；
/// 3. 返回完整递归证明树。
fn pok_star_p(
    params_ah: &CsCommitParams,
    r_y: &BigUint,
    y: &BigUint,
    c_p: &CsCiphertext,
    r_p: &CsCommitOpening,
    cy: &BigUint,
    c_values: &[CsCiphertext],
    c_p_commitment: &CsCommitment,
    aux_openings: &[PoKAuxOpeningEntry],
    tau: &PoKTranscript,
) -> CryptoResult<PoKStarProof> {
    if c_values.is_empty() {
        return Err(CryptoError::InvalidInput("c_values must be non-empty"));
    }
    if !c_values.len().is_power_of_two() {
        return Err(CryptoError::InvalidInput(
            "PoK*_P requires polynomial length to be a power of two",
        ));
    }

    let poly = CiphertextPolynomial::new(c_values.to_vec(), &params_ah.n2)?;
    let params_df_for_alpha = df_params_from_ah(params_ah);

    pok_star_recursive(
        params_ah,
        &params_df_for_alpha,
        r_y,
        y,
        c_p,
        r_p,
        cy,
        &poly,
        c_p_commitment,
        aux_openings,
        tau,
    )
}

/// Algorithm 1: PoKP(r, y, Cy, c0,...,c_{n-1},cP) -> pi
///
/// 入参说明：
/// 1. params_ah: AH/CS 承诺参数（用于 CP <- Com_AH(cP;0)）
/// 2. params_df: DF 承诺参数（用于 Cy2i 承诺）
/// 3. r_y: Cy 对应开口随机数
/// 4. y: 向量/标量基值（后续构造 y^(2^i)）
/// 5. cy: 对 y 的 DF 承诺值
/// 6. c_values: 输入序列 c0..c_{n-1}
/// 7. c_p: 目标值 cP
/// 8. df_randomness_bits: DF 承诺随机数位长
///
/// 返回：
/// - aux: 每一轮 y^(2^i) 的承诺及关联证明
/// - recursive_proof: PoK*_P 的递归证明树
pub fn pokp(
    params_ah: &CsCommitParams,
    params_df: &DfParams,
    r_y: &BigUint,
    y: &BigUint,
    cy: &BigUint,
    c_values: &[CsCiphertext],
    c_p: &CsCiphertext,
    df_randomness_bits: usize,
) -> CryptoResult<PoKPProof> {
    if c_values.is_empty() {
        return Err(CryptoError::InvalidInput("c_values must be non-empty"));
    }
    if !c_values.len().is_power_of_two() {
        return Err(CryptoError::InvalidInput(
            "current PoKP implementation requires n to be a power of two",
        ));
    }
    if df_randomness_bits == 0 {
        return Err(CryptoError::InvalidInput("df_randomness_bits must be > 0"));
    }

    // Step 1: CP <- Com_AH(cP; 0)
    let c_p_wrapped = com_ah_with_zero_randomness(params_ah, c_p)?;

    // Step 2: 构造 y^(2^i) 承诺序列，并生成每轮关系证明 pi_y2i。
    let rounds = c_values.len().ilog2() as usize;
    let mut aux = Vec::with_capacity(rounds);
    let mut aux_openings = Vec::with_capacity(rounds);

    let mut prev_z = y.clone();
    let mut prev_cy = cy.clone();
    let mut prev_r = r_y.clone();

    for i in 1..=rounds {
        let z2 = &prev_z * &prev_z;
        let cy2i = commit_df(params_df, &z2, df_randomness_bits)?;

        // 按算法调用 NIZK 链接证明：
        // pi_y2i <- NIZK[(z,r_{i-1},r_i): Cy2i-1=Com(z;r_{i-1}) ∧ Cy2i=Com(z^2;r_i)]
        let pi_y2i = prove_mult_with_lambda(
            params_df,
            &prev_cy,
            &prev_r,
            &cy2i.c,
            &cy2i.r,
            &prev_z,
            params_ah.lambda_bits,
        )?;

        aux.push(PoKAuxEntry {
            round: i,
            cy_2i: cy2i.c.clone(),
            pi_y2i,
        });
        aux_openings.push(PoKAuxOpeningEntry {
            round: i,
            cy_2i: cy2i.c.clone(),
            r_i: cy2i.r.clone(),
        });

        prev_z = z2;
        prev_cy = cy2i.c;
        prev_r = cy2i.r;
    }

    // Step 3: 初始化 tau。
    let tau = PoKTranscript {
        cy: cy.clone(),
        c_values: c_values.to_vec(),
        c_p: c_p.clone(),
        history: Vec::new(),
    };

    // Step 4: 返回 aux, PoK*_P(...)
    let recursive_proof = pok_star_p(
        params_ah,
        r_y,
        y,
        c_p,
        &c_p_wrapped.opening,
        cy,
        c_values,
        &c_p_wrapped.commitment,
        &aux_openings,
        &tau,
    )?;

    Ok(PoKPProof {
        aux,
        tau,
        c_p_commitment: c_p_wrapped.commitment,
        recursive_proof,
    })
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;
    use crate::cs::{enc_cs, keygen_cs, setup_cs};
    use crate::df::commit_df_with_opening;
    use crate::df::DfParams;
    use crate::math::sample_unit_mod_n2;
    use crate::setup_cs_commit;

    #[test]
    fn test_com_ah_with_zero_randomness_shape() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");
        let ct = enc_cs(&cs_params, &pk, &BigUint::from(3u32)).expect("enc should succeed");

        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
        };
        let params_ah = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let wrapped = com_ah_with_zero_randomness(&params_ah, &ct).expect("zero random commit should succeed");
        assert_eq!(wrapped.commitment.c1, ct.c0 % &params_ah.n2);
        assert_eq!(wrapped.commitment.c2, BigUint::one());
        assert_eq!(wrapped.commitment.c3, ct.c1 % &params_ah.n2);
        assert_eq!(wrapped.commitment.c4, BigUint::one());
        assert_eq!(wrapped.opening.s1, BigUint::zero());
        assert_eq!(wrapped.opening.r1, BigUint::zero());
    }

    #[test]
    fn test_prove_mult_and_verify_square_df() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
        };

        let z = BigUint::from(9u32);
        let r_in = BigUint::from(77u32);
        let r_out = BigUint::from(123u32);
        let c_in = commit_df_with_opening(&df_params, &z, &r_in).expect("commit in should succeed");
        let z_sq = &z * &z;
        let c_out = commit_df_with_opening(&df_params, &z_sq, &r_out).expect("commit out should succeed");

        let proof = prove_mult(&df_params, &c_in.c, &c_in.r, &c_out.c, &c_out.r, &z)
            .expect("prove mult should succeed");
        let ok = verify_mult(&df_params, &c_in.c, &c_out.c, &proof).expect("verify should run");
        assert!(ok);
    }

    #[test]
    fn test_verify_mult_rejects_tampered_proof() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
        };

        let z = BigUint::from(6u32);
        let r_in = BigUint::from(11u32);
        let r_out = BigUint::from(19u32);
        let c_in = commit_df_with_opening(&df_params, &z, &r_in).expect("commit in should succeed");
        let z_sq = &z * &z;
        let c_out = commit_df_with_opening(&df_params, &z_sq, &r_out).expect("commit out should succeed");

        let mut proof = prove_mult(&df_params, &c_in.c, &c_in.r, &c_out.c, &c_out.r, &z)
            .expect("prove mult should succeed");
        proof.z_gamma += BigInt::from(1u32);

        let ok = verify_mult(&df_params, &c_in.c, &c_out.c, &proof).expect("verify should run");
        assert!(!ok);
    }

    #[test]
    fn test_ciphertext_polynomial_evaluate_matches_manual_homomorphic_sum() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");

        let x0 = enc_cs(&cs_params, &pk, &BigUint::from(1u32)).expect("enc x0 should succeed");
        let x1 = enc_cs(&cs_params, &pk, &BigUint::from(2u32)).expect("enc x1 should succeed");
        let x2 = enc_cs(&cs_params, &pk, &BigUint::from(3u32)).expect("enc x2 should succeed");

        let poly = CiphertextPolynomial::new(vec![x0.clone(), x1.clone(), x2.clone()], &cs_params.n2)
            .expect("poly construction should succeed");
        let y = BigUint::from(3u32);
        let eval = poly.evaluate(&y);

        let y2 = &y * &y;
        let x1_y = CsCiphertext {
            c0: x1.c0.modpow(&y, &cs_params.n2),
            c1: x1.c1.modpow(&y, &cs_params.n2),
        };
        let x2_y2 = CsCiphertext {
            c0: x2.c0.modpow(&y2, &cs_params.n2),
            c1: x2.c1.modpow(&y2, &cs_params.n2),
        };
        let manual = CsCiphertext {
            c0: (((&x0.c0 * &x1_y.c0) % &cs_params.n2) * &x2_y2.c0) % &cs_params.n2,
            c1: (((&x0.c1 * &x1_y.c1) % &cs_params.n2) * &x2_y2.c1) % &cs_params.n2,
        };

        assert_eq!(eval.c0, manual.c0);
        assert_eq!(eval.c1, manual.c1);
    }

    #[test]
    fn test_ciphertext_polynomial_split_and_fold() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");

        let c0 = enc_cs(&cs_params, &pk, &BigUint::from(1u32)).expect("enc c0 should succeed");
        let c1 = enc_cs(&cs_params, &pk, &BigUint::from(2u32)).expect("enc c1 should succeed");
        let c2 = enc_cs(&cs_params, &pk, &BigUint::from(3u32)).expect("enc c2 should succeed");
        let c3 = enc_cs(&cs_params, &pk, &BigUint::from(4u32)).expect("enc c3 should succeed");

        let poly = CiphertextPolynomial::new(vec![c0.clone(), c1.clone(), c2.clone(), c3.clone()], &cs_params.n2)
            .expect("poly construction should succeed");
        let (low, up) = poly.split_in_half();
        assert_eq!(low.len(), 2);
        assert_eq!(up.len(), 2);

        let alpha = BigUint::from(2u32);
        let folded = low.fold(&up, &alpha);

        let expected0 = CsCiphertext {
            c0: (&c0.c0 * c2.c0.modpow(&alpha, &cs_params.n2)) % &cs_params.n2,
            c1: (&c0.c1 * c2.c1.modpow(&alpha, &cs_params.n2)) % &cs_params.n2,
        };
        let expected1 = CsCiphertext {
            c0: (&c1.c0 * c3.c0.modpow(&alpha, &cs_params.n2)) % &cs_params.n2,
            c1: (&c1.c1 * c3.c1.modpow(&alpha, &cs_params.n2)) % &cs_params.n2,
        };

        assert_eq!(folded.coeffs()[0].c0, expected0.c0);
        assert_eq!(folded.coeffs()[0].c1, expected0.c1);
        assert_eq!(folded.coeffs()[1].c0, expected1.c0);
        assert_eq!(folded.coeffs()[1].c1, expected1.c1);
    }

    #[test]
    fn test_pokp_runs_with_recursive_pok_star_p() {
        let cs_params = setup_cs(64).expect("setup cs should succeed");
        let (pk, _sk) = keygen_cs(&cs_params).expect("keygen should succeed");

        let c0 = enc_cs(&cs_params, &pk, &BigUint::from(1u32)).expect("enc c0 should succeed");
        let c1 = enc_cs(&cs_params, &pk, &BigUint::from(2u32)).expect("enc c1 should succeed");

        // 令 cP = x0 ⊕ (x1 ⊙ y)，满足 e = sum_i x_i ⊙ y^i。
        let y = BigUint::from(5u32);
        let c1_y = CsCiphertext {
            c0: c1.c0.modpow(&y, &cs_params.n2),
            c1: c1.c1.modpow(&y, &cs_params.n2),
        };
        let c_p = CsCiphertext {
            c0: (&c0.c0 * &c1_y.c0) % &cs_params.n2,
            c1: (&c0.c1 * &c1_y.c1) % &cs_params.n2,
        };

        let df_params = DfParams {
            n: cs_params.n.clone(),
            n2: cs_params.n2.clone(),
            g: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
            h: sample_unit_mod_n2(&mut rand::rngs::OsRng, &cs_params.n2),
        };
        let params_ah = setup_cs_commit(40, &cs_params, &df_params).expect("setup cs commit should succeed");

        let r_y = BigUint::from(7u32);
        let cy = (df_params.g.modpow(&y, &df_params.n2) * df_params.h.modpow(&r_y, &df_params.n2)) % &df_params.n2;

        let proof = pokp(
            &params_ah,
            &df_params,
            &r_y,
            &y,
            &cy,
            &[c0, c1],
            &c_p,
            64,
        )
        .expect("PoKP should run to completion");

        match proof.recursive_proof {
            PoKStarProof::Recursive { .. } => {}
            _ => panic!("expected recursive PoK*_P proof for degree-1 polynomial"),
        }
    }
}
