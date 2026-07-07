//! Algorithm 2: Setup
//!
//! 负责初始化整个协议所需的全局参数 Λ。
//!
//! 输入：安全参数 λ（以 `lambda_bits` 表示）、属性向量长度 ℓ=2、
//!       阈值 t、Pedersen 承诺参数 cpar*（椭圆曲线版）。
//!
//! 输出：全局参数 Λ = (pp, cpar*, cpar, inv, Λ_BLUE, t, crs2)。
//!
//! S1 的 CRS 由 (cpar, cpar*) 承载；S2 的 CRS 按 Algorithm 13/14 生成。

use ark_bls12_381::{G1Projective, G2Projective};
use ark_ff::UniformRand;
use ark_std::Zero;

use rust::PpbParams;

use mercurial_signature::PublicParams as MsPublicParams;

/// Common reference string for Algorithm 13/14 (S2).
#[derive(Clone)]
pub struct Crs2 {
    pub h2: G1Projective,
    pub h3: G1Projective,
    pub h2_hat: G2Projective,
    pub h3_hat: G2Projective,
    pub p: G1Projective,
    pub p_hat: G2Projective,
}

fn random_nonzero_g1(rng: &mut ark_std::rand::rngs::OsRng) -> G1Projective {
    loop {
        let point = G1Projective::rand(rng);
        if !point.is_zero() {
            return point;
        }
    }
}

fn random_nonzero_g2(rng: &mut ark_std::rand::rngs::OsRng) -> G2Projective {
    loop {
        let point = G2Projective::rand(rng);
        if !point.is_zero() {
            return point;
        }
    }
}

/// 全局参数 Λ，对应 Algorithm 2 的输出。
///
/// 字段语义：
/// 1. `pp`：Mercurial Signature 的公共参数（BLS12-381 生成元 p1, p2）；
/// 2. `cpar_star`：Pedersen 承诺参数（椭圆曲线版，BLS12-381 G1 群）；
/// 3. `cpar`：DF 承诺参数（整数域，由 ppb setup 内部生成）；
/// 4. `inv`：随机采样的 G1 群元素，用于后续协议中的匿名化操作；
/// 5. `lambda_blue`：ppb 协议的全局参数（包含 HEC 参数等）；
/// 6. `t`：阈值参数；
/// 7. `crs2`：ZKProveS2/ZKVerifyS2 的公共参考串。
#[derive(Clone)]
pub struct Lambda {
    /// SPS 公共参数（Mercurial Signature 的公共参数）。
    pub pp: MsPublicParams,
    /// Pedersen 承诺参数（椭圆曲线版，cpar*）。
    pub cpar_star: rust::PedersenCommitmentParams,
    /// DF 承诺参数（整数域，cpar），由 ppb setup 内部生成。
    pub cpar: rust::DfParams,
    /// 随机 G1 群元素 inv ∈ RandomM(pp)。
    pub inv: ark_bls12_381::G1Projective,
    /// ppb 协议的全局参数 Λ_BLUE。
    pub lambda_blue: PpbParams,
    /// 阈值参数 t。
    pub t: usize,
    /// ZKVerifyS2 / ZKProveS2 使用的 CRS。
    pub crs2: Crs2,
}

/// Algorithm 2: Setup(1^λ, 1^ℓ=2, 1^t, cpar, cpar*, S1, S2) -> Λ
///
/// 输入：
/// 1. `lambda_bits`：安全参数 λ 的位长；
/// 2. `t`：阈值参数；
/// 3. `cpar_star`：Pedersen 承诺参数（椭圆曲线版，cpar*）。
///
/// 输出：全局参数 Λ。
///
/// 过程（对应算法步骤编号）：
/// Step 1: pp ← SPS.Setup(1^λ, 1^ℓ)
///   - 调用 mercurial-signature 的 PublicParams::new 生成 BLS12-381 上的
///     公共参数 pp = (p1, p2)，其中 p1 ∈ G1, p2 ∈ G2 为随机生成元。
///
/// Step 2: inv ∈$ RandomM(pp)
///   - 在 BLS12-381 的 G1 群上随机采样一个元素作为 inv。
///   - RandomM(pp) 表示由 pp 确定的消息空间（此处为 G1 群）。
///
/// Step 3: Λ_BLUE ← Setup(1^λ, cpar)
///   - 调用 ppb 的 setup_ppb 生成隐私保护协议的全局参数。
///   - setup_ppb 内部会生成 HEC 参数和 DF 承诺参数 cpar。
///   - 同时从返回值中提取 cpar 供全局参数使用。
///
/// Step 4-5: crs1 由 cpar/cpar* 隐式给出；采样 S2 所需的 crs2。
///
/// Step 6: return Λ = (pp, cpar*, cpar, inv, Λ_BLUE, t, crs2)。
pub fn setup(lambda_bits: usize, t: usize, cpar_star: rust::PedersenCommitmentParams) -> Lambda {
    let mut rng = ark_std::rand::rngs::OsRng;

    // ============================================================
    // Step 1: pp ← SPS.Setup(1^λ, 1^ℓ)
    // ============================================================
    // 调用 mercurial-signature 的 PublicParams::new，
    // 生成 BLS12-381 曲线上的两个随机生成元 p1 ∈ G1, p2 ∈ G2。
    let pp = MsPublicParams::new(&mut rng);

    // ============================================================
    // Step 2: inv ∈$ RandomM(pp)
    // ============================================================
    // RandomM(pp) 为 Mercurial Signature 的消息空间，此处为 G1 群。
    // 随机采样一个 G1 群元素作为 inv。
    let inv = ark_bls12_381::G1Projective::rand(&mut rng);

    // ============================================================
    // Step 3: Λ_BLUE ← Setup(1^λ, cpar)
    // ============================================================
    // 调用 ppb 的 setup_ppb，内部会：
    //   1. 调用 setup_hec 生成 HEC 同态加密参数；
    //   2. 从 HEC 参数中派生 DF 承诺参数 cpar = (n, n^2, g, h)。
    // BLUE 内部的 S1/S2/S3 参数仍由底层占位；最终协议的 S2 CRS 在下方生成。
    let lambda_blue =
        rust::setup_ppb(lambda_bits, &(), &(), &()).expect("setup_ppb failed during Setup");

    // 从 Λ_BLUE 中提取 cpar（DF 承诺参数），作为全局参数的一部分。
    let cpar = lambda_blue.cpar.clone();

    // ============================================================
    // Step 4-5: crs1 由 cpar/cpar* 隐式给出；生成 Algorithm 13/14 的 crs2。
    // ============================================================
    let crs2 = Crs2 {
        h2: random_nonzero_g1(&mut rng),
        h3: random_nonzero_g1(&mut rng),
        h2_hat: random_nonzero_g2(&mut rng),
        h3_hat: random_nonzero_g2(&mut rng),
        p: random_nonzero_g1(&mut rng),
        p_hat: random_nonzero_g2(&mut rng),
    };

    // ============================================================
    // Step 6: return Λ = (pp, cpar*, cpar, inv, Λ_BLUE, t, crs2)
    // ============================================================
    Lambda {
        pp,
        cpar_star,
        cpar,
        inv,
        lambda_blue,
        t,
        crs2,
    }
}
