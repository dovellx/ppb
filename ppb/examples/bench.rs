#![allow(non_snake_case)]
//! **端到端基准**：把 Griffy et al. 方案（本 crate）的算法各跑一遍，报告耗时与证明体积，
//! 直接对应论文的 `tab:computation-time` 与 `tab:proof-size` 的 **Griffy et al.** 两行。
//!
//! 跑法（一定要 `--release`，debug 慢 ~50×）：
//! ```text
//!   cargo run --release --example bench -- <profile> [reps]
//!   profile ∈ { tiny | small | medium | large | rowA | rowB }
//! ```
//! 不给参数就跑 `tiny`。`rowA`/`rowB` 是论文 `sec:evaluation` 的两组参数；
//! `tiny`…`large` 是同结构的缩小版，用来测出耗时随 ℓ_N / n 的增长曲线。
//!
//! 结果同时打印到 stdout 并追加写入 `bench_results/`。每跑完一次重复就立即落盘，
//! 因为 `rowA` 单次重复约 22 小时，中途必须能看到进度。

use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use num_bigint::{BigInt, BigUint, RandBigInt};
use rand::rngs::StdRng;
use rand::SeedableRng;

use rust::cs_commit::CsComCtProof;
use rust::pok::PoKStarRoundProof;
use rust::{
    dec_ppb, escrow_ppb, judge_ppb, keygen_ppb, setup_ppb, verify_pk, verify_poks3, CsAddProof,
    CsComProof, CsCommitment, CsEncProof, CsMultProof, CsCiphertext, CsPubKey, DfOpenProof,
    HecEvalInput, HecFunctionKey, PoKAuxEntry, PoKPProof, PoKStarProof, PoKTranscript, PpbAuthProof,
    PpbDecProof, PpbEncMulAddProof, PpbParams, PpbS1FinalProof, PpbS1FoldRound, PpbUserProof,
    PpbYConsistencyProof, ProveMultProof,
};

// ============================================================================
// 参数组
// ============================================================================

/// 一组完整的可运行参数。
///
/// Griffy 方案的自由度比"Ours"少得多：整个方案只挂在一个 RSA 模数位长 `ℓ_N`
/// 和一个名单规模 `n` 上（见 `EXPERIMENT_PLAN.md` §1）。下面三个字段是记录性的，
/// 当前代码里**没有对应旋钮**，原因写在字段注释里。
struct Profile {
    name: &'static str,
    /// 计算安全参数。仅记录用：代码里没有独立的 λ，见 `tau`。
    lambda: usize,
    /// 统计安全参数 τ。**当前代码没有这个旋钮**：`derive_poks1_blinding_bits`
    /// 用的是 `B + 2·lambda_bits`，而 `lambda_bits` 就是 ℓ_N。
    /// 因此 rowA/rowB 的差别**只体现在 ℓ_N 上**，τ 这一列是名义值。
    /// 若接受给 `PpbParams` 加 `stat_bits`，Σ 协议部分还能再省约一半。
    tau: usize,
    /// `ℓ_N`：RSA 模数 N = pq 的位长。群元素在 `Z_{N²}`，明文空间 `Z_N`。
    ell_n: usize,
    /// 名单规模 n。**必须满足 n+1 是 2 的幂**（`pokp` 的硬约束）。
    n: usize,
    /// 论文参数集给出的名义名单规模 `B·(Δ+1)`，仅用于 `describe` 里对照。
    nominal_watchlist: usize,
    /// 重复次数。表格取均值，同时报告标准差。
    reps: usize,
}

impl Profile {
    fn get(name: &str) -> Option<Profile> {
        // 论文 sec:evaluation：B ≤ 128（正文）/ ≤ 100（附录），Δ ≤ 127。
        // 取附录的 B = 100 ⇒ 名义名单 = B·(Δ+1) = 100 × 128 = 12800。
        // Griffy 的 PoKP 要求系数个数 n+1 是 2 的幂，12801 不是；
        // 按论文脚注 14 应补齐到 16384，这里等价地直接把 n 取到 16383。
        // 两种做法的算力完全相同（都是 16384 个系数），差别只是 3583 个哑元。
        const NOMINAL: usize = 12800;
        Some(match name {
            "rowA" => Profile {
                name: "rowA(tau=80, paper)",
                lambda: 128,
                tau: 80,
                ell_n: 4096,
                n: 16383,
                nominal_watchlist: NOMINAL,
                reps: 1,
            },
            "rowB" => Profile {
                name: "rowB(tau=128, paper)",
                lambda: 128,
                tau: 128,
                ell_n: 4608,
                n: 16383,
                nominal_watchlist: NOMINAL,
                reps: 1,
            },
            "tiny" => Profile {
                name: "tiny(l_N=256)",
                lambda: 128,
                tau: 80,
                ell_n: 256,
                n: 15,
                nominal_watchlist: 15,
                reps: 5,
            },
            "small" => Profile {
                name: "small(l_N=512)",
                lambda: 128,
                tau: 80,
                ell_n: 512,
                n: 127,
                nominal_watchlist: 127,
                reps: 5,
            },
            "medium" => Profile {
                name: "medium(l_N=1024)",
                lambda: 128,
                tau: 80,
                ell_n: 1024,
                n: 1023,
                nominal_watchlist: 1023,
                reps: 3,
            },
            "large" => Profile {
                name: "large(l_N=2048)",
                lambda: 128,
                tau: 80,
                ell_n: 2048,
                n: 4095,
                nominal_watchlist: 4095,
                reps: 2,
            },
            _ => return None,
        })
    }

    /// 逐条核对**在跑之前**就能挡下来的约束。
    ///
    /// 与"Ours"那边不同，Griffy 这边没有 Σ 协议提升到整数关系的位长约束
    /// （它的承诺本来就是整数承诺），所以这里检查的是实现层面的硬约束。
    fn preflight(&self) -> bool {
        let coeffs = self.n + 1;
        let group_bytes = 2 * self.ell_n / 8;
        // pk 里 n+1 个 CS 密文，每个 2 个 Z_{N²} 元素；π_U 的 tau.c_values 是它的副本。
        let pk_mb = (coeffs * 2 * group_bytes) as f64 / (1024.0 * 1024.0);

        let checks: [(&str, bool, String); 5] = [
            (
                "n+1 是 2 的幂 (pokp 硬约束)",
                coeffs.is_power_of_two(),
                format!("n+1 = {coeffs}"),
            ),
            (
                "ℓ_N 为偶且 ≥ 32 (generate_safe_rsa_modulus)",
                self.ell_n % 2 == 0 && self.ell_n >= 32,
                format!("ℓ_N = {}", self.ell_n),
            ),
            (
                "名单元素 + y_at < N (map_y_to_df_message 的整数和约束)",
                true,
                "基准把 y_id/y_at 都取自 [0, N/2)".into(),
            ),
            (
                "内存：pk 与 π_U 各约一份系数密文",
                pk_mb < 512.0,
                format!("每份约 {pk_mb:.1} MiB，进程峰值约 {:.1} MiB", pk_mb * 6.0),
            ),
            (
                "τ 在代码中无对应旋钮",
                true,
                "rowA/rowB 仅 ℓ_N 不同；见 Profile::tau 注释".into(),
            ),
        ];

        let mut ok = true;
        println!("参数前置检查:");
        for (name, good, detail) in checks {
            if !good {
                ok = false;
            }
            println!(
                "  [{}] {name:<46} {detail}",
                if good { "OK" } else { "!!" }
            );
        }
        if !ok {
            println!();
            println!("参数组不合法，跑不起来。n 只能取 2^k − 1（15/127/1023/16383…）。");
        }
        println!();
        ok
    }

    fn describe(&self) {
        println!("参数组 {}", self.name);
        println!(
            "  λ={} τ={}(名义) ℓ_N={} ⇒ 群元素 {} bit，明文空间 Z_N ({} bit)",
            self.lambda,
            self.tau,
            self.ell_n,
            2 * self.ell_n,
            self.ell_n
        );
        println!(
            "  n={} ⇒ 多项式系数 {} 个 = 2^{}，PoKP 递归 {} 层",
            self.n,
            self.n + 1,
            (self.n + 1).ilog2(),
            (self.n + 1).ilog2()
        );
        if self.nominal_watchlist != self.n {
            println!(
                "  论文参数集名义名单 B·(Δ+1) = {}；补齐到 2 的幂后取 n = {}（脚注 14）",
                self.nominal_watchlist, self.n
            );
        }
        println!("  重复次数 = {}（表格取均值，同时报标准差）", self.reps);
    }
}

// ============================================================================
// 证明体积
// ============================================================================
//
// 仓库里没有任何序列化（全仓库无 serde），所以体积按「每个群元素 / 每个响应的字节数
// 之和」计。这里与"Ours"侧的基准保持同一口径：**最小幅值字节数**，即紧致下界。
// 同时额外报告一个「规范定长编码」口径（每个 Z_{N²} 元素记 2ℓ_N/8 字节），
// 因为真实传输会用定长；两个口径的差别在报告里必须写明。

trait Size {
    fn size(&self) -> usize;
}

impl Size for BigUint {
    fn size(&self) -> usize {
        self.to_bytes_be().len()
    }
}
impl Size for BigInt {
    fn size(&self) -> usize {
        // 符号占 1 字节。
        self.to_bytes_be().1.len() + 1
    }
}
impl Size for bool {
    fn size(&self) -> usize {
        1
    }
}
impl Size for usize {
    fn size(&self) -> usize {
        8
    }
}
impl<T: Size> Size for Vec<T> {
    fn size(&self) -> usize {
        self.iter().map(Size::size).sum()
    }
}
impl<T: Size> Size for Box<T> {
    fn size(&self) -> usize {
        (**self).size()
    }
}

/// `impl Size for T { 各字段求和 }`
macro_rules! size_of_fields {
    ($ty:ty { $($f:ident),* $(,)? }) => {
        impl Size for $ty {
            fn size(&self) -> usize { 0 $(+ self.$f.size())* }
        }
    };
}

size_of_fields!(CsPubKey { k });
size_of_fields!(CsCiphertext { c0, c1 });
size_of_fields!(CsCommitment { c1, c2, c3, c4 });
size_of_fields!(CsComProof { r2, r4, z_s1, z_r1, z_s2, z_r2 });
size_of_fields!(CsComCtProof { r1, r2, r3, r4, z_s1, z_r1, z_s2, z_r2 });
size_of_fields!(CsAddProof { e, z1, z2, z3, z4 });
size_of_fields!(CsMultProof { r_y, r1, r2, r3, r4, z_y, z_ry, z1, z2, z3, z4 });
size_of_fields!(CsEncProof { r_y, r1, r2, r3, r4, z_y, z_ry, z_ra, z_s1, z_r1, z_s2, z_r2 });
size_of_fields!(ProveMultProof { r1, r2, z_z, z_rin, z_gamma });
size_of_fields!(DfOpenProof { r_commitment, z_r });
size_of_fields!(PoKAuxEntry { round, cy_2i, c_w, c_k, pi_y2i });
size_of_fields!(PoKTranscript { cy, c_values, c_p, history });
size_of_fields!(PoKStarRoundProof {
    c1, c2, c3, c_alpha_e3, c_p_prime, alpha, cy_half, cy_alpha, pi_cy_alpha, pi_c1, pi_c2, pi_c3,
    pi_c_alpha_e3, pi_c_p_prime, pi_e_eq_e1_plus_e2, pi_e2_eq_y_half_mul_e3, pi_alpha_mul_e3,
    pi_eprime_eq_e1_plus_alphae3,
});
size_of_fields!(PoKPProof { aux, tau, c_p_commitment, recursive_proof });
size_of_fields!(PpbS1FoldRound { l, r });
size_of_fields!(PpbS1FinalProof {
    r_cx, r_cd, r_pk, r_u, r_v, z_x, z_rx, z_md, z_rd, z_sk, z_rho
});
size_of_fields!(PpbAuthProof { rounds, final_proof });
size_of_fields!(PpbEncMulAddProof { c_enc, c_mul, pi_enc, pi_mult, pi_add });
size_of_fields!(PpbYConsistencyProof { c_y_from_cid_cat, relation_holds });
size_of_fields!(PpbUserProof {
    ah_g, c_id, c_at, c_r1, c_r2, c_r3, pk_sky, c_sky, pi_poly, pi_nf, pi_id, pi_at, pi_sky, pi_y
});
size_of_fields!(PpbDecProof {
    r_d_commitment, r_pk_commitment, r_z_id, r_z_at, r_z_nf, z_md, z_rd, z_sk
});

impl Size for PoKStarProof {
    fn size(&self) -> usize {
        match self {
            PoKStarProof::Base { pi_open_cp } => pi_open_cp.size(),
            PoKStarProof::Recursive { round, next } => round.size() + next.size(),
        }
    }
}

/// `π_U` 中**可从公开语句恢复**的冗余字段，真实实现不会重传。
///
/// - `pi_poly.tau.c_values`：审计方公钥里 `A_1..A_{n+1}` 的完整副本。论文 Alg. 1 第 3 行
///   写明 `τ` 是 Fiat–Shamir 的哈希输入（公开语句），不是证明的一部分。
///   在 n=16383 / ℓ_N=4096 下它单项就有约 32 MiB，会完全主导 `|π_U|`，
///   并让 Griffy 的 escrow 从论文自述的 `O(log n)` 变成 `O(n)`。
/// - `pk_sky`：由 setup 固定的公共参数。
/// - `pi_y.c_y_from_cid_cat`：恒等于公开输入 `C_y`。
fn redundant_bytes(pi_u: &PpbUserProof) -> usize {
    pi_u.pi_poly.tau.c_values.size() + pi_u.pk_sky.size() + pi_u.pi_y.c_y_from_cid_cat.size()
}

/// Griffy 侧 `ect_x` 的对应物：HECenc 的公开输出 `X = (pk_AH, A_1..A_{n+1})`。
///
/// 论文 Sec 5.2：`HECenc` 把名单 `x` 展开成 `P(χ) = s·Π(χ − x_i)`，逐系数加密后输出
/// `X = (pk_AH, {A_i = Enc(pk_AH, a_i)}_{i∈[0..n]})`，`X` 是 `pk_A` 的第一个分量
///（Fig. 5.4 KeyGen 第 8 行 `pk_A ← (X, Cx, Cd, πA)`）。
/// 也就是说 Griffy 的"加密名单"并没有单独成阶段，但**这个对象本身是存在的**，
/// 尺寸完全可比。
///
/// ⚠️ `HecPublicPackage.polynomial` 是 `encrypted_coeffs` 的**本地副本**
///（同一批密文外面包了一层 `CiphertextPolynomial`，只为免去重复构造），
/// 不是要传输的第二份数据——**绝不能重复计入**。
///
/// 解析尺寸：`1 + 2(n+1)` 个 `Z_{N²}` 元素，即 `(2n+3)·2ℓ_N/8` 字节。
/// rowA（n=16383, ℓ_N=4096）下约 32 MiB。
fn ect_x_bytes(x: &rust::HecPublicPackage) -> usize {
    x.pk_ah.size()
        + x.encrypted_coeffs
            .iter()
            .map(Size::size)
            .sum::<usize>()
}

fn kib(bytes: usize) -> String {
    format!("{:>12.2} KiB", bytes as f64 / 1024.0)
}

// ============================================================================
// 计时
// ============================================================================

fn timed<T>(label: &str, f: impl FnOnce() -> T) -> (T, Duration) {
    let t0 = Instant::now();
    let out = f();
    let dt = t0.elapsed();
    println!("  {label:<12} {:>12.3} s", dt.as_secs_f64());
    (out, dt)
}

#[derive(Default)]
struct Samples {
    keygen: Vec<f64>,
    verpk: Vec<f64>,
    escrow: Vec<f64>,
    verescrow: Vec<f64>,
    dec: Vec<f64>,
    judge: Vec<f64>,
}

fn mean(v: &[f64]) -> f64 {
    if v.is_empty() {
        return f64::NAN;
    }
    v.iter().sum::<f64>() / v.len() as f64
}

fn stddev(v: &[f64]) -> f64 {
    if v.len() < 2 {
        return 0.0;
    }
    let m = mean(v);
    (v.iter().map(|x| (x - m).powi(2)).sum::<f64>() / (v.len() - 1) as f64).sqrt()
}

fn stat_cell(v: &[f64]) -> String {
    if v.len() < 2 {
        format!("{:.3}", mean(v))
    } else {
        format!("{:.3} ± {:.3}", mean(v), stddev(v))
    }
}

// ============================================================================

fn main() {
    let mut args = std::env::args().skip(1);
    let name = args.next().unwrap_or_else(|| "tiny".into());
    let Some(mut p) = Profile::get(&name) else {
        eprintln!("未知参数组 `{name}`；可选：tiny | small | medium | large | rowA | rowB");
        std::process::exit(2);
    };
    if let Some(r) = args.next().and_then(|s| s.parse::<usize>().ok()) {
        p.reps = r.max(1);
    }

    p.describe();
    println!();
    if !p.preflight() {
        std::process::exit(1);
    }

    let out_dir = PathBuf::from("bench_results");
    fs::create_dir_all(&out_dir).expect("创建 bench_results/");
    let csv_path = out_dir.join("griffy_raw.csv");
    let md_path = out_dir.join("griffy_tables.md");
    let mut csv = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&csv_path)
        .expect("打开 csv");
    if csv.metadata().map(|m| m.len()).unwrap_or(0) == 0 {
        writeln!(
            csv,
            "profile,ell_n,n,rep,keygen_s,verpk_s,escrow_s,verescrow_s,dec_s,judge_s,\
             pi_A_bytes,pi_U_bytes,pi_U_net_bytes,pi_Z_bytes,ect_x_bytes,pk_bytes,zhat_bytes"
        )
        .ok();
    }

    let mut rng = StdRng::seed_from_u64(0xB1A5E);
    let mut s = Samples::default();
    let mut last_sizes: Option<(usize, usize, usize, usize, usize, usize, usize, usize)> = None;

    // ── Setup（论文明确说「Setup time is excluded」，故只报不计入表）──────────
    //
    // 注意 Setup 里是安全 RSA 模数搜索，耗时服从几何分布、方差极大
    // （ℓ_N=4096 实测单次约 181 s，但方差可达数倍）。参数与 n 无关，
    // 因此所有重复共用同一份 Λ——这既是论文的语义，也避免把方差混进表格。
    println!("Setup（论文的表里排除，仅供参考）:");
    let (lam, _): (PpbParams, _) = timed("Setup", || {
        setup_ppb(p.ell_n, &(), &(), &()).expect("setup 必须成功")
    });
    println!();

    // 名单元素与 y 都取自 [0, N/2)：现有实现要求 y_id + y_at < N
    //（`map_y_to_df_message` 取模而验证侧 `C_id·C_at` 用整数和），
    // 而位长仍是 ℓ_N−1，对指数代价而言与满位长等价。
    // ⚠️ 绝不能用 3、5、7 这类小整数：那会让 modexp 的指数只有几 bit，
    //    把真实代价整体压低一个数量级（见 AUDIT_POKP.md §4.7）。
    let half_n = &lam.cpar.n >> 1u32;

    println!("tab:computation-time（秒）:");
    for rep in 1..=p.reps {
        println!("[rep {rep}/{}]", p.reps);

        let x: Vec<BigUint> = (0..p.n).map(|_| rng.gen_biguint_below(&half_n)).collect();
        let fk = HecFunctionKey { n: x.len(), k: 1 };
        let r_x = rng.gen_biguint_below(&lam.cpar.n);
        let mask = rng.gen_biguint_below(&lam.cpar.n) + BigUint::from(1u32);

        let ((pkA, skA), t_keygen) =
            timed("KeyGen", || keygen_ppb(&lam, &fk, &x, &r_x, &mask).expect("keygen"));
        let (ok, t_verpk) = timed("VerPK", || verify_pk(&lam, &pkA, &pkA.c_x));
        assert!(ok, "诚实 pk_A 必须通过 VerPK");

        // 命中名单内成员，走完整最长路径（Dec 必须解出具体身份）。
        let y = HecEvalInput {
            y_id: x[p.n / 2].clone(),
            y_at: rng.gen_biguint_below(&half_n),
        };
        let r_y = rng.gen_biguint_below(&lam.cpar.n);

        let (zesc, t_escrow) = timed("Escrow", || {
            escrow_ppb(&lam, &pkA, &y, &r_y)
                .expect("escrow 必须可运行")
                .expect("诚实托管必须通过内部 VerPK")
        });
        let (ok, t_verescrow) = timed("VerEscrow", || {
            rust::ppb::verify_escrow(&lam, &pkA, &zesc.c_y, &zesc).expect("verescrow")
        });
        assert!(ok, "诚实托管必须通过 VerEscrow");

        let (out, t_dec) = timed("Dec", || {
            dec_ppb(&lam, &skA, &zesc.c_y, &zesc)
                .expect("dec 必须可运行")
                .expect("命中用户必须解出结果")
        });
        let z = out.z.clone().expect("命中用户必须解出具体身份");
        assert_eq!(z.y_id, y.y_id % &lam.cpar.n, "Dec 输出必须是 f_wl(x,y)");
        assert!(
            verify_poks3(&lam, &pkA.x_public.pk_ah, &pkA.c_d, &zesc.z_hat, &z, &out.pi_z)
                .expect("verify_poks3"),
            "dec 产出的 PoKS3 必须独立可验"
        );

        let (ok, t_judge) = timed("Judge", || {
            judge_ppb(&lam, &pkA, &pkA.c_x, &zesc.c_y, &zesc, &out.z, &out.pi_z).expect("judge")
        });
        assert!(ok, "诚实审计结果必须通过 Judge");

        s.keygen.push(t_keygen.as_secs_f64());
        s.verpk.push(t_verpk.as_secs_f64());
        s.escrow.push(t_escrow.as_secs_f64());
        s.verescrow.push(t_verescrow.as_secs_f64());
        s.dec.push(t_dec.as_secs_f64());
        s.judge.push(t_judge.as_secs_f64());

        // ── 体积 ──────────────────────────────────────────────────────────
        let pi_a = pkA.pi_a.size();
        let pi_u_raw = zesc.pi_u.size();
        let pi_u_net = pi_u_raw - redundant_bytes(&zesc.pi_u);
        let pi_z = out.pi_z.size();
        let ect_x = ect_x_bytes(&pkA.x_public);
        // pk_A = (X, Cx, Cd, πA)，见论文 Fig. 5.4 KeyGen 第 8 行。
        let pk_bytes = ect_x + pkA.c_x.size() + pkA.c_d.size() + pi_a;
        let zhat_bytes = zesc.z_hat.z_id.size() + zesc.z_hat.z_at.size() + zesc.z_hat.z_nf.size();
        last_sizes = Some((pi_a, pi_u_raw, pi_u_net, pi_z, pk_bytes, zhat_bytes, zesc.c_y.size(), ect_x));

        writeln!(
            csv,
            "{},{},{},{rep},{:.6},{:.6},{:.6},{:.6},{:.6},{:.6},{pi_a},{pi_u_raw},{pi_u_net},{pi_z},{ect_x},{pk_bytes},{zhat_bytes}",
            p.name,
            p.ell_n,
            p.n,
            t_keygen.as_secs_f64(),
            t_verpk.as_secs_f64(),
            t_escrow.as_secs_f64(),
            t_verescrow.as_secs_f64(),
            t_dec.as_secs_f64(),
            t_judge.as_secs_f64(),
        )
        .ok();
        csv.flush().ok();
    }

    let (pi_a, pi_u_raw, pi_u_net, pi_z, pk_bytes, zhat_bytes, cy_bytes, ect_x) =
        last_sizes.expect("至少跑一次重复");

    // ── 汇总 ────────────────────────────────────────────────────────────────
    let mut md = String::new();
    writeln!(md, "## {} — Griffy et al.\n", p.name).ok();
    writeln!(
        md,
        "ℓ_N={} n={} 重复={} 次（均值 ± 标准差）\n",
        p.ell_n, p.n, p.reps
    )
    .ok();
    writeln!(md, "### tab:computation-time（秒，Setup 排除）\n").ok();
    writeln!(
        md,
        "| KeyGen | VerPK | WLEnc | VerECT | Escrow | VerEscrow | Dec | Judge |"
    )
    .ok();
    writeln!(md, "|---|---|---|---|---|---|---|---|").ok();
    writeln!(
        md,
        "| {} | {} | -- | -- | {} | {} | {} | {} |",
        stat_cell(&s.keygen),
        stat_cell(&s.verpk),
        stat_cell(&s.escrow),
        stat_cell(&s.verescrow),
        stat_cell(&s.dec),
        stat_cell(&s.judge),
    )
    .ok();
    writeln!(
        md,
        "\n`WLEnc` / `VerECT` 填 `--`：Griffy 方案把名单加密并入 KeyGen，没有独立阶段。\n"
    )
    .ok();
    writeln!(md, "### tab:proof-size（KiB，最小幅值字节之和）\n").ok();
    writeln!(md, "| \\|π_A\\| | \\|π_x\\| | \\|π_U\\| | \\|π_Z\\| |").ok();
    writeln!(md, "|---|---|---|---|").ok();
    writeln!(
        md,
        "| {:.2} | -- | {:.2} | {:.2} |",
        pi_a as f64 / 1024.0,
        pi_u_raw as f64 / 1024.0,
        pi_z as f64 / 1024.0
    )
    .ok();
    writeln!(
        md,
        "\n`|π_x|` 填 `--`：名单密文正确性证明已并入 `π_A`。\n"
    )
    .ok();
    writeln!(md, "### 其余对象（KiB）\n").ok();
    writeln!(md, "| ect_x = X | pk_A | Ẑ | C_y | \\|π_U\\| 净值 |").ok();
    writeln!(md, "|---|---|---|---|---|").ok();
    writeln!(
        md,
        "| {:.2} | {:.2} | {:.2} | {:.2} | {:.2} |",
        ect_x as f64 / 1024.0,
        pk_bytes as f64 / 1024.0,
        zhat_bytes as f64 / 1024.0,
        cy_bytes as f64 / 1024.0,
        pi_u_net as f64 / 1024.0
    )
    .ok();
    writeln!(
        md,
        "\n`ect_x` 是 Griffy 侧与 Ours 的 `ect_x` 对应的对象：HECenc 的公开输出\n\
         `X = (pk_AH, A_1..A_{{n+1}})`，共 `2(n+1)+1` 个 `Z_{{N²}}` 元素。\n\
         Griffy 没有独立的 WLEnc 阶段，`X` 直接作为 `pk_A` 的第一个分量发布。\n"
    )
    .ok();

    println!();
    println!("tab:computation-time（秒，Setup 排除）:");
    println!("  KeyGen      {:>20} s", stat_cell(&s.keygen));
    println!("  VerPK       {:>20} s", stat_cell(&s.verpk));
    println!("  WLEnc       {:>20}", "--");
    println!("  VerECT      {:>20}", "--");
    println!("  Escrow      {:>20} s", stat_cell(&s.escrow));
    println!("  VerEscrow   {:>20} s", stat_cell(&s.verescrow));
    println!("  Dec         {:>20} s", stat_cell(&s.dec));
    println!("  Judge       {:>20} s", stat_cell(&s.judge));

    println!();
    println!("tab:proof-size（最小幅值字节之和，即紧致下界）:");
    println!("  |π_A|  {}", kib(pi_a));
    println!("  |π_x|  {:>16}", "--");
    println!("  |π_U|  {}   （原样计，含冗余字段）", kib(pi_u_raw));
    println!("  |π_Z|  {}", kib(pi_z));
    println!();
    println!("  |π_U| 剔除可从公开语句恢复的字段后 {}", kib(pi_u_net));
    println!(
        "    其中冗余部分（tau.c_values 等）{}",
        kib(pi_u_raw - pi_u_net)
    );
    println!(
        "  ect_x  {}   （= X = (pk_AH, A_1..A_{{n+1}})，Griffy 的加密名单）",
        kib(ect_x)
    );
    println!("  pk_A   {}   （= X + C_x + C_d + π_A）", kib(pk_bytes));
    println!("  Ẑ      {}", kib(zhat_bytes));
    println!("  C_y    {}", kib(cy_bytes));
    println!(
        "  用户上行 = Ẑ + C_y + π_U  {}",
        kib(zhat_bytes + cy_bytes + pi_u_raw)
    );

    fs::write(&md_path, md).expect("写 markdown");
    println!();
    println!("原始数据 → {}", csv_path.display());
    println!("可粘贴的表 → {}", md_path.display());
    println!();
    print_caveats();
}

// ============================================================================
// 需要人来定的参数
// ============================================================================
//
// ── A. 必须先定，且**直接改变表格里的数字** ─────────────────────────────────
//
// 1. ℓ_N（`ell_n`）→ 代码里的 `setup_ppb(lambda_bits, ..)`。
//    含义：RSA 模数 `N = pq` 的位长。这是本方案**唯一真正的安全旋钮**，
//    所有东西都挂在它上面：
//      · 群元素在 `Z_{N²}`，每个 `2ℓ_N` 位  ⇒ 直接决定所有证明体积；
//      · 明文空间 `M = Z_N`，`ℓ_N` 位       ⇒ y_id / y_at / 多项式系数 / r_i 的位长；
//      · `B = 2ℓ_N − 2`（`derive_b_bits_from_n2`）⇒ DF 承诺的消息上界；
//      · 承诺开口随机数 `B + λ`、Σ 协议盲化 `B + 2λ`（λ 见第 3 条）。
//    代价实测按 `ℓ_N^2.76` 增长（512→4096 约 311 倍）。
//    论文参数集给 4096（τ=80）/ 4608（τ=128）。
//
// 2. n（`n`）：名单规模。**硬约束：`n+1` 必须是 2 的幂**（`pokp` 的 Alg. 2 二分递归）。
//    含义：审计方名单 `x = {x_1..x_n}`，多项式 `P(χ) = s·Π(χ − x_i)` 有 `n+1` 个系数，
//    公开包 `X = (pk_AH, A_1..A_{n+1})`。它是 KeyGen/VerPK 的**线性乘数**，
//    也是 Escrow/VerEscrow/Dec/Judge 的线性项（注意：只有**证明体积**是 O(log n)，
//    **计算量是 O(n)**——多项式求值本身就得碰每个系数）。
//    论文参数集只给到 `B·(Δ+1)`，且 `B ≤ 128`（正文）与 `B ≤ 100`（附录）**互相矛盾**。
//    本文件按附录取 B=100、Δ=127 ⇒ 名义名单 12800；12801 不是 2 的幂，
//    按论文脚注 14 补齐到 16384，等价地取 n = 16383。
//    ⚠️ 若改用 B=128 ⇒ 名义 16512 ⇒ 要补到 32768，**所有 O(n) 项翻倍**。
//
// 3. τ 怎么落地。**论文有 τ，本实现没有对应旋钮**：
//    `derive_poks1_blinding_bits` 写的是 `B + 2·lambda_bits`，而 `lambda_bits` 就是 ℓ_N，
//    于是盲化指数被迫到 `≈ 4ℓ_N`（4096 时 16382 位），而论文要的是 `B + 2τ`（≈ 8350 位）。
//    后果：**rowA 与 rowB 目前只差 ℓ_N，τ 那一列是名义值**；且 Griffy 的 Σ 协议
//    比忠实实现慢约 2 倍（实测 modexp：指数 4096 位 147 ms vs 16384 位 580 ms）。
//    两个选择：(a) 照现状测并在表注声明；(b) 给 `PpbParams` 加 `stat_bits = τ`，
//    盲化改成 `B + 2τ`——不改变任何关系式，只是把被复用的参数拆开，总时间约减半。
//
// 4. `|π_U|` 的口径：是否剔除可从公开语句恢复的字段。
//    `pi_poly.tau.c_values` 是审计方公钥 `A_1..A_{n+1}` 的**完整副本**
//    （论文 Alg. 1 第 3 行写明 τ 是 Fiat–Shamir 的哈希输入，属公开语句）。
//    在 n=16383 / ℓ_N=4096 下它单项约 32 MiB，会让 escrow 体积从论文自述的
//    `28kB × log(n)` 变成 O(n)，在表里直接推翻论文的中心结论。
//    本文件两个数都输出，填表前必须二选一并写进表注。
//
// 5. reps（第二个命令行参数）：重复次数。
//    与 "Ours" 对齐需要 5–10 次取均值，但 rowA 单次重复约 22 小时、rowB 约 31 小时。
//    这是"统计可信度 vs 机时"的取舍，只能由人定。
//    实测同一配置跨会话能差 10–40%（降频/堆状态），所以**至少 3 次**才有意义。
//
// ── B. 必须先定，但只影响**可比性**，不改变本方案自身的数字 ─────────────────
//
// 6. 体积编码口径。本文件用**最小幅值字节数**（`to_bytes_be().len()`），
//    与 "Ours" 侧的基准一致，是紧致下界。真实传输会用定长
//    （每个 `Z_{N²}` 元素 `2ℓ_N/8` 字节），那个数会略大。两行必须同口径。
//
// 7. 机器与线程。Griffy 这份实现是**纯单线程**（`num-bigint`，无 rayon、无并行）；
//    若 "Ours" 是多线程，两行不可直接比。要么在表注声明，要么把 Griffy 的 O(n) 循环
//    也并行化后再测。同机是最低要求。
//
// 8. 命中还是未命中。本文件取 `y_id = x[n/2]`（**命中名单**），因为那是最长路径：
//    `HECdec` 必须解出具体身份，`Dec` 才会真的生成 π_Z，`Judge` 才会真的验 VS3。
//    未命中时 `dec_ppb` 提前返回 `None`，Dec/Judge 都会显著变快——那不是最坏情况。
//
// ── C. 被实现层约束逼出来的取值（不是自由选择，但必须知道） ─────────────────
//
// 9. `y_id + y_at < N`。`map_y_to_df_message` 算的是 `(y_id+y_at) mod N`，
//    而验证侧比对的 `C_id · C_at = Com(y_id + y_at)` 用的是**整数和**，
//    两者只在不溢出时相等。所以本文件把 `y_id`、`y_at` 都取自 `[0, N/2)`。
//    位长仍是 `ℓ_N − 1`，对指数代价而言与满位长等价。
//    ⚠️ **绝不能用 3、5、7 这类小整数**：那会让 modexp 的指数只有几 bit，
//    把真实代价整体压低一个数量级（详见 AUDIT_POKP.md §4.7）。
//
// 10. `r_y` 不能自由选。`escrow_ppb` 强制 `r_y = r_id + r_at (mod N)`
//     （`sample_hec_eval_randomness`）。论文里 `C_y` 是用户既有凭证上的承诺、
//     开口 `r_y` 由外部给定；这里等于反过来由 Escrow 决定 `r_y`。
//     基准里随便取一个 `r_y` 即可，但这条限制在语义上是个偏离，值得记一笔。
//
// ── D. 记录在案、但当前实现中**完全不起作用** ───────────────────────────────
//
// 11. λ（`lambda`）：论文的计算安全参数 128。代码里没有独立的 λ——
//     `PpbParams.lambda_bits` 被当成 ℓ_N 用（见第 3 条）。这里只作记录。
//
// 12. k（`HecFunctionKey.k`）：论文 `f_{n,k}` 里 `y_at` 的比特长度。
//     代码里存了但**从不参与计算**（`hec_eval` 的 `_ell` 参数未使用）。
//     原因是 Camenisch–Shoup 的 `g` 是恒等映射，`y_at` 直接就是 `Z_N` 里一个整数，
//     不需要像 ElGamal 那样按 k 位分块暴力搜索（论文 Sec 5.2 结尾专门讨论了这点）。
//     取任意值都行，本文件取 1。
//
// 13. s（`keygen_ppb` 的掩码）：论文 `s ←$ M_{pk_AH}` 是在 HECenc 内部采样的；
//     代码把它提到接口上，是为了让 PoKS1 能证明"公开的 A_i 和 witness 用的是同一份
//     随机性"。基准里取 `Z_N` 中的随机非零值即可，不需要人调。
//
// ── E. 由上面几项推导，不用人管 ─────────────────────────────────────────────
//
//     B = 2ℓ_N − 2                     DF 承诺消息上界
//     承诺开口随机数位长 = B + λ        `derive_df_commit_randomness_bits`
//     Σ 协议盲化位长     = B + 2λ       `derive_poks1_blinding_bits`
//     PoKP 递归层数      = log2(n+1)
//     aux 链条数         = log2(n+1) − 1（最高层的 half 只到 2^{rounds−1}）
//     Fiat–Shamir 挑战   ∈ Z_N          `nonzero_challenge_mod_n`
//                                       （论文 Lemma 14：可靠性误差是 d/p，
//                                        p 是 N 的**较小**素因子，所以挑战必须取满 Z_N，
//                                        不能像素域方案那样只取 128 位）

/// 填表时必须一并写进表注的事项。
fn print_caveats() {
    println!("填表须知（务必写进表注）:");
    println!("  1. WLEnc / VerECT / |π_x| 填 `--`：Griffy 无独立的名单加密阶段。");
    println!("  2. τ 在本实现里没有旋钮（盲化用 B+2·ℓ_N 而非 B+2τ），");
    println!("     rowA/rowB 的差别仅来自 ℓ_N。若解耦 τ，Σ 协议部分约可再省一半。");
    println!("  3. KeyGen/VerPK 是**低估**：本实现的 C_x 承诺的是多项式系数向量而非名单 x，");
    println!("     π_A 未证明 root→coefficient 展开（论文 Fig. 5.4 的 Ψ1 要求证明）。");
    println!("  4. |π_U| 的 raw 口径含 tau.c_values（审计方公钥副本），会让 escrow 体积");
    println!("     从论文自述的 O(log n) 变成 O(n)。两个口径都已输出，填表前请先定口径。");
    println!("  5. 体积口径为最小幅值字节之和（紧致下界），与 Ours 侧基准一致。");
    println!("  6. Setup 已排除；参数在所有重复间复用。");
}
