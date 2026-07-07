use num_bigint::BigUint;

use r#final::{commit, keygen};

// 使用 ppb 的 Pedersen 承诺
use rust::setup_pedersen;

fn main() {
    println!("=== Algorithm 2: Setup 演示 ===\n");

    // 准备输入参数
    let lambda_bits = 64; // 安全参数 λ
    let t = 3; // 阈值参数 t
    let cpar_star =
        setup_pedersen(lambda_bits).expect("Failed to setup Pedersen commitment params (cpar*)");
    println!("输入参数准备完毕: lambda_bits={}, t={}", lambda_bits, t);
    println!("cpar* (Pedersen 承诺参数) 已生成");

    // 调用 Algorithm 2: Setup
    let lambda = r#final::setup::setup(lambda_bits, t, cpar_star);

    println!("\n=== Setup 输出 Λ ===");
    println!("pp (Mercurial Signature 公共参数): 已生成");
    println!("cpar* (Pedersen 承诺参数): 已包含");
    println!(
        "cpar  (DF 承诺参数): n 位长 = {} bits",
        lambda.cpar.n.bits()
    );
    println!("inv   (随机 G1 元素): 已生成");
    println!(
        "Λ_BLUE (ppb 参数): lambda_bits = {}",
        lambda.lambda_blue.lambda_bits
    );
    println!("t     (阈值): {}", lambda.t);

    // ================================================================
    // Algorithm 1: Commit 演示
    // ================================================================
    println!("\n=== Algorithm 1: Commit 演示 ===\n");

    // 准备输入：名单 x = (x_1, x_2, x_3)，随机数 r_x，掩码 s
    let x = vec![
        BigUint::from(5u32),
        BigUint::from(11u32),
        BigUint::from(13u32),
    ];
    let r_x = BigUint::from(37u32);
    let s = BigUint::from(7u32);
    println!("输入: x = {:?}, r_x = {}, s = {}", x, r_x, s);

    // 调用 Algorithm 1: Commit
    let poly_commit = commit::commit(&lambda, &x, &r_x, &s);

    println!("输出:");
    println!(
        "  多项式 P 的系数 (a_0, ..., a_{{|x|}}) = {:?}",
        poly_commit.coeffs
    );
    println!("  承诺值 C_x 的位长 = {} bits", poly_commit.c.bits());
    println!("  C_x = {}", poly_commit.c);

    // ================================================================
    // Algorithm 3: KeyGen 演示
    // ================================================================
    println!("\n=== Algorithm 3: KeyGen 演示 ===\n");

    // 场景 1: ℓ > t（|x| = 5, t = 3, α = 2 ≠ 0 → 分割为 x1[0:3], x2[3:5]）
    let x_keygen: Vec<BigUint> = (1..=5).map(|i| BigUint::from(i as u32)).collect();
    let r_x_keygen = vec![BigUint::from(100u32), BigUint::from(200u32)];
    let s_keygen = vec![BigUint::from(3u32), BigUint::from(5u32)];
    println!("场景 1: ℓ > t (|x|={}, t={})", x_keygen.len(), lambda.t);
    println!(
        "  x = {:?}, r_x = {:?}, s = {:?}",
        x_keygen, r_x_keygen, s_keygen
    );

    let ((pk, sk), c_x) = keygen::keygen(&lambda, &x_keygen, &r_x_keygen, &s_keygen);

    println!("  pk_Λ1 存在: {}", pk.pk1.is_some());
    println!("  pk_Λ2 存在: true");
    println!("  pk_SPS 存在: {}", pk.pk_sps.is_some());
    println!(
        "  C_x1 存在: {}, 系数数量: {}",
        c_x[0].is_some(),
        c_x[0].as_ref().map_or(0, |c| c.coeffs.len())
    );
    println!(
        "  C_x2 存在: {}, 系数数量: {}",
        c_x[1].is_some(),
        c_x[1].as_ref().map_or(0, |c| c.coeffs.len())
    );

    // 场景 2: ℓ ≤ t（|x| = 2, t = 3）
    let x_small = vec![BigUint::from(42u32), BigUint::from(99u32)];
    let r_x_small = vec![BigUint::from(10u32), BigUint::from(20u32)];
    let s_small = vec![BigUint::from(1u32), BigUint::from(2u32)];
    println!("\n场景 2: ℓ ≤ t (|x|={}, t={})", x_small.len(), lambda.t);
    println!(
        "  x = {:?}, r_x = {:?}, s = {:?}",
        x_small, r_x_small, s_small
    );

    let ((pk2, sk2), c_x2) = keygen::keygen(&lambda, &x_small, &r_x_small, &s_small);

    println!("  pk_Λ1 = ⊥: {}", pk2.pk1.is_none());
    println!("  pk_Λ2 存在: true");
    println!("  pk_SPS = ⊥: {}", pk2.pk_sps.is_none());
    println!("  C_x1 = ⊥: {}", c_x2[0].is_none());
    println!(
        "  C_x2 存在: {}, 系数数量: {}",
        c_x2[1].is_some(),
        c_x2[1].as_ref().map_or(0, |c| c.coeffs.len())
    );

    println!("\n=== 完成 ===");
}
