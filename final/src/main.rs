mod commit;
mod setup;

use num_bigint::BigUint;

// 使用 ppb 的 Pedersen 承诺
use rust::{setup_pedersen, commit_pedersen_with_opening, PedersenCommitmentParams};

// 使用 SPS-EQ 的签名
use sps_eq::sign::{keygen, SecretKey, PublicKey, Signature};

fn main() {
    println!("=== Algorithm 2: Setup 演示 ===\n");

    // 准备输入参数
    let lambda_bits = 64;   // 安全参数 λ
    let t = 3;              // 阈值参数 t
    let cpar_star = setup_pedersen(lambda_bits)
        .expect("Failed to setup Pedersen commitment params (cpar*)");
    println!("输入参数准备完毕: lambda_bits={}, t={}", lambda_bits, t);
    println!("cpar* (Pedersen 承诺参数) 已生成");

    // 调用 Algorithm 2: Setup
    let lambda = setup::setup(lambda_bits, t, cpar_star);

    println!("\n=== Setup 输出 Λ ===");
    println!("pp (Mercurial Signature 公共参数): 已生成");
    println!("cpar* (Pedersen 承诺参数): 已包含");
    println!("cpar  (DF 承诺参数): n 位长 = {} bits", lambda.cpar.n.bits());
    println!("inv   (随机 G1 元素): 已生成");
    println!("Λ_BLUE (ppb 参数): lambda_bits = {}", lambda.lambda_blue.lambda_bits);
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
    println!("  多项式 P 的系数 (a_0, ..., a_{{|x|}}) = {:?}", poly_commit.coeffs);
    println!("  承诺值 C_x 的位长 = {} bits", poly_commit.c.bits());
    println!("  C_x = {}", poly_commit.c);

    println!("\n=== 完成 ===");
}
