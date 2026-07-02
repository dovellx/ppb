use num_bigint::BigUint;

use rust::{
    dec_ppb, escrow_ppb, judge_ppb, keygen_ppb, setup_ppb, verify_poks3, HecEvalInput, HecFunctionKey,
};

// 端到端系统测试：覆盖完整顺序链路与关键反例。
// 顺序链路为 setup -> keygen -> escrow -> dec -> judge。
// 目标是确保协议在“正常输入”下通过，在“证明被篡改”时拒绝。

#[test]
fn test_ppb_system_full_flow_in_order() {
    // 1) setup：初始化系统公共参数，后续所有承诺/加密/证明都在该参数域下运行。
    let params = setup_ppb(64, &(), &(), &()).expect("setup should succeed");

    // 2) keygen：生成用户公私钥及注册阶段关联承诺。
    let x = vec![BigUint::from(5u32), BigUint::from(11u32), BigUint::from(13u32)];
    let fk = HecFunctionKey { n: x.len(), k: 1 };
    let r_x = BigUint::from(37u32);
    let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen should succeed");

    // 3) escrow：用户提交待托管输入 y，并生成/验证 escrow 侧证明对象。
    let y = HecEvalInput {
        y_id: BigUint::from(11u32),
        y_at: BigUint::from(29u32),
    };
    let r_y = BigUint::from(41u32);
    let escrow_out = escrow_ppb(&params, &pk_a, &y, &r_y)
        .expect("escrow should run")
        // 外层 Result 成功后，内层 Option 为 Some 表示 escrow 验证通过。
        .expect("escrow should pass verification");

    // 4) dec：先验证 escrow，再解密得到 z，并返回 PoKS3 证明。
    let dec_out = dec_ppb(&params, &sk_a, &escrow_out.c_y, &escrow_out)
        .expect("dec should run")
        .expect("dec should return output after successful escrow verification");

    let z = dec_out
        .z
        .clone()
        .expect("this scenario should decrypt to a concrete identity tuple");
    // 解密结果应与输入在模 n 意义下等价（协议在 Zn 上工作）。
    assert_eq!(z.y_id, y.y_id % &params.cpar.n);
    assert_eq!(z.y_at, y.y_at % &params.cpar.n);

    // dec 输出的 PoKS3 必须可独立通过验证。
    let poks3_ok = verify_poks3(
        &params,
        &pk_a.x_public.pk_ah,
        &pk_a.c_d,
        &escrow_out.z_hat,
        &z,
        &dec_out.pi_z,
    )
    .expect("verify_poks3 should run");
    assert!(poks3_ok);

    // 5) judge：最终裁决合取验证（VS3 ∧ VerPK ∧ VerEscrow）应为真。
    let judge_ok = judge_ppb(
        &params,
        &pk_a,
        &pk_a.c_x,
        &escrow_out.c_y,
        &escrow_out,
        &dec_out.z,
        &dec_out.pi_z,
    )
    .expect("judge should run");
    assert!(judge_ok);
}

#[test]
fn test_ppb_system_judge_rejects_tampered_dec_proof() {
    // 反例目标：只篡改 dec 产出的 PoKS3 响应，Judge 必须拒绝。
    // 先确保 setup -> keygen -> escrow -> dec 主链路本身可正常执行。
    let params = setup_ppb(64, &(), &(), &()).expect("setup should succeed");
    let x = vec![BigUint::from(7u32), BigUint::from(19u32), BigUint::from(23u32)];
    let fk = HecFunctionKey { n: x.len(), k: 1 };
    let r_x = BigUint::from(43u32);
    let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen should succeed");

    let y = HecEvalInput {
        y_id: BigUint::from(19u32),
        y_at: BigUint::from(31u32),
    };
    let r_y = BigUint::from(53u32);
    let escrow_out = escrow_ppb(&params, &pk_a, &y, &r_y)
        .expect("escrow should run")
        .expect("escrow should pass verification");

    let mut dec_out = dec_ppb(&params, &sk_a, &escrow_out.c_y, &escrow_out)
        .expect("dec should run")
        .expect("dec should return output");

    // 篡改 PoKS3 响应，模拟提交方伪造/破坏了解密知识证明。
    dec_out.pi_z.z_md += 1;

    let judge_ok = judge_ppb(
        &params,
        &pk_a,
        &pk_a.c_x,
        &escrow_out.c_y,
        &escrow_out,
        &dec_out.z,
        &dec_out.pi_z,
    )
    .expect("judge should run");

    // 最终裁决必须为 false，确保篡改证明不会被误接受。
    assert!(!judge_ok);
}

#[test]
fn test_ppb_system_judge_rejects_tampered_public_z() {
    // 反例目标：只篡改 dec 公开输出 z，不改证明本体，S3 必须拒绝。
    let params = setup_ppb(64, &(), &(), &()).expect("setup should succeed");
    let x = vec![BigUint::from(7u32), BigUint::from(19u32), BigUint::from(23u32)];
    let fk = HecFunctionKey { n: x.len(), k: 1 };
    let r_x = BigUint::from(43u32);
    let (pk_a, sk_a) = keygen_ppb(&params, &fk, &x, &r_x, &BigUint::from(1u32)).expect("keygen should succeed");

    let y = HecEvalInput {
        y_id: BigUint::from(19u32),
        y_at: BigUint::from(31u32),
    };
    let r_y = BigUint::from(53u32);
    let escrow_out = escrow_ppb(&params, &pk_a, &y, &r_y)
        .expect("escrow should run")
        .expect("escrow should pass verification");

    let mut dec_out = dec_ppb(&params, &sk_a, &escrow_out.c_y, &escrow_out)
        .expect("dec should run")
        .expect("dec should return output");
    dec_out.z.as_mut().expect("z should exist").y_id += BigUint::from(1u32);

    let judge_ok = judge_ppb(
        &params,
        &pk_a,
        &pk_a.c_x,
        &escrow_out.c_y,
        &escrow_out,
        &dec_out.z,
        &dec_out.pi_z,
    )
    .expect("judge should run");

    assert!(!judge_ok);
}
