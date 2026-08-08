## rowA(tau=80, paper) — Griffy et al.

ℓ_N=4096 n=16383 重复=1 次（均值 ± 标准差）

### tab:computation-time（秒，Setup 排除）

| KeyGen | VerPK | WLEnc | VerECT | Escrow | VerEscrow | Dec | Judge |
|---|---|---|---|---|---|---|---|
| 17154.304 | 1492.452 | -- | -- | 14796.564 | 1845.899 | 1945.380 | 3476.024 |

`WLEnc` / `VerECT` 填 `--`：Griffy 方案把名单加密并入 KeyGen，没有独立阶段。

### tab:proof-size（KiB，最小幅值字节之和）

| \|π_A\| | \|π_x\| | \|π_U\| | \|π_Z\| |
|---|---|---|---|
| 45.50 | -- | 34851.66 | 11.00 |

`|π_x|` 填 `--`：名单密文正确性证明已并入 `π_A`。

## rowB(tau=128, paper) — Griffy et al.

ℓ_N=4608 n=16383 重复=1 次（均值 ± 标准差）

### tab:computation-time（秒，Setup 排除）

| KeyGen | VerPK | WLEnc | VerECT | Escrow | VerEscrow | Dec | Judge |
|---|---|---|---|---|---|---|---|
| 24385.879 | 2036.342 | -- | -- | 20305.722 | 2652.620 | 2896.351 | 5705.931 |

`WLEnc` / `VerECT` 填 `--`：Griffy 方案把名单加密并入 KeyGen，没有独立阶段。

### tab:proof-size（KiB，最小幅值字节之和）

| \|π_A\| | \|π_x\| | \|π_U\| | \|π_Z\| |
|---|---|---|---|
| 51.12 | -- | 39207.40 | 12.38 |

`|π_x|` 填 `--`：名单密文正确性证明已并入 `π_A`。