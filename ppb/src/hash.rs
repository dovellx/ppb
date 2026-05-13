use num_bigint::BigUint;
use sha2::{Digest, Sha256};

/// Fiat-Shamir 变换中常用的挑战值生成函数。
///
/// 输入为多个字节片段（通常对应 transcript 中的字段），
/// 输出固定 32 字节挑战值，便于后续映射到标量域或整数域。
///
/// 注意：
/// 1. 该函数仅负责哈希拼接，不包含域分离标签；
/// 2. 若协议层需要严格域分离，应在 chunks 中显式加入标签字节串。
pub fn fiat_shamir_challenge(chunks: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for chunk in chunks {
        hasher.update(chunk);
    }
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// 把一个非负大整数按“长度前缀 + 本体字节”编码到 transcript 中。
///
/// 设计动机：
/// 1. 直接拼接变长字段会产生歧义风险；
/// 2. 长度前缀可以把字段边界写入 transcript，保证挑战输入可唯一还原；
/// 3. 这里统一使用 8 字节大端长度，便于跨模块复用。
///
/// 编码格式：
/// [len(8 bytes, BE)] || [value.to_bytes_be()]
fn append_biguint_with_len(transcript: &mut Vec<u8>, value: &BigUint) {
    let bytes = value.to_bytes_be();
    let len = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    transcript.extend_from_slice(&len.to_be_bytes());
    transcript.extend_from_slice(&bytes);
}

/// 统一的 BigUint Fiat-Shamir 挑战构造器。
///
/// 该函数将字段列表按顺序编码后做 SHA-256，返回非负 BigUint 挑战值。
/// 由于证明系统经常在整数域中计算响应（`z = k + e * w`），直接返回 BigUint
/// 可减少每个协议中重复的字节到整数转换逻辑。
///
/// 注意：
/// 1. 字段顺序由调用方负责，顺序变化会导致挑战变化；
/// 2. 若需要域分离标签（domain separator），应由调用方作为额外字段传入；
/// 3. 该函数不做“语义去重”，只做确定性编码与哈希。
pub fn fiat_shamir_challenge_biguints(values: &[&BigUint]) -> BigUint {
    let mut transcript = Vec::new();
    for value in values {
        append_biguint_with_len(&mut transcript, value);
    }
    let digest = fiat_shamir_challenge(&[&transcript]);
    BigUint::from_bytes_be(&digest)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;

    #[test]
    fn test_fiat_shamir_stable_output_len() {
        let c = fiat_shamir_challenge(&[b"alpha", b"beta"]);
        assert_eq!(c.len(), 32);
    }

    #[test]
    fn test_fiat_shamir_biguints_is_deterministic() {
        let a = BigUint::from(1u32);
        let b = BigUint::from(257u32);
        let c1 = fiat_shamir_challenge_biguints(&[&a, &b]);
        let c2 = fiat_shamir_challenge_biguints(&[&a, &b]);
        assert_eq!(c1, c2);
    }
}
