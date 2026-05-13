/// 密码学原语统一错误类型。
///
/// 设计原则：
/// 1. 所有对外接口都返回 Result，避免 panic 破坏协议流程。
/// 2. 错误信息聚焦“可定位性”，便于上层协议快速识别失败原因。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CryptoError {
    /// 入参不满足协议定义（例如消息不在指定区间）。
    InvalidInput(&'static str),
    /// 模逆不存在，通常意味着参与求逆的值与模数不互素。
    ModularInverseUnavailable,
    /// 安全素数或安全 RSA 模数生成失败。
    PrimeGenerationFailed,
}

/// 全库统一 Result 别名。
pub type CryptoResult<T> = Result<T, CryptoError>;
