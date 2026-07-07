use num_bigint::BigUint;

use rust::{CryptoError, CryptoResult};

use crate::commit::PolyCommitment;

#[derive(Debug, Clone)]
pub struct WatchlistCommitments {
    pub prefix: Option<PolyCommitment>,
    pub remainder: PolyCommitment,
}

impl WatchlistCommitments {
    pub fn into_legacy_vec(self) -> Vec<Option<PolyCommitment>> {
        vec![self.prefix, Some(self.remainder)]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SplitWatchlist<'a> {
    pub prefix: Option<&'a [BigUint]>,
    pub remainder: &'a [BigUint],
    pub split_index: usize,
    pub remainder_len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpdateKind {
    FullRegeneration,
    ReusePrefix,
    NoChange,
}

#[derive(Debug, Clone, Copy)]
pub struct WatchlistUpdatePlan<'a> {
    pub kind: UpdateKind,
    pub old_len: usize,
    pub new_len: usize,
    pub delta: usize,
    pub old_remainder_len: usize,
    pub new_remainder: &'a [BigUint],
    pub new_split_index: usize,
}

pub fn split_watchlist<'a>(x: &'a [BigUint], t: usize) -> CryptoResult<SplitWatchlist<'a>> {
    if t == 0 {
        return Err(CryptoError::InvalidInput(
            "watchlist threshold t must be > 0",
        ));
    }
    if x.is_empty() {
        return Err(CryptoError::InvalidInput("watchlist must be non-empty"));
    }

    let len = x.len();
    let split_index = if len <= t {
        0
    } else {
        let alpha = len % t;
        if alpha == 0 { len - t } else { len - alpha }
    };

    let prefix = if split_index == 0 {
        None
    } else {
        Some(&x[..split_index])
    };
    let remainder = &x[split_index..];

    Ok(SplitWatchlist {
        prefix,
        remainder,
        split_index,
        remainder_len: remainder.len(),
    })
}

pub fn plan_watchlist_update<'a>(
    old_x: &[BigUint],
    new_x: &'a [BigUint],
    t: usize,
) -> CryptoResult<WatchlistUpdatePlan<'a>> {
    let old_split = split_watchlist(old_x, t)?;
    let new_split = split_watchlist(new_x, t)?;

    if old_x == new_x {
        return Ok(WatchlistUpdatePlan {
            kind: UpdateKind::NoChange,
            old_len: old_x.len(),
            new_len: new_x.len(),
            delta: 0,
            old_remainder_len: old_split.remainder_len,
            new_remainder: new_split.remainder,
            new_split_index: new_split.split_index,
        });
    }

    if !new_x.starts_with(old_x) {
        return Ok(WatchlistUpdatePlan {
            kind: UpdateKind::FullRegeneration,
            old_len: old_x.len(),
            new_len: new_x.len(),
            delta: new_x.len().saturating_sub(old_x.len()),
            old_remainder_len: old_split.remainder_len,
            new_remainder: new_split.remainder,
            new_split_index: new_split.split_index,
        });
    }

    let delta = new_x.len() - old_x.len();
    let kind = if old_split.remainder_len + delta > t {
        UpdateKind::FullRegeneration
    } else {
        UpdateKind::ReusePrefix
    };

    let new_remainder = match kind {
        UpdateKind::FullRegeneration => new_split.remainder,
        UpdateKind::ReusePrefix => {
            let new_remainder_len = old_split.remainder_len + delta;
            let start = new_x.len() - new_remainder_len;
            &new_x[start..]
        }
        UpdateKind::NoChange => new_split.remainder,
    };

    Ok(WatchlistUpdatePlan {
        kind,
        old_len: old_x.len(),
        new_len: new_x.len(),
        delta,
        old_remainder_len: old_split.remainder_len,
        new_remainder,
        new_split_index: new_x.len() - new_remainder.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn values(n: u32) -> Vec<BigUint> {
        (1..=n).map(BigUint::from).collect()
    }

    #[test]
    fn split_small_list_has_no_prefix() {
        let x = values(2);
        let split = split_watchlist(&x, 3).expect("split should succeed");

        assert!(split.prefix.is_none());
        assert_eq!(split.remainder, &x[..]);
        assert_eq!(split.split_index, 0);
    }

    #[test]
    fn split_large_non_multiple_keeps_remainder() {
        let x = values(5);
        let split = split_watchlist(&x, 3).expect("split should succeed");

        assert_eq!(split.prefix.unwrap(), &x[..3]);
        assert_eq!(split.remainder, &x[3..]);
        assert_eq!(split.remainder_len, 2);
    }

    #[test]
    fn split_large_multiple_moves_last_block_to_remainder() {
        let x = values(6);
        let split = split_watchlist(&x, 3).expect("split should succeed");

        assert_eq!(split.prefix.unwrap(), &x[..3]);
        assert_eq!(split.remainder, &x[3..]);
        assert_eq!(split.remainder_len, 3);
    }

    #[test]
    fn update_reuse_prefix_keeps_old_remainder() {
        let old_x = values(4);
        let new_x = values(5);
        let plan = plan_watchlist_update(&old_x, &new_x, 3).expect("plan should succeed");

        assert_eq!(plan.kind, UpdateKind::ReusePrefix);
        assert_eq!(plan.new_remainder, &new_x[3..]);
    }

    #[test]
    fn update_full_regeneration_when_remainder_overflows() {
        let old_x = values(4);
        let new_x = values(7);
        let plan = plan_watchlist_update(&old_x, &new_x, 3).expect("plan should succeed");

        assert_eq!(plan.kind, UpdateKind::FullRegeneration);
        assert_eq!(plan.new_remainder, &new_x[6..]);
    }

    #[test]
    fn update_full_regeneration_when_watchlist_is_replaced() {
        let old_x = vec![BigUint::from(42u32)];
        let new_x = values(5);
        let plan = plan_watchlist_update(&old_x, &new_x, 3).expect("plan should succeed");

        assert_eq!(plan.kind, UpdateKind::FullRegeneration);
        assert_eq!(plan.new_remainder, &new_x[3..]);
    }
}
