//! Honest table-17 trace generator for `nearAirV3` (`acctTableV3` =
//! `{AccountEmpty.table with maxLog := 19}`, `Assembly/NearAir.lean`), the Rust
//! twin of the Lean honest render `acctTraceAlignedE`
//! (`Render/PaddedAcctE.lean`): no account (`as = []`) gives the all-zero trace
//! of log 1 (`AccountEmpty.emptyTrace`); otherwise the aligned generator
//! `acctTraceAligned` (`Render/PaddedRcpt.lean`: `AcctV3Gen.cell`,
//! `Rcpt/Render/AcctRender.lean`, at `padLog22 (logOf (16 · |as|))`).  Both
//! cases are the same formula here (`padLog22 (logOf 0) = 1`, no active row).
//!
//! Input: the `List AcctV` entries (a v1 view at `Near/Extract/SmallViews.lean`:
//! `k`, `tlast`, the 72 canonical `pre` bytes and the 16 canonical `post` bytes),
//! deserialized from JSON with the Lean field names.  Every cell is reduced mod
//! `P`.  `conformance/run-v2.d/rcs.sh` compares the dumps with
//! `np-lean-render-v3-rcs` byte for byte.

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::Deserialize;

use crate::field::F;

use super::{Tab, b, get, log_of, pad_log22};

pub const ACCT_WIDTH: usize = 16;

/// A v1 `AcctV` view (`Near/Extract/SmallViews.lean:54`): touched slot `k`, the
/// time of the closing memory read `tlast`, the 72 raw pre bytes and the 16 raw
/// post amount bytes.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct AcctV {
    pub k: u64,
    pub tlast: u64,
    pub pre: Vec<u64>,
    pub post: Vec<u64>,
}

/// `AcctGen.dsumOf v i = Σ_{j ≤ i} (255 − v_j)` over the naturals.
fn dsum_of(v: &[u64], i: usize) -> u64 {
    (0..=i).map(|j| 255u64.saturating_sub(get(v, j))).sum()
}

/// `invP x`: the field inverse `x⁻¹` (`0 ↦ 0`).
fn inv_p(x: u64) -> u64 {
    F::from_u64(x)
        .try_inverse()
        .unwrap_or(F::ZERO)
        .as_canonical_u32() as u64
}

/// `AcctV3Gen.actCell as q`: the lane cells of active row `q` (`q < 16·|as|`),
/// with lane `i = q % 16`.
fn act_cell(a: &[AcctV], q: usize) -> [u64; ACCT_WIDTH] {
    let e = a.get(q / 16).cloned().unwrap_or_default();
    let i = q % 16;
    let pre = &e.pre;
    let mut c = [0u64; ACCT_WIDTH];
    c[0] = 1;
    c[1] = b(i == 0);
    c[2] = b(i == 15);
    c[3] = e.k;
    c[4] = i as u64;
    c[5] = e.tlast;
    c[6] = get(pre, i);
    c[7] = get(&e.post, i);
    c[8] = get(pre, 16 + i);
    c[9] = if i < 8 { get(pre, 64 + i) } else { 0 };
    c[10] = get(pre, 32 + 2 * i);
    c[11] = get(pre, 33 + 2 * i);
    c[12] = b(i < 8);
    c[13] = dsum_of(pre, i);
    c[14] = if i == 15 { inv_p(dsum_of(pre, 15)) } else { 0 };
    c[15] = b(i < 8);
    c
}

/// `acctTraceAlignedE as`: 16 rows per record, zero padding to
/// `2^padLog22(logOf (16·|as|))` (log 1, all zero, for `as = []`).
pub fn acct_aligned(a: &[AcctV]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(16 * a.len())), ACCT_WIDTH);
    let h = t.height();
    for q in 0..(16 * a.len()).min(h) {
        for (c, x) in act_cell(a, q).into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

pub fn render(json: &str) -> Result<Tab, String> {
    let a: Vec<AcctV> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(acct_aligned(&a))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_hand_checked_first_record() {
        let e = AcctV {
            k: 7,
            tlast: 3,
            pre: {
                let mut v = vec![9u64; 72];
                v[0] = 0;
                v
            },
            post: vec![1u64; 16],
        };
        let t = acct_aligned(&[e]);
        // logOf 16 = 4 -> log 4, 16 rows
        assert_eq!(t.log, 4);
        assert_eq!(t.height(), 16);
        let at = |r: usize, c: usize| t.cells[r * ACCT_WIDTH + c];
        assert_eq!(at(0, 0), 1);
        assert_eq!(at(0, 1), 1); // af
        assert_eq!(at(15, 2), 1); // al
        assert_eq!(at(0, 3), 7); // k
        assert_eq!(at(0, 13), 255); // dsum lane 0 = 255 - 0
        assert_eq!(at(15, 13), 255 + 15 * 246); // 255 - 9 = 246 each lane
        assert_eq!(at(0, 12), 1); // lo8
        assert_eq!(at(8, 12), 0); // i = 8 >= 8
    }

    #[test]
    fn empty_is_log1_zero() {
        let t = acct_aligned(&[]);
        assert_eq!(t.log, 1);
        assert!(t.cells.iter().all(|&x| x == 0));
    }
}
