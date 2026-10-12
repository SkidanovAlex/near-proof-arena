//! Honest `sizeA7` trace generator (`nearAirV3` table 21), the Rust twin of the
//! Lean aligned render `sizeA7Trace pub v t (yA7 y0 y1 y2)`
//! (`ZkFormal/NearV3/Render/UnfoldA7Aligned.lean`): the base
//! `sizeTraceAligned pub v` (`Render/PaddedRcpt.lean`: `SizeGen.cell`,
//! `Rcpt/Render/SizeRender.lean`, at the cap `sizeCapV3 = 4`, i.e. 16 rows —
//! rows `0..2` carry the three totals, rows `≥ 3` are padding with only the
//! row counter `t = q`) with the A7 columns of `sizeCols yN`
//! (`Render/UnfoldA7Ext.lean`): `y` (31) = `yN q`, `u` (32) = `Σ_{i ≤ q} yN i`,
//! `ub` (33..56) the 24 bits of `B0 − u` (natural subtraction, `B0 = 2,000,000`).
//!
//! Input: `SizeV {x0, x1, x2}` (the three received `SIZE` totals), the public
//! witness overhead `ovh = ovhNat pub` (`pubNat pub (PH_WOVH + 0..3)`, taken here
//! as a JSON field) and the optional received A7 totals `"yN": [y0, y1, y2]`
//! (node, val, ups; `yA7`, default zeros, entries past 3 ignored).  Width 57,
//! every cell reduced mod `P`.  `conformance/run-v2.d/a7.sh` compares the dumps
//! with `np-lean-render-v3-a7 size` byte for byte.

use serde::Deserialize;

use super::Tab;

/// `SizeV3.width` (the base columns).
pub const SIZE_WIDTH: usize = 31;
/// `sizeA7` width: base + `y` (31) + `u` (32) + `ub` (33..56).
pub const SIZE_A7_WIDTH: usize = 57;
/// `sizeCapV3`: the aligned height is `2^4`.
pub const SIZE_LOG: usize = 4;
/// `UnfoldA7.B0`, the A7 bound.
pub const B0: u64 = 2_000_000;

/// A v3 `SizeV` view (`ZkFormal/NearV3/Rcpt/Extract/SizeProof.lean:22`): the
/// three received totals.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct SizeV {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
}

/// The `ovhNat pub` field of the size differential (the public `u32` witness
/// overhead, little-endian, at `PH_WOVH`).
#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub struct SizeInput {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
    #[serde(default)]
    pub ovh: u64,
    /// the received A7 totals `yA7 y0 y1 y2` (node, val, ups); absent → zeros.
    #[serde(default, rename = "yN", skip_serializing_if = "Vec::is_empty")]
    pub y_n: Vec<u64>,
}

/// `SizeGen.xAt v q`.
fn x_at(v: &SizeV, q: usize) -> u64 {
    match q {
        0 => v.x0,
        1 => v.x1,
        2 => v.x2,
        _ => 0,
    }
}

/// `SizeGen.totAt v q`: the running sum `x_0 + … + x_q`.
fn tot_at(v: &SizeV, q: usize) -> u64 {
    match q {
        0 => v.x0,
        1 => v.x0 + v.x1,
        2 => v.x0 + v.x1 + v.x2,
        _ => 0,
    }
}

/// `SizeGen.baseAt v q`: `x_0`, then `x_0 + x_1` on rows 1 and 2.
fn base_at(v: &SizeV, q: usize) -> u64 {
    match q {
        0 => v.x0,
        1 | 2 => v.x0 + v.x1,
        _ => 0,
    }
}

/// `SizeGen.bv pub v q`: the 24-bit slack of row `q` (natural subtraction, so a
/// negative slack becomes 0).
fn bv(ovh: u64, v: &SizeV, q: usize) -> u64 {
    match q {
        1 => 3_000_000u64.saturating_sub(v.x0 + v.x1),
        2 => 8_388_608u64
            .saturating_sub(ovh)
            .saturating_sub(v.x0 + v.x1 + v.x2),
        _ => 0,
    }
}

/// `SizeGen.cell pub v q`: row `q` of the honest table.
fn cell(ovh: u64, v: &SizeV, q: usize) -> [u64; SIZE_WIDTH] {
    let mut c = [0u64; SIZE_WIDTH];
    c[0] = (q < 3) as u64;
    c[1] = q as u64;
    c[2] = x_at(v, q);
    c[3] = tot_at(v, q);
    c[4] = base_at(v, q);
    c[5] = (q == 1) as u64;
    c[6] = (q == 2) as u64;
    let slack = bv(ovh, v, q);
    for e in 0..24 {
        c[7 + e] = (slack >> e) & 1;
    }
    c
}

/// `sizeTraceAligned pub v` = `mkTab (2^sizeCapV3) SizeV3.width (SizeGen.cell pub v)`.
pub fn size_aligned(ovh: u64, v: &SizeV) -> Tab {
    let mut t = Tab::zero(SIZE_LOG, SIZE_WIDTH);
    for q in 0..t.height() {
        for (c, x) in cell(ovh, v, q).into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

/// `sizeA7Trace pub v t (yA7 y[0] y[1] y[2])`: [`size_aligned`] plus `sizeCols`.
pub fn size_a7(ovh: u64, v: &SizeV, y: &[u64]) -> Tab {
    let base = size_aligned(ovh, v);
    let mut t = super::widen(&base, SIZE_A7_WIDTH);
    let mut u: u128 = 0;
    for q in 0..t.height() {
        let yq = if q < 3 {
            y.get(q).copied().unwrap_or(0)
        } else {
            0
        };
        u += yq as u128;
        t.set(q, 31, yq);
        t.set(q, 32, (u % crate::field::P as u128) as u64);
        let slack = (B0 as u128).saturating_sub(u) as u64;
        for e in 0..24 {
            t.set(q, 33 + e, (slack >> e) & 1);
        }
    }
    t
}

pub fn render(json: &str) -> Result<Tab, String> {
    let mut es: Vec<SizeInput> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    if es.len() != 1 {
        return Err(format!(
            "size: expected exactly one entry, got {}",
            es.len()
        ));
    }
    let input = es.swap_remove(0);
    let v = SizeV {
        x0: input.x0,
        x1: input.x1,
        x2: input.x2,
    };
    Ok(size_a7(input.ovh, &v, &input.y_n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn four_rows_and_bounds() {
        let v = SizeV {
            x0: 1000,
            x1: 2000,
            x2: 3000,
        };
        let t = size_aligned(500, &v);
        assert_eq!(t.log, SIZE_LOG);
        assert_eq!(t.height(), 16);
        let at = |r: usize, c: usize| t.cells[r * SIZE_WIDTH + c];
        assert_eq!(at(0, 0), 1); // act
        assert_eq!(at(3, 0), 0); // padding row inactive
        assert_eq!(at(1, 5), 1); // lb
        assert_eq!(at(2, 6), 1); // la
        assert_eq!(at(1, 3), 3000); // tot
        assert_eq!(at(2, 4), 3000); // base
        // slack row 1 = 3_000_000 - 3000 = 2_997_000
        let s1: u64 = (0..24).map(|e| (at(1, 7 + e) as u64) << e).sum();
        assert_eq!(s1, 2_997_000);
        // slack row 2 = 8_388_608 - 500 - 6000 = 8_382_108
        let s2: u64 = (0..24).map(|e| (at(2, 7 + e) as u64) << e).sum();
        assert_eq!(s2, 8_382_108);
        // padding rows: only the row counter
        for q in 3..16 {
            for c in 0..SIZE_WIDTH {
                assert_eq!(
                    at(q, c),
                    if c == 1 { q as u32 } else { 0 },
                    "row {q} col {c}"
                );
            }
        }
    }

    #[test]
    fn a7_columns() {
        let v = SizeV {
            x0: 1,
            x1: 2,
            x2: 3,
        };
        let t = size_a7(0, &v, &[700_000, 600_000, 500_000, 99]);
        assert_eq!((t.log, t.width), (SIZE_LOG, SIZE_A7_WIDTH));
        let at = |r: usize, c: usize| t.cells[r * SIZE_A7_WIDTH + c] as u64;
        let bits = |r: usize| (0..24).map(|e| at(r, 33 + e) << e).sum::<u64>();
        assert_eq!(
            (at(0, 31), at(0, 32), bits(0)),
            (700_000, 700_000, 1_300_000)
        );
        assert_eq!(
            (at(2, 31), at(2, 32), bits(2)),
            (500_000, 1_800_000, 200_000)
        );
        // `yA7` is zero past row 2; `u` stays at the total
        assert_eq!((at(3, 31), at(15, 32), bits(15)), (0, 1_800_000, 200_000));
        // over the bound: the slack is the natural `B0 − u = 0`
        let t = size_a7(0, &v, &[B0, 1, 0]);
        assert!((0..24).all(|e| t.cells[2 * SIZE_A7_WIDTH + 33 + e] == 0));
    }

    #[test]
    fn a7_constraints() {
        // the 27 appended constraints (`NEARAIRV3_JSON`): honest at and below
        // the bound; `u`, `y` and the bits of the last active row are pinned
        let v = SizeV {
            x0: 10,
            x1: 20,
            x2: 30,
        };
        let cells = [
            (0, 32),
            (1, 32),
            (2, 32),
            (1, 31),
            (2, 31),
            (2, 33),
            (2, 40),
            (2, 56),
        ];
        for y in [[0, 0, 0], [700_000, 600_000, 500_000], [1, 2, B0 - 3]] {
            let t = size_a7(0, &v, &y);
            super::super::a7_test::honest_and_tampered(21, SIZE_WIDTH, &t, &cells);
        }
        // over the bound: the last active row's slack constraint fails
        if let Some(air) = super::super::a7_test::air() {
            let t = size_a7(0, &v, &[B0, 1, 0]);
            assert!(!super::super::a7_test::failing_new(&air, 21, SIZE_WIDTH, &t).is_empty());
        }
    }
}
