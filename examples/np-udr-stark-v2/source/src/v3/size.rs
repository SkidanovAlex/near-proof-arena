//! Honest `sizeV3` trace generator (part 2 extension), the Rust twin of the Lean
//! aligned generator `ZkFormal.NearV3.Render.SizeGen.cell` + `sizeRows`
//! (`ZkFormal/NearV3/Rcpt/Render/SizeRender.lean`, via the aligned wrapper
//! `sizeTraceAligned`).
//!
//! Input: `SizeV {x0, x1, x2}` (the three received `SIZE` totals) plus the public
//! witness overhead `ovh = ovhNat pub` (`pubNat pub (PH_WOVH + 0..3)`, taken here
//! as a JSON field), deserialized with the Lean field names.  Output: `sizeRows`
//! is `mkTab 4 SizeV3.width` (height 4, width 31); every cell is reduced mod `P`.
//! `conformance/run-v2.sh` compares the dumps with `np-lean-render-v3` byte for
//! byte.

use serde::Deserialize;

use super::Tab;

pub const SIZE_WIDTH: usize = 31;

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

/// `sizeRows pub v` = `mkTab 4 SizeV3.width` (height 4).
pub fn size_aligned(ovh: u64, v: &SizeV) -> Tab {
    let mut t = Tab::zero(2, SIZE_WIDTH);
    for q in 0..4 {
        for (c, x) in cell(ovh, v, q).into_iter().enumerate() {
            t.set(q, c, x);
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
    Ok(size_aligned(input.ovh, &v))
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
        assert_eq!(t.log, 2);
        assert_eq!(t.height(), 4);
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
    }
}
