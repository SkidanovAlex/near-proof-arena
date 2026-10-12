//! Honest v1 `mrk`/`sort` trace generators for `nearAirV3` tables 23/24.
//!
//! `nearAirV3` reuses the v1 outcome-Merkle and receipt-id-sort tables at their
//! v3 heights (`Assembly/NearAir.lean:44-47`): table 23 is
//! `ZkFormal.NearV3.Candidates.MerklePublic.table` (v1 `Mrk.table` with the two
//! public index ranges `PV_N → PH_N`, `PV_OUT → PH_OUT` translated,
//! `Candidates/MerklePublic.lean:9-28`) and table 24 is v1 `Sort.table` with
//! `maxLog := 18`.
//!
//! The cell functions are exactly v1's
//! `ZkFormal.Near.Render.MrkGen.cell` (`Render/Mrk.lean:98`) and
//! `SortGen.cell` (`Render/Sort.lean:68`); the public-index translation is a
//! property of the *table's* constraints, not of the trace, so the rendered
//! cells are the v1 ones.  Where v1's `mrkRowsAll`/`sortRowsAll` sized the trace
//! at `2^logOf rows`, the v3 traces are fixed at the table height
//! (`MerkleRender.trace` log 19, `SortGeneral.trace` log 18), which is the v1
//! rows followed by zero padding.
//!
//! * `mrk` input: a `MrkV` (`Extract/SmallViews.lean:133`) — the leaf count `n`,
//!   the root reference `(J, rootId, rootLen)` and the node list in row order
//!   (`MrkNode.hashed`/`.promoted`, `Extract/SmallViews.lean:126`).
//! * `sort` input: the sorted id list `S : List (Nat × List Nat)` consumed by
//!   `SortGeneral.trace` — receipt index and 32 id bytes, ascending.

use serde::Deserialize;

use crate::near::ids::{K_LEAF, K_MRK};
use crate::near::info::inv_p;
use crate::near::small::{MRK_WIDTH, SORT_WIDTH, mrk_shape};

use super::Tab;

const MRK_LOG: usize = 19;
const SORT_LOG: usize = 18;

fn msg_id(kind: usize, idx: usize) -> u64 {
    (kind + 16 * idx) as u64
}
fn b(x: bool) -> u64 {
    x as u64
}
fn get(xs: &[u64], i: usize) -> u64 {
    xs.get(i).copied().unwrap_or(0)
}

// ---------------------------------------------------------------------------
// mrk columns (`ZkFormal.Near.Mrk`)
// ---------------------------------------------------------------------------

mod mc {
    pub const RT: usize = 0;
    pub const SG: usize = 1;
    pub const PR: usize = 2;
    pub const PW: usize = 3;
    pub const WN: usize = 4;
    pub const WF: usize = 5;
    pub const WL: usize = 6;
    pub const SF: usize = 7;
    pub const SL: usize = 8;
    pub const Q: usize = 9;
    pub const J: usize = 10;
    pub const I: usize = 11;
    pub const SP: usize = 12;
    pub const S: usize = 13;
    pub const ODD: usize = 14;
    pub const LIL: usize = 15;
    pub const TOP: usize = 16;
    pub const INV: usize = 17;
    pub const CID: usize = 18;
    pub const CLEN: usize = 19;
    pub const MJ: usize = 20;
    pub const MI: usize = 21;
    pub const OID: usize = 22;
    pub const OLEN: usize = 23;
    pub const GM: usize = 24;
    pub const GO: usize = 25;
    pub const REG: usize = 26;
}

/// A merkle node: SHA message id, length, digest (`Render/Mrk.lean:18`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, serde::Serialize)]
pub struct MNode {
    pub id: u64,
    pub len: u64,
    #[serde(default)]
    pub dig: Vec<u64>,
}

/// `MrkNode` (`Extract/SmallViews.lean:126`): the child reference and, for a
/// hashed node, both 32-byte windows.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, serde::Serialize)]
pub enum MrkNode {
    #[serde(rename = "hashed")]
    Hashed {
        #[serde(rename = "lId")]
        l_id: u64,
        #[serde(rename = "lLen")]
        l_len: u64,
        l: Vec<u64>,
        #[serde(rename = "rId")]
        r_id: u64,
        #[serde(rename = "rLen")]
        r_len: u64,
        r: Vec<u64>,
    },
    #[serde(rename = "promoted")]
    Promoted {
        #[serde(rename = "cId")]
        c_id: u64,
        #[serde(rename = "cLen")]
        c_len: u64,
    },
}

/// `MrkV` (`Extract/SmallViews.lean:133`): the number of leaves, the root
/// reference `(J, Id, len)` and the nodes in table order (levels `1, …`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct MrkV {
    pub n: u64,
    #[serde(rename = "J", default)]
    pub j: u64,
    #[serde(rename = "rootId", default)]
    pub root_id: u64,
    #[serde(rename = "rootLen", default)]
    pub root_len: u64,
    #[serde(default)]
    pub nodes: Vec<MrkNode>,
}

/// `size n j` (`Render/Mrk.lean:28`).
fn msize(n: u64, j: u64) -> u64 {
    (0..j).fold(n, |s, _| s.div_ceil(2))
}
/// `qBase n j` (`Render/Mrk.lean:32`).
fn qbase(n: u64, j: u64) -> u64 {
    if j < 2 {
        0
    } else {
        qbase(n, j - 1) + msize(n, j - 2) / 2
    }
}

/// `topJ n`: the first level of size 1 (`Render/Mrk.lean:50`).
fn top_j(n: u64) -> u64 {
    mrk_shape(n as usize)
        .last()
        .map(|x| x.0 as u64)
        .unwrap_or(1)
}

/// `MrkGen.nodeCell` (`Render/Mrk.lean:57`) of the `k`-th node row record,
/// where `k` indexes `MrkGen.recs n` (a hashed node spans 64 rows).
fn node_cell(n: u64, nd: &MrkNode, j: u64, i: u64, p: u64) -> Vec<u64> {
    let sp = msize(n, j - 1);
    let s = msize(n, j);
    let q = qbase(n, j) + i;
    let mut row = vec![0u64; MRK_WIDTH];
    row[mc::Q] = q;
    row[mc::J] = j;
    row[mc::I] = i;
    row[mc::SP] = sp;
    row[mc::S] = s;
    row[mc::ODD] = sp % 2;
    row[mc::LIL] = b(i + 1 == s);
    row[mc::TOP] = b(s == 1);
    row[mc::INV] = if s == 1 { 0 } else { inv_p(s - 1) };
    row[mc::MJ] = j - 1;
    match nd {
        MrkNode::Hashed {
            l_id,
            l_len,
            l,
            r_id,
            r_len,
            r,
        } => {
            let (cid, clen, dig) = if p / 32 == 0 {
                (*l_id, *l_len, l)
            } else {
                (*r_id, *r_len, r)
            };
            row[mc::SG] = 1;
            row[mc::PW] = p % 32;
            row[mc::WN] = p / 32;
            row[mc::WF] = b(p % 32 == 0);
            row[mc::WL] = b(p % 32 == 31);
            row[mc::SF] = b(p == 0);
            row[mc::SL] = b(p == 63);
            row[mc::CID] = cid;
            row[mc::CLEN] = clen;
            row[mc::MI] = 2 * i + p / 32;
            row[mc::GM] = b(p % 32 == 0);
            row[mc::GO] = b(p == 0);
            row[mc::OID] = if p == 0 { msg_id(K_MRK, q as usize) } else { 0 };
            row[mc::OLEN] = if p == 0 { 64 } else { 0 };
            for x in 0..32 {
                row[mc::REG + x] = get(dig, p as usize % 32 + x);
            }
        }
        MrkNode::Promoted { c_id, c_len } => {
            row[mc::PR] = 1;
            row[mc::CID] = *c_id;
            row[mc::CLEN] = *c_len;
            row[mc::MI] = 2 * i;
            row[mc::GM] = 1;
            row[mc::GO] = 1;
            row[mc::OID] = *c_id;
            row[mc::OLEN] = *c_len;
        }
    }
    row
}

/// `MrkGen.rootCell` (`Render/Mrk.lean:93`).
fn root_cell(n: u64, v: &MrkV) -> Vec<u64> {
    let mut row = vec![0u64; MRK_WIDTH];
    row[mc::RT] = 1;
    row[mc::GM] = 1;
    row[mc::MJ] = top_j(n);
    row[mc::CID] = v.root_id;
    row[mc::CLEN] = v.root_len;
    row
}

/// Row records `(j, i, hashed, p)` (`MrkGen.recs`, `Render/Mrk.lean:53`).
#[cfg(test)]
fn mrk_recs(n: u64) -> Vec<(u64, u64, bool, u64)> {
    let mut out = vec![];
    for (j, i, h) in mrk_shape(n as usize) {
        let (j, i) = (j as u64, i as u64);
        if h {
            out.extend((0..64).map(|p| (j, i, true, p)));
        } else {
            out.push((j, i, false, 0));
        }
    }
    out
}

/// `MrkGen.cell` over the whole `2^19` table (`MerkleRender.trace`).
///
/// Row 0 is the root row; then the node rows in `MrkGen.recs` order (a hashed
/// node spans 64 rows, a promoted node one), then zero padding.  `v.nodes` is
/// in `mrkShape` order, so `shape[k]`'s node is `v.nodes[k]`.
pub fn mrk_aligned(v: &MrkV) -> Tab {
    let n = v.n;
    let mut t = Tab::zero(MRK_LOG, MRK_WIDTH);
    let h = t.height();
    if h == 0 {
        return t;
    }
    let root = root_cell(n, v);
    for (c, x) in root.into_iter().enumerate() {
        t.set(0, c, x);
    }
    let mut q = 1usize;
    for (k, &(j, i, hashed)) in mrk_shape(n as usize).iter().enumerate() {
        let nd = match v.nodes.get(k) {
            Some(nd) => nd,
            None => break,
        };
        let (j, i) = (j as u64, i as u64);
        let rows = if hashed { 64u64 } else { 1 };
        for p in 0..rows {
            if q >= h {
                break;
            }
            let row = node_cell(n, nd, j, i, p);
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            q += 1;
        }
    }
    t
}

/// Parse `json` as a [`MrkV`] and render the `mrk` trace.
pub fn render_mrk(json: &str) -> Result<Tab, String> {
    let v: MrkV = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(mrk_aligned(&v))
}

// ---------------------------------------------------------------------------
// sort (`ZkFormal.Near.Sort`, `Render/Sort.lean`)
// ---------------------------------------------------------------------------

/// Compare little-endian naturals (`leVal`, `Render/Sort.lean:20`).
fn le_cmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    let n = a.len().max(b.len());
    for j in (0..n).rev() {
        let (x, y) = (get(a, j), get(b, j));
        if x != y {
            return x.cmp(&y);
        }
    }
    std::cmp::Ordering::Equal
}

/// `x − y − 1` (truncated at 0) of little-endian naturals, as bytes.
fn sub1(x: &[u64], y: &[u64]) -> Vec<u64> {
    let n = x.len().max(y.len()) + 1;
    let mut out = vec![0u64; n];
    let mut br: i64 = 1;
    for j in 0..n {
        let t = get(x, j) as i64 - get(y, j) as i64 - br;
        if t < 0 {
            out[j] = (t + 256) as u64;
            br = 1;
        } else {
            out[j] = t as u64;
            br = 0;
        }
    }
    if br != 0 { vec![0u64; n] } else { out }
}

/// `SortGen.cell S H q col` (`Render/Sort.lean:68`) with `H = 2^18`.
fn sort_cell(
    s: &[(u64, Vec<u64>)],
    h: usize,
    diffs: &[Vec<u64>],
    carries: &[Vec<u64>],
    q: usize,
    col: usize,
) -> u64 {
    let ns = s.len();
    let id_of = |t: usize| -> &[u64] { s.get(t).map(|x| x.1.as_slice()).unwrap_or(&[]) };
    let bb_at = |q: usize| -> u64 {
        if q < 32 * ns {
            get(id_of(q / 32), q % 32)
        } else {
            0
        }
    };
    if col >= 17 {
        return if col < 49 {
            let src = (q + 2 * h).saturating_sub(1).saturating_sub(col - 17) % h;
            bb_at(src)
        } else {
            0
        };
    }
    if q >= 32 * ns {
        return 0;
    }
    let t = q / 32;
    let l = q % 32;
    match col {
        0 => 1,
        1 => b(l == 0),
        2 => b(l == 31),
        3 => b(t == 0),
        4 => s[t].0,
        5 => l as u64,
        6 => bb_at(q),
        7 => carries[t][l],
        8 => carries[t][l + 1],
        _ => {
            let j = col - 9;
            if j < 8 {
                (get(&diffs[t], l) >> j) & 1
            } else {
                0
            }
        }
    }
}

/// `SortGen.cell`'s carries (`Render/Sort.lean:49`).
fn sort_diffs_carries(s: &[(u64, Vec<u64>)]) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let ns = s.len();
    let id_of = |t: usize| -> &[u64] { s.get(t).map(|x| x.1.as_slice()).unwrap_or(&[]) };
    let diffs: Vec<Vec<u64>> = (0..ns)
        .map(|t| {
            if t == 0 {
                vec![]
            } else {
                sub1(id_of(t), id_of(t - 1))
            }
        })
        .collect();
    let carries: Vec<Vec<u64>> = (0..ns)
        .map(|t| {
            (0..=33)
                .map(|ii| {
                    if t == 0 {
                        b(ii == 0)
                    } else {
                        let (x, y) = (id_of(t - 1), &diffs[t]);
                        let mut c = 1u64;
                        for j in 0..ii {
                            c = (get(x, j) + get(y, j) + c) / 256;
                        }
                        c
                    }
                })
                .collect()
        })
        .collect();
    (diffs, carries)
}

/// Honest `sort` trace at `2^18` rows (`SortGeneral.trace`).
///
/// `s` is the sorted id list; entries must be ascending (little-endian) and
/// each id exactly 32 bytes for the table's constraints to hold.
pub fn sort_aligned(s: &[(u64, Vec<u64>)]) -> Tab {
    let h = 1usize << SORT_LOG;
    let (diffs, carries) = sort_diffs_carries(s);
    let mut t = Tab::zero(SORT_LOG, SORT_WIDTH);
    for q in 0..h {
        for c in 0..SORT_WIDTH {
            let x = sort_cell(s, h, &diffs, &carries, q, c);
            t.set(q, c, x);
        }
    }
    t
}

/// Parse `json` as the sorted id list and render the `sort` trace.
pub fn render_sort(json: &str) -> Result<Tab, String> {
    let s: Vec<(u64, Vec<u64>)> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(sort_aligned(&s))
}

// ---------------------------------------------------------------------------
// Samplers (used by `npudr v3sample` and the tests)
// ---------------------------------------------------------------------------

use super::sample::Rng;

/// The `MrkGen.levels I` (`Render/Mrk.lean:39`) of `n` leaves with
/// pseudo-random 32-byte digests: level `0` the leaves, level `j` the level-`j`
/// internal nodes (a lone node is promoted unchanged).  The digest data is
/// arbitrary (authenticated by the SHA bus); only its 32-byte width enters the
/// local constraints.
fn sample_levels(r: &mut Rng, n: u64) -> Vec<Vec<MNode>> {
    let mut lv: Vec<Vec<MNode>> = vec![
        (0..n)
            .map(|i| MNode {
                id: msg_id(K_LEAF, i as usize),
                len: 68,
                dig: r.bytes(32),
            })
            .collect(),
    ];
    // `Render/Mrk.lean:39`/`Render/Mrk.lean:107` build the levels `0 … n+1`, so
    // `topJ n ≤ n+1` always resolves.
    for j in 1..=n + 1 {
        let prev = lv.last().unwrap();
        let next: Vec<MNode> = (0..prev.len().div_ceil(2))
            .map(|i| {
                if 2 * i + 1 < prev.len() {
                    MNode {
                        id: msg_id(K_MRK, qbase(n, j) as usize + i),
                        len: 64,
                        dig: r.bytes(32),
                    }
                } else {
                    prev[2 * i].clone()
                }
            })
            .collect();
        lv.push(next);
    }
    lv
}

/// Assemble a `MrkV` from concrete levels (`MrkGen.levels I` in table order):
/// the root reference `(J, Id, len)` and the node list generated by `mrkShape`.
pub fn mrk_from_levels(n: u64, lv: &[Vec<MNode>]) -> MrkV {
    let nodes: Vec<MrkNode> = mrk_shape(n as usize)
        .into_iter()
        .map(|(j, i, h)| {
            let child = |k: usize| -> MNode {
                lv.get(j - 1)
                    .and_then(|l| l.get(k))
                    .cloned()
                    .unwrap_or_default()
            };
            if h {
                let l = child(2 * i);
                let r2 = child(2 * i + 1);
                MrkNode::Hashed {
                    l_id: l.id,
                    l_len: l.len,
                    l: l.dig,
                    r_id: r2.id,
                    r_len: r2.len,
                    r: r2.dig,
                }
            } else {
                let l = child(2 * i);
                MrkNode::Promoted {
                    c_id: l.id,
                    c_len: l.len,
                }
            }
        })
        .collect();
    let root = lv
        .get(top_j(n) as usize)
        .and_then(|l| l.first())
        .cloned()
        .unwrap_or_default();
    MrkV {
        n,
        j: top_j(n),
        root_id: root.id,
        root_len: root.len,
        nodes,
    }
}

/// `n ≥ 1` honest `MrkV` entries (random 32-byte windows).
pub fn mrk(r: &mut Rng, n: u64) -> MrkV {
    let n = n.max(1);
    let lv = sample_levels(r, n);
    mrk_from_levels(n, &lv)
}

/// `k ≥ 1` sorted 32-byte ids (`(receipt index, id)`), ascending.
pub fn sort(r: &mut Rng, k: usize) -> Vec<(u64, Vec<u64>)> {
    let k = k.max(1);
    let mut v: Vec<(u64, Vec<u64>)> = (0..k)
        .map(|i| {
            let mut b = r.bytes(30);
            b.push(r.below(256));
            b.push(i as u64 % 256);
            (i as u64, b)
        })
        .collect();
    v.sort_by(|a, b| le_cmp(&a.1, &b.1));
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::F;
    use p3_field::PrimeCharacteristicRing;

    fn air() -> crate::air::Air {
        let air_json = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../conformance/out-v2/nearAirV3.json"
        );
        let txt = std::fs::read_to_string(air_json).expect("nearAirV3.json");
        crate::air::Air::from_json(&txt).expect("parse air")
    }

    /// The honest public vector for table 23: `PH_N` (30..34) the little-endian
    /// `n`.  The local constraints only read `PH_N` (`nPubE`); the `PH_OUT`
    /// digest receive is a bus interaction, not a local constraint.
    fn mrk_pubs(air: &crate::air::Air, n: u64) -> Vec<F> {
        let mut p = vec![F::ZERO; air.num_pub];
        for (i, b) in crate::near::spec::le_n(4, n as u128).iter().enumerate() {
            p[30 + i] = F::from_u64(*b as u64);
        }
        p
    }

    #[test]
    fn mrk_matches_v1_cells() {
        // The v3 `mrk_aligned` reproduces `MrkGen.cell` row for row: rebuild the
        // levels and compare against `MrkGen.nodeCell` semantics via the shape.
        let mut r = Rng::new(7);
        for n in [1u64, 2, 3, 5, 7, 8, 9, 16, 17] {
            let v = mrk(&mut r, n);
            let t = mrk_aligned(&v);
            assert_eq!(t.log, 19);
            assert_eq!(t.width, MRK_WIDTH);
            let recs = mrk_recs(n);
            // row 0 is the root row
            assert_eq!(t.cells[mc::RT], 1);
            assert_eq!(t.cells[mc::CID] as u64, v.root_id);
            assert_eq!(t.cells[mc::CLEN] as u64, v.root_len);
            // a hashed node's 64 rows carry the two windows
            for (q1, &(j, i, h, p)) in recs.iter().enumerate() {
                let q = q1 + 1;
                let base = q * MRK_WIDTH;
                assert_eq!(t.cells[base + mc::Q] as u64, qbase(n, j) + i, "n={n} q={q}");
                if h {
                    assert_eq!(t.cells[base + mc::SG], 1);
                    assert_eq!(t.cells[base + mc::SL] as u64, b(p == 63));
                } else {
                    assert_eq!(t.cells[base + mc::PR], 1);
                    assert_eq!(p, 0);
                }
            }
            // one all-zero padding row after the records
            let pad = (recs.len() + 1) * MRK_WIDTH;
            for c in 0..MRK_WIDTH {
                assert_eq!(t.cells[pad + c], 0, "n={n} col={c}");
            }
        }
    }

    #[test]
    fn mrk_constraints_hold_with_honest_pubs() {
        let air = air();
        let t = &air.tables[23];
        let mut r = Rng::new(3);
        for n in [1u64, 2, 3, 5, 7, 8, 16] {
            let v = mrk(&mut r, n);
            // exercise the JSON `render_mrk` entry point
            let j = serde_json::to_string(&v).unwrap();
            let tab = render_mrk(&j).unwrap();
            let pubs = mrk_pubs(&air, n);
            let bad = crate::check::failing_constraints(t, &tab.to_matrix(), &pubs, 40);
            assert!(bad.is_empty(), "n={n} failing: {bad:?}");
        }
    }

    #[test]
    fn sort_matches_v1_cells() {
        let mut r = Rng::new(5);
        for k in [1usize, 2, 5, 37] {
            let s = sort(&mut r, k);
            let t = sort_aligned(&s);
            assert_eq!(t.log, 18);
            assert_eq!(t.width, SORT_WIDTH);
            // first segment: act, sf, ft, i, cin
            assert_eq!(t.cells[0], 1);
            assert_eq!(t.cells[1], 1);
            assert_eq!(t.cells[3], 1);
            assert_eq!(t.cells[5], 0);
            assert_eq!(t.cells[7], 1);
            // a padding row is inactive: columns 0..9 (except the delay line
            // 17..49, which follows `bbAt` as in v1) are zero
            let pad = (32 * k) * SORT_WIDTH;
            assert_eq!(t.cells[pad], 0, "k={k}");
            for c in 0..17 {
                assert_eq!(t.cells[pad + c], 0, "k={k} col={c}");
            }
        }
    }

    /// Differential against the real v1 `sort` generator on a public fixture:
    /// `sort_aligned (sorted_ids i)` reproduces `small::sort_rows_all i` on the
    /// active rows (the v3 trace is the v1 rows plus padding to `2^18`).
    #[test]
    fn sort_matches_v1_generator_on_fixture() {
        use crate::near::{ext, info, spec};
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../oracle/fixtures/public/cases/example-tierA");
        let (Ok(req), Ok(wit)) = (
            std::fs::read(dir.join("request.bin")),
            std::fs::read(dir.join("witness.bin")),
        ) else {
            return;
        };
        let inp = spec::load_inputs(&req, &wit).unwrap();
        let e = ext::ext_of(&inp.claim, &inp.witness);
        let i = info::mk_info(&inp.claim, &e);
        let v1 = crate::near::small::sort_rows_all(&i);
        let s = crate::near::small::sorted_ids(&i);
        let s: Vec<(u64, Vec<u64>)> = s
            .into_iter()
            .map(|(r, b)| (r as u64, b.into_iter().map(|x| x as u64).collect()))
            .collect();
        let t = sort_aligned(&s);
        assert_eq!(t.log, 18);
        let active = 32 * s.len();
        assert!(active <= t.height());
        // Columns 0..17 (the active-row cells) are functions of `S` alone; the
        // delay line 17..49 depends on the table height `H` (`bbAt ((q + 2H −
        // 1 − j) mod H)`), which is v1's `sortH` there but the fixed `2^18` here.
        for q in 0..active {
            for c in 0..17 {
                assert_eq!(
                    t.cells[q * SORT_WIDTH + c] as u64,
                    v1[q][c] as u64,
                    "fixture v1 mismatch q={q} c={c}"
                );
            }
        }
    }

    /// Differential against the real v1 `mrk` generator on a public fixture:
    /// `mrk_aligned` reproduces `small::mrk_rows_all` on the active rows (the v3
    /// trace is the v1 rows padded to `2^19`).  `mrk`'s cells do not depend on
    /// the height, so every column is compared.
    #[test]
    fn mrk_matches_v1_generator_on_fixture() {
        use crate::near::{ext, info, spec};
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../oracle/fixtures/public/cases/example-tierA");
        let (Ok(req), Ok(wit)) = (
            std::fs::read(dir.join("request.bin")),
            std::fs::read(dir.join("witness.bin")),
        ) else {
            return;
        };
        let inp = spec::load_inputs(&req, &wit).unwrap();
        let e = ext::ext_of(&inp.claim, &inp.witness);
        let i = info::mk_info(&inp.claim, &e);
        let v1 = crate::near::small::mrk_rows_all(&i);
        let lv = mrk_levels(&i);
        let v = mrk_from_levels(i.n_rcpt() as u64, &lv);
        let t = mrk_aligned(&v);
        assert_eq!(t.log, 19);
        let active = v1.len();
        assert!(active <= t.height());
        for q in 0..active {
            for c in 0..MRK_WIDTH {
                assert_eq!(
                    t.cells[q * MRK_WIDTH + c] as u64,
                    v1[q][c] as u64,
                    "fixture v1 mrk mismatch q={q} c={c}"
                );
            }
        }
    }

    /// `mrk_levels I` (`Render/Mrk.lean:39`): the concrete level data of an
    /// `Info` — the real leaf digests and the internal SHA hashes.
    fn mrk_levels(i: &crate::near::info::Info) -> Vec<Vec<MNode>> {
        use crate::near::sim::leaf_bytes;
        let n = i.n_rcpt();
        let mut lv: Vec<Vec<MNode>> = vec![
            (0..n)
                .map(|r| MNode {
                    id: msg_id(K_LEAF, r),
                    len: 68,
                    dig: crate::near::info::sha_n(&leaf_bytes(i, r))
                        .into_iter()
                        .map(|x| x as u64)
                        .collect(),
                })
                .collect(),
        ];
        let mut j = 0u64;
        while lv.last().unwrap().len() > 1 {
            let prev = lv.last().unwrap().clone();
            let next: Vec<MNode> = (0..prev.len().div_ceil(2))
                .map(|k| {
                    if 2 * k + 1 < prev.len() {
                        let mut b: Vec<u8> = prev[2 * k].dig.iter().map(|&x| x as u8).collect();
                        b.extend(prev[2 * k + 1].dig.iter().map(|&x| x as u8));
                        MNode {
                            id: msg_id(K_MRK, qbase(n as u64, j + 1) as usize + k),
                            len: 64,
                            dig: crate::near::info::sha_n(&b)
                                .into_iter()
                                .map(|x| x as u64)
                                .collect(),
                        }
                    } else {
                        prev[2 * k].clone()
                    }
                })
                .collect();
            lv.push(next);
            j += 1;
        }
        lv
    }

    #[test]
    fn sort_constraints_hold() {
        let air = air();
        let t = &air.tables[24];
        let mut r = Rng::new(9);
        for k in [1usize, 2, 5, 37] {
            let s = sort(&mut r, k);
            // exercise the JSON `render_sort` entry point
            let j = serde_json::to_string(&s).unwrap();
            let tab = render_sort(&j).unwrap();
            let pubs = vec![F::ZERO; air.num_pub];
            let bad = crate::check::failing_constraints(t, &tab.to_matrix(), &pubs, 40);
            assert!(bad.is_empty(), "k={k} failing: {bad:?}");
        }
    }
}
