//! Streaming MMCS commitment and opening for the low-memory prover.
//!
//! Same commitment as [`crate::mmcs`] (bit for bit): level 0
//! `WH(LEAF, rows_0(j))`, level `k ≥ 1` `WH(NODE, u8 k ‖ L ‖ R ‖ rows_k(j))`.
//! Rows are never materialized for a whole matrix: level-0 positions are
//! processed in groups, each matrix's columns in chunks (coefficients
//! recomputed per group), evaluated on the group's position range with
//! [`eval_range`] and streamed into a [`WhStream`].
//!
//! Levels below `KEEP` are not stored; an opening recomputes the
//! `2^KEEP`-leaf subtree around every queried position from the matrix rows
//! on that range.

use std::collections::HashMap;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use crate::field::F;
use crate::hash::{Digest64, TAG_LEAF, TAG_NODE, wh};
use crate::lmsrc::Src;
use crate::lowmem::{Dft, WhStream, eval_range};
use crate::mmcs::{Opening, index_sets};

/// Levels `< keep` are recomputed at opening time: `KEEP` normally,
/// `KEEP_LARGE` for traces under memory pressure (4× smaller stored trees,
/// costlier openings).
pub const KEEP: usize = 4;
pub const KEEP_LARGE: usize = 6;

/// A committed matrix: its source, LDE log, coset shift and tree class
/// (`l0 − lde log`).
pub struct CMat<'a> {
    pub src: &'a Src<'a>,
    pub lde: usize,
    pub shift: F,
    pub class: usize,
}

pub struct LTree {
    pub l0: usize,
    /// `levels[k]` for `k ≥ KEEP` (or every level when the tree is small)
    pub levels: Vec<Option<Vec<Digest64>>>,
}

impl LTree {
    pub fn root(&self) -> Digest64 {
        self.levels[self.l0].as_ref().unwrap()[0]
    }
}

/// Hash level `k` on the position ranges `ranges` (`(p0, len)` at level `k`),
/// given the children digests `prev` (concatenated in range order, `2·Σlen`
/// entries) for `k ≥ 1`. Returns the digests in range order.
pub fn hash_ranges(
    dft: &Dft,
    mats: &[CMat],
    k: usize,
    ranges: &[(usize, usize)],
    prev: Option<&[Digest64]>,
    chunk: usize,
) -> Vec<Digest64> {
    let n: usize = ranges.iter().map(|r| r.1).sum();
    let ms: Vec<&CMat> = mats.iter().filter(|m| m.class == k).collect();
    if ms.is_empty() {
        let p = prev.expect("level 0 needs a matrix");
        use rayon::prelude::*;
        return (0..n)
            .into_par_iter()
            .with_min_len(1024)
            .map(|i| wh(TAG_NODE, &[&[k as u8], &p[2 * i], &p[2 * i + 1]]))
            .collect();
    }
    let mut st = WhStream::new(n, if k == 0 { TAG_LEAF } else { TAG_NODE });
    if let Some(p) = prev {
        st.feed(129, |i, out| {
            out.push(k as u8);
            out.extend_from_slice(&p[2 * i]);
            out.extend_from_slice(&p[2 * i + 1]);
        });
    }
    for m in &ms {
        for (c0, c1) in m.src.chunks(chunk) {
            let co = m.src.coeffs(dft, c0, c1);
            let w = c1 - c0;
            let mut off = 0;
            for &(p0, len) in ranges {
                let t = co.height();
                // evaluate block by block to bound the buffer
                let step = len.min(t);
                for b in 0..len / step {
                    let e = eval_range(dft, &co, m.lde, m.shift, p0 + b * step, step, None);
                    st.feed_at(
                        off + b * step,
                        4 * w,
                        |i, out| {
                            for x in &e.values[i * w..(i + 1) * w] {
                                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
                            }
                        },
                        step,
                    );
                }
                off += len;
            }
            st.commit_len(4 * w);
        }
    }
    st.finish()
}

// ---------------------------------------------------------------------------
// Level 0 of large class-0 matrices: whole LDE blocks, 64-byte aligned feeds
// ---------------------------------------------------------------------------

/// Smallest class-0 height (log) for which level 0 is hashed block-wise.
pub const FAST_MIN_LOG: usize = 10;

/// Leaf-hash states of `n` messages `WH(tag, body)`: the two SHA-256 states
/// of each message in native-endian words, in the 64 bytes of its digest
/// slot (finished in place into the big-endian digest).
struct LeafStates;

const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

impl LeafStates {
    fn init(n: usize) -> Vec<Digest64> {
        use rayon::prelude::*;
        let mut d = [0u8; 64];
        for (k, w) in H0.iter().chain(H0.iter()).enumerate() {
            d[4 * k..4 * k + 4].copy_from_slice(&w.to_ne_bytes());
        }
        let mut v: Vec<Digest64> = Vec::with_capacity(n);
        v.par_extend((0..n).into_par_iter().with_min_len(1 << 14).map(|_| d));
        v
    }
    #[inline(always)]
    fn load(d: &Digest64) -> [u32; 16] {
        std::array::from_fn(|k| u32::from_ne_bytes(d[4 * k..4 * k + 4].try_into().unwrap()))
    }
    #[inline(always)]
    fn store(d: &mut Digest64, s: &[u32; 16]) {
        for (k, w) in s.iter().enumerate() {
            d[4 * k..4 * k + 4].copy_from_slice(&w.to_ne_bytes());
        }
    }
    /// Absorb `data` into one message whose stream holds `done` bytes so far
    /// (`done = 0`: nothing yet, the 12-byte prefix `RO_TAG ‖ tag ‖ variant`
    /// comes first; otherwise `done` is a multiple of 64). With `last`, pad
    /// and write the digest; otherwise `done + data` (+ prefix) must end on a
    /// block boundary. Blocks after the first are compressed into both states
    /// at once ([`crate::sha2x::compress_pair`]).
    #[inline]
    fn absorb(d: &mut Digest64, tag: u8, done: u64, data: &[u8], last: bool) {
        let s = Self::load(d);
        let mut sa: [u32; 8] = s[..8].try_into().unwrap();
        let mut sb: [u32; 8] = s[8..].try_into().unwrap();
        let total = if done == 0 { 12 } else { done } + data.len() as u64;
        let mut off = 0;
        if done == 0 {
            // block 0: prefix (with the variant byte) and the first 52 bytes
            let mut b0 = [0u8; 64];
            b0[..10].copy_from_slice(crate::hash::RO_TAG);
            b0[10] = tag;
            if data.len() >= 52 {
                b0[12..].copy_from_slice(&data[..52]);
                Self::compress_first(&mut sa, &mut sb, &b0);
                off = 52;
            } else {
                // short message (with `last`): prefix ‖ data ‖ padding
                debug_assert!(last, "unaligned leaf feed");
                let mut m = b0[..12].to_vec();
                m.extend_from_slice(data);
                Self::finish_from(&mut sa, &mut sb, &m, total, true, d);
                return;
            }
        }
        let rest = &data[off..];
        let nfull = rest.len() / 64;
        // SAFETY: `[u8; 64]` has alignment 1; `nfull · 64 ≤ rest.len()`.
        let blocks: &[[u8; 64]] =
            unsafe { std::slice::from_raw_parts(rest.as_ptr() as *const [u8; 64], nfull) };
        crate::sha2x::compress_pair(&mut sa, &mut sb, blocks);
        let tail = &rest[nfull * 64..];
        if !last {
            debug_assert!(tail.is_empty(), "unaligned leaf feed");
            let mut s = [0u32; 16];
            s[..8].copy_from_slice(&sa);
            s[8..].copy_from_slice(&sb);
            Self::store(d, &s);
            return;
        }
        Self::finish_from(&mut sa, &mut sb, tail, total, false, d);
    }

    /// Block 0 of both messages (variant byte 1 resp. 2 at offset 11).
    #[inline(always)]
    fn compress_first(sa: &mut [u32; 8], sb: &mut [u32; 8], b0: &[u8; 64]) {
        use sha2::digest::generic_array::GenericArray;
        let mut blk = *b0;
        blk[11] = 1;
        sha2::compress256(sa, &[*GenericArray::from_slice(&blk)]);
        blk[11] = 2;
        sha2::compress256(sb, &[*GenericArray::from_slice(&blk)]);
    }

    /// Pad the remaining bytes `tail` (< 64, or the whole short message
    /// including block 0 when `first`) and write the digest into `d`.
    fn finish_from(
        sa: &mut [u32; 8],
        sb: &mut [u32; 8],
        tail: &[u8],
        total: u64,
        first: bool,
        d: &mut Digest64,
    ) {
        let mut m = tail.to_vec();
        m.push(0x80);
        while m.len() % 64 != 56 {
            m.push(0);
        }
        m.extend_from_slice(&(total * 8).to_be_bytes());
        // SAFETY: as above (`m.len()` is a multiple of 64).
        let blocks: &[[u8; 64]] =
            unsafe { std::slice::from_raw_parts(m.as_ptr() as *const [u8; 64], m.len() / 64) };
        let mut rest = blocks;
        if first {
            Self::compress_first(sa, sb, &blocks[0]);
            rest = &blocks[1..];
        }
        crate::sha2x::compress_pair(sa, sb, rest);
        for (k, w) in sa.iter().chain(sb.iter()).enumerate() {
            d[4 * k..4 * k + 4].copy_from_slice(&w.to_be_bytes());
        }
    }
}

/// Column chunks of the concatenated class-0 row (`widths` per matrix):
/// segments `(matrix, c0, c1)`; every chunk but the last ends on a 64-byte
/// boundary of the leaf message (12-byte prefix + 4 bytes per column).
fn plan_chunks(widths: &[usize], cw: usize) -> Vec<Vec<(usize, usize, usize)>> {
    let total: usize = widths.iter().sum();
    let k = (cw / 16).max(1);
    let mut sizes = vec![];
    let mut done = 0;
    while done < total {
        let want = if done == 0 { 13 + 16 * (k - 1) } else { 16 * k };
        let n = want.min(total - done);
        sizes.push(n);
        done += n;
    }
    let mut out = vec![];
    let (mut mi, mut c) = (0usize, 0usize);
    for n in sizes {
        let mut segs = vec![];
        let mut left = n;
        while left > 0 {
            while widths[mi] == c {
                mi += 1;
                c = 0;
            }
            let take = left.min(widths[mi] - c);
            segs.push((mi, c, c + take));
            c += take;
            left -= take;
        }
        out.push(segs);
    }
    out
}

/// Whether level 0 of `mats` can be hashed block-wise for groups of `s`
/// positions.
fn fast_level0(mats: &[CMat], s: usize) -> bool {
    let ms: Vec<&CMat> = mats.iter().filter(|m| m.class == 0).collect();
    if ms.is_empty() || ms.iter().all(|m| m.src.width() == 0) {
        return false;
    }
    let lh = ms[0].src.log_h();
    lh >= FAST_MIN_LOG && ms.iter().all(|m| m.src.log_h() == lh) && s % (1usize << lh) == 0
}

/// Level-0 digests of positions `g0 .. g0 + s` (whole LDE blocks of the
/// class-0 matrices): each column chunk's coefficients once, one coset DFT
/// per block, rows streamed into the leaf states.
fn hash_level0_blocks(dft: &Dft, mats: &[CMat], g0: usize, s: usize, cw: usize) -> Vec<Digest64> {
    use rayon::prelude::*;
    let ms: Vec<&CMat> = mats.iter().filter(|m| m.class == 0).collect();
    let n = ms[0].src.log_h();
    let t = 1usize << n;
    let cd = crate::lde::coset_dft(n);
    let widths: Vec<usize> = ms.iter().map(|m| m.src.width()).collect();
    let plan = plan_chunks(&widths, cw);
    let mut st = LeafStates::init(s);
    let mut done = 0u64;
    let mut evs: Vec<Vec<F>> = vec![];
    for (ci, segs) in plan.iter().enumerate() {
        let last = ci + 1 == plan.len();
        let cos: Vec<RowMajorMatrix<F>> = segs
            .iter()
            .map(|&(mi, c0, c1)| ms[mi].src.coeffs(dft, c0, c1))
            .collect();
        let sw: Vec<usize> = segs.iter().map(|&(_, c0, c1)| c1 - c0).collect();
        let nbytes: usize = 4 * sw.iter().sum::<usize>();
        evs.resize_with(segs.len(), Vec::new);
        for (e, &w) in evs.iter_mut().zip(&sw) {
            if e.len() != t * w {
                // fully overwritten by the coset DFT
                *e = crate::bufpool::take(t * w);
            }
        }
        for b in g0 / t..(g0 + s) / t {
            for ((e, co), &(mi, _, _)) in evs.iter_mut().zip(&cos).zip(segs) {
                let m = ms[mi];
                let c = m.shift
                    * crate::field::omega(m.lde).exp_u64(crate::mmcs::rev(b, m.lde - n) as u64);
                let _t = std::time::Instant::now();
                cd.eval(&co.values, co.width(), c, e);
                crate::lowmem::prof::add(&crate::lowmem::prof::EVAL, _t);
            }
            let _t = std::time::Instant::now();
            let base = b * t - g0;
            let evr = &evs;
            st[base..base + t]
                .par_chunks_mut(1024)
                .enumerate()
                .for_each_init(
                    || Vec::with_capacity(nbytes),
                    |buf, (k, leaves)| {
                        for (i, d) in leaves.iter_mut().enumerate() {
                            let u = k * 1024 + i;
                            buf.clear();
                            for (e, &w) in evr.iter().zip(&sw) {
                                for x in &e[u * w..(u + 1) * w] {
                                    buf.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
                                }
                            }
                            LeafStates::absorb(d, TAG_LEAF, done, buf, last);
                        }
                    },
                );
            crate::lowmem::prof::add(&crate::lowmem::prof::FEED, _t);
        }
        done = if done == 0 { 12 } else { done } + nbytes as u64;
        for co in cos {
            crate::bufpool::give(co.values);
        }
    }
    for e in evs {
        crate::bufpool::give(e);
    }
    st
}

/// Commit a round. `group` = level-0 positions hashed at once.
pub fn commit(
    dft: &Dft,
    mats: &[CMat],
    l0: usize,
    group: usize,
    chunk: usize,
    keep_lvl: usize,
) -> LTree {
    let n0 = 1usize << l0;
    let s = group.min(n0);
    let ls = p3_util::log2_strict_usize(s);
    let keep = if l0 < 12 { 0 } else { keep_lvl };
    let mut levels: Vec<Option<Vec<Digest64>>> = (0..=l0)
        .map(|k| {
            if k >= keep {
                Some(Vec::with_capacity(n0 >> k))
            } else {
                None
            }
        })
        .collect();
    let fast = fast_level0(mats, s);
    for g in 0..n0 / s {
        let mut cur = if fast {
            hash_level0_blocks(dft, mats, g * s, s, chunk)
        } else {
            hash_ranges(dft, mats, 0, &[(g * s, s)], None, chunk)
        };
        if keep == 0 {
            levels[0].as_mut().unwrap().extend_from_slice(&cur);
        }
        for k in 1..=ls {
            cur = hash_ranges(dft, mats, k, &[((g * s) >> k, s >> k)], Some(&cur), chunk);
            if k >= keep {
                levels[k].as_mut().unwrap().extend_from_slice(&cur);
            }
        }
    }
    for k in ls + 1..=l0 {
        let prev = levels[k - 1].take().unwrap();
        let cur = hash_ranges(dft, mats, k, &[(0, n0 >> k)], Some(&prev), chunk);
        levels[k - 1] = Some(prev);
        levels[k] = Some(cur);
    }
    LTree { l0, levels }
}

/// Rows of every matrix at the positions of `ranges` (`(p0, len)` at the
/// matrix's level), concatenated per matrix.
fn rows_on(dft: &Dft, m: &CMat, ranges: &[(usize, usize)], chunk: usize) -> Vec<Vec<F>> {
    let w = m.src.width();
    let n: usize = ranges.iter().map(|r| r.1).sum();
    let mut out = vec![vec![F::default(); w]; n];
    for (c0, c1) in m.src.chunks(chunk) {
        let co = m.src.coeffs(dft, c0, c1);
        let cw = c1 - c0;
        // ranges grouped by length; one streaming pass per length
        let mut lens: Vec<usize> = ranges.iter().map(|r| r.1).collect();
        lens.sort_unstable();
        lens.dedup();
        let mut evs: Vec<Option<RowMajorMatrix<F>>> = ranges.iter().map(|_| None).collect();
        // Small tables: evaluating the whole coset blocks (size T) that hold
        // the ranges (~log T operations per point) is cheaper than one fold
        // over all coefficients per range (T per range)
        let t = co.height();
        let lt = p3_util::log2_strict_usize(t);
        let mut blocks: Vec<usize> = ranges
            .iter()
            .filter(|r| r.1 <= t)
            .map(|r| r.0 / t)
            .collect();
        blocks.sort_unstable();
        blocks.dedup();
        // (measured: 1.7-2.6x faster openings for T <= 2^13, where the block
        // DFTs stay in cache; 3x slower at T = 2^16 with AVX-512 folds)
        let by_block = lt <= 13
            && ranges.iter().all(|r| r.1 <= t)
            && blocks.len() * (lt / 2 + 2) < ranges.len();
        if by_block {
            for &b in &blocks {
                let ev = crate::lowmem::eval_range(dft, &co, m.lde, m.shift, b * t, t, None);
                for (i, &(p0, len)) in ranges.iter().enumerate() {
                    if p0 / t == b {
                        let u = p0 - b * t;
                        evs[i] = Some(RowMajorMatrix::new(
                            ev.values[u * cw..(u + len) * cw].to_vec(),
                            cw,
                        ));
                    }
                }
            }
        }
        for &l in lens.iter().filter(|_| !by_block) {
            let idx: Vec<usize> = (0..ranges.len()).filter(|&i| ranges[i].1 == l).collect();
            let p0s: Vec<usize> = idx.iter().map(|&i| ranges[i].0).collect();
            for (i, e) in idx.iter().zip(crate::lowmem::eval_ranges(
                dft, &co, m.lde, m.shift, &p0s, l,
            )) {
                evs[*i] = Some(e);
            }
        }
        let mut off = 0;
        for (e, &(_, len)) in evs.iter().zip(ranges) {
            let e = e.as_ref().unwrap();
            for i in 0..len {
                out[off + i][c0..c1].copy_from_slice(&e.values[i * cw..(i + 1) * cw]);
            }
            off += len;
        }
    }
    out
}

/// Open a round at level-0 query positions (same multiproof as
/// [`crate::mmcs::open`]).
pub fn open(dft: &Dft, mats: &[CMat], tree: &LTree, queries: &[usize], chunk: usize) -> Opening {
    let l0 = tree.l0;
    let keep = (0..=l0).find(|&k| tree.levels[k].is_some()).unwrap();
    let sets = index_sets(l0, queries);
    let gsz = 1usize << keep;
    // 2^keep-aligned groups of level-0 positions
    let mut groups: Vec<usize> = queries.iter().map(|&q| q / gsz).collect();
    groups.sort_unstable();
    groups.dedup();
    // rows of each matrix on its level's part of every group (or, for
    // classes ≥ keep, at the opened positions themselves)
    let mut rowmap: Vec<HashMap<usize, Vec<F>>> = vec![];
    for m in mats {
        let k = m.class;
        let ranges: Vec<(usize, usize)> = if k < keep {
            groups.iter().map(|&g| ((g * gsz) >> k, gsz >> k)).collect()
        } else {
            sets[k].iter().map(|&j| (j, 1)).collect()
        };
        let rows = rows_on(dft, m, &ranges, chunk);
        let mut map = HashMap::new();
        let mut i = 0;
        for &(p0, len) in &ranges {
            for u in 0..len {
                map.insert(p0 + u, rows[i].clone());
                i += 1;
            }
        }
        rowmap.push(map);
    }
    let row_bytes = |k: usize, j: usize| -> Vec<u8> {
        let mut b = vec![];
        for (m, map) in mats.iter().zip(&rowmap) {
            if m.class == k {
                for x in &map[&j] {
                    b.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
                }
            }
        }
        b
    };
    // recompute levels < keep inside the groups
    // (groups are independent subtrees: hashed in parallel)
    use rayon::prelude::*;
    let parts: Vec<Vec<((usize, usize), Digest64)>> = groups
        .par_iter()
        .map(|&g| {
            let mut loc: HashMap<(usize, usize), Digest64> = HashMap::new();
            for j in g * gsz..(g + 1) * gsz {
                loc.insert((0, j), wh(TAG_LEAF, &[&row_bytes(0, j)]));
            }
            for k in 1..keep {
                for j in (g * gsz) >> k..((g + 1) * gsz) >> k {
                    let (a, b) = (loc[&(k - 1, 2 * j)], loc[&(k - 1, 2 * j + 1)]);
                    loc.insert(
                        (k, j),
                        wh(TAG_NODE, &[&[k as u8], &a, &b, &row_bytes(k, j)]),
                    );
                }
            }
            loc.into_iter().collect()
        })
        .collect();
    let low: HashMap<(usize, usize), Digest64> = parts.into_iter().flatten().collect();
    let node = |k: usize, j: usize| -> Digest64 {
        match &tree.levels[k] {
            Some(l) => l[j],
            None => low[&(k, j)],
        }
    };
    let rows = mats
        .iter()
        .zip(&rowmap)
        .map(|(m, map)| {
            let mut r = vec![];
            for &j in &sets[m.class] {
                r.extend_from_slice(&map[&j]);
            }
            r
        })
        .collect();
    let mut siblings = vec![];
    for k in 1..=l0 {
        let below = &sets[k - 1];
        for &j in &sets[k] {
            for c in [2 * j, 2 * j + 1] {
                if below.binary_search(&c).is_err() {
                    siblings.push(node(k - 1, c));
                }
            }
        }
    }
    Opening { rows, siblings }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cols::TraceCols;
    use crate::field::{F, shift};
    use crate::mmcs::{self, Mat};
    use p3_dft::TwoAdicSubgroupDft;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn matches_mmcs() {
        // tables: 2^9 rows w=5 (class 0), 2^7 rows w=3 (class 2), 2^9 rows w=0
        check(
            &[(9, 5), (7, 3), (9, 0)],
            13,
            &[(1 << 13, 64), (1 << 11, 2), (1 << 12, 8)],
        );
    }

    /// Block-wise level 0 (class-0 tables of `2^FAST_MIN_LOG` rows and more):
    /// several class-0 matrices whose widths cross the 64-byte chunk
    /// boundaries, an empty one, and a smaller class.
    #[test]
    fn matches_mmcs_fast_level0() {
        let l0 = 15;
        let tabs = [(11, 5), (11, 20), (11, 0), (11, 9), (9, 3), (11, 33)];
        check(
            &tabs,
            l0,
            &[(1 << 15, 16), (1 << 14, 32), (1 << 13, 48), (1 << 11, 8)],
        );
        check(&[(11, 13)], l0, &[(1 << 15, 16)]);
        check(&[(11, 12), (10, 2)], l0, &[(1 << 15, 64), (1 << 11, 16)]);
    }

    fn check(tabs: &[(usize, usize)], l0: usize, runs: &[(usize, usize)]) {
        let dft = Dft::default();
        let mk = |lh: usize, w: usize, seed: u32| {
            TraceCols::from_rows(lh, w, |r, b| {
                for c in 0..w {
                    b[c] = (r as u32 * 7 + c as u32 * 13 + seed).wrapping_mul(2654435761u32)
                        % 2013265921;
                }
            })
        };
        let ts: Vec<TraceCols> = tabs
            .iter()
            .enumerate()
            .map(|(i, &(lh, w))| mk(lh, w, i as u32 + 1))
            .collect();
        let srcs: Vec<Src> = ts.iter().map(Src::Main).collect();
        let mats: Vec<CMat> = srcs
            .iter()
            .zip(&ts)
            .map(|(s, t)| {
                let class = l0 - (t.log_h + 4);
                CMat {
                    src: s,
                    lde: t.log_h + 4,
                    shift: shift().exp_power_of_2(class),
                    class,
                }
            })
            .collect();
        // reference: full LDE (natural) as bitrev Mats
        let refm: Vec<Mat> = ts
            .iter()
            .zip(&mats)
            .map(|(t, m)| {
                let v = if t.width() == 0 {
                    vec![]
                } else {
                    dft.coset_lde_batch(t.chunk(0, t.width()), 4, m.shift)
                        .to_row_major_matrix()
                        .values
                };
                Mat {
                    width: t.width(),
                    log_height: m.lde,
                    values: v,
                    bitrev: true,
                }
            })
            .collect();
        let rt = mmcs::commit(&refm);
        for &(group, chunk) in runs {
            let t = commit(&dft, &mats, l0, group, chunk, KEEP);
            assert_eq!(t.root(), rt.root(), "group {group} chunk {chunk}");
            let n0 = 1usize << l0;
            let qs = vec![5, n0 - 192, n0 / 2 + 1, 5, 123];
            let a = open(&dft, &mats, &t, &qs, chunk);
            let b = mmcs::open(&refm, &rt, &qs);
            assert_eq!(a, b);
        }
        let _ = F::ZERO;
    }
}
