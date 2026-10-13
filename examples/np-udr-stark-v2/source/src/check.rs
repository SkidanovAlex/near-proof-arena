//! Debug helpers: evaluate an AIR directly on its traces (no commitments).
//!
//! * [`failing_constraints`] — every `(constraint index, row)` where a
//!   constraint of `Table.constraints` (incl. the bit constraints) is non-zero
//!   (selectors are the exact row indicators, `next` wraps around);
//! * [`bus_imbalance`] — the multiset of `(bus, msg)` with
//!   `Σ send multiplicities ≠ Σ receive multiplicities` (multiplicity
//!   `Σ_k bit_k 2^k`, as in `Interaction.multNat`).
use std::collections::BTreeMap;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rayon::prelude::*;

use crate::air::{Air, Expr, Table, Tape};
use crate::field::F;

fn sel(r: usize, n: usize) -> [F; 3] {
    let last = r + 1 == n;
    [
        F::from_bool(r == 0),
        F::from_bool(last),
        F::from_bool(!last),
    ]
}

/// `(constraint, row)` pairs that fail, at most `limit` of them.
pub fn failing_constraints(
    t: &Table,
    tr: &RowMajorMatrix<F>,
    pubs: &[F],
    limit: usize,
) -> Vec<(usize, usize)> {
    let tape = Tape::compile(&t.constraints);
    let n = tr.height();
    let w = tr.width();
    let v = &tr.values;
    let mut bad: Vec<(usize, usize)> = (0..n)
        .into_par_iter()
        .flat_map_iter(|r| {
            let mut regs = Vec::with_capacity(tape.ops.len());
            let nx = (r + 1) % n;
            tape.eval(
                &mut regs,
                |c, next| v[(if next { nx } else { r }) * w + c],
                pubs,
                sel(r, n),
            );
            let out: Vec<(usize, usize)> = tape
                .outputs
                .iter()
                .enumerate()
                .filter(|(_, o)| regs[**o as usize] != F::ZERO)
                .map(|(i, _)| (i, r))
                .collect();
            out
        })
        .collect();
    bad.sort();
    bad.truncate(limit);
    bad
}

/// Bus messages whose send and receive multiplicities differ:
/// `(bus, msg, sent, received)`.
pub fn bus_imbalance(
    air: &Air,
    trs: &[RowMajorMatrix<F>],
    pubs: &[F],
) -> Vec<(usize, Vec<u32>, u64, u64)> {
    let mut m: BTreeMap<(usize, Vec<u32>), (u64, u64)> = BTreeMap::new();
    for (t, tr) in air.tables.iter().zip(trs) {
        let (n, w) = (tr.height(), tr.width());
        for it in &t.interactions {
            let exprs: Vec<Expr> = it.mult.iter().chain(&it.msg).cloned().collect();
            let tape = Tape::compile(&exprs);
            let nb = it.mult.len();
            let mut regs = vec![];
            for r in 0..n {
                tape.eval(
                    &mut regs,
                    |c, next| tr.values[(if next { (r + 1) % n } else { r }) * w + c],
                    pubs,
                    sel(r, n),
                );
                let out: Vec<F> = tape.outputs.iter().map(|&o| regs[o as usize]).collect();
                let mult: u64 = (0..nb)
                    .map(|k| if out[k] == F::ONE { 1u64 << k } else { 0 })
                    .sum();
                if mult == 0 {
                    continue;
                }
                let msg: Vec<u32> = out[nb..].iter().map(|x| x.as_canonical_u32()).collect();
                let ent = m.entry((it.bus, msg)).or_default();
                if it.send {
                    ent.0 += mult
                } else {
                    ent.1 += mult
                }
            }
        }
    }
    m.into_iter()
        .filter(|(_, (s, r))| s != r)
        .map(|((b, msg), (s, r))| (b, msg, s, r))
        .collect()
}

/// One unbalanced bus message: `(bus, msg, sent, received)`.
pub type Imbalance = (usize, Vec<u32>, u64, u64);

/// [`bus_imbalance`] restricted to one bus, over a subset of the tables plus the
/// public messages of the prepared tape (`pubMsgs`, `globalChecksP`): every table
/// interaction on `bus` of the supplied `(table index, trace)` pairs and every public
/// message on `bus`.  Balanced iff every table touching `bus` is supplied (the caller's
/// responsibility); `None` when the tape does not fit (`pubFit`).
pub fn bus_imbalance_with_pub(
    air: &Air,
    trs: &[(usize, &RowMajorMatrix<F>)],
    pubs: &[F],
    tape: &[u8],
    bus: usize,
) -> Option<Vec<Imbalance>> {
    if !crate::verifier::pub_fit(air, tape) {
        return None;
    }
    let mut m: BTreeMap<(usize, Vec<u32>), (u64, u64)> = BTreeMap::new();
    for &(ti, tr) in trs {
        let t = &air.tables[ti];
        let (n, w) = (tr.height(), tr.width());
        for it in t.interactions.iter().filter(|it| it.bus == bus) {
            let exprs: Vec<Expr> = it.mult.iter().chain(&it.msg).cloned().collect();
            let tape = Tape::compile(&exprs);
            let nb = it.mult.len();
            let mut regs = vec![];
            for r in 0..n {
                tape.eval(
                    &mut regs,
                    |c, next| tr.values[(if next { (r + 1) % n } else { r }) * w + c],
                    pubs,
                    sel(r, n),
                );
                let out: Vec<F> = tape.outputs.iter().map(|&o| regs[o as usize]).collect();
                let mult: u64 = (0..nb)
                    .map(|k| if out[k] == F::ONE { 1u64 << k } else { 0 })
                    .sum();
                if mult == 0 {
                    continue;
                }
                let msg: Vec<u32> = out[nb..].iter().map(|x| x.as_canonical_u32()).collect();
                let ent = m.entry((it.bus, msg)).or_default();
                if it.send {
                    ent.0 += mult
                } else {
                    ent.1 += mult
                }
            }
        }
    }
    for (b, send, rec) in crate::verifier::pub_msgs(air, tape) {
        if b != bus {
            continue;
        }
        let msg: Vec<u32> = rec.iter().map(|x| x.as_canonical_u32()).collect();
        let ent = m.entry((b, msg)).or_default();
        if send { ent.0 += 1 } else { ent.1 += 1 }
    }
    Some(
        m.into_iter()
            .filter(|(_, (s, r))| s != r)
            .map(|((b, msg), (s, r))| (b, msg, s, r))
            .collect(),
    )
}

/// [`failing_constraints`] on compact column storage ([`crate::cols::TraceCols`],
/// the `render_cols` path for cases whose row-major traces do not fit).
pub fn failing_constraints_cols(
    t: &Table,
    tr: &crate::cols::TraceCols,
    pubs: &[F],
    limit: usize,
) -> Vec<(usize, usize)> {
    let tape = Tape::compile(&t.constraints);
    if all_vanish_cols(&tape, tr, pubs) {
        return vec![];
    }
    let n = tr.height();
    // rows in chunks, one register file per task
    const CH: usize = 4096;
    let mut bad: Vec<(usize, usize)> = (0..n.div_ceil(CH))
        .into_par_iter()
        .map_init(
            || Vec::with_capacity(tape.ops.len()),
            |regs, k| {
                let mut out = vec![];
                for r in k * CH..((k + 1) * CH).min(n) {
                    let nx = (r + 1) % n;
                    tape.eval(
                        regs,
                        |c, next| tr.get(if next { nx } else { r }, c),
                        pubs,
                        sel(r, n),
                    );
                    for (i, o) in tape.outputs.iter().enumerate() {
                        if regs[*o as usize] != F::ZERO {
                            out.push((i, r));
                        }
                    }
                }
                out
            },
        )
        .flatten()
        .collect();
    bad.sort();
    bad.truncate(limit);
    bad
}

/// Fast pre-check of [`failing_constraints_cols`]: whether the fixed
/// combination `Σ_k α^k·C_k` vanishes on every row (packed [`BlockEval`]).
/// Every constraint vanishing implies it; a failing constraint makes it
/// non-zero except with probability `≤ #constraints / |K|` (`α` is fixed and
/// the traces are honest, so this only selects the fast path — a `true`
/// with a failing constraint would also be caught by the verifier re-check).
///
/// [`BlockEval`]: crate::eval::BlockEval
fn all_vanish_cols(tape: &Tape, tr: &crate::cols::TraceCols, pubs: &[F]) -> bool {
    use crate::cols::Col;
    use crate::field::EF;
    use p3_field::BasedVectorSpace;
    let n = tr.height();
    let w = tr.width();
    if tape.outputs.is_empty() || n < 2 {
        return tape.outputs.is_empty();
    }
    let be = crate::eval::BlockEval::new(tape, pubs);
    let alpha = EF::from_basis_coefficients_fn(|i| {
        F::new(0x2d5b_3a17u32.wrapping_mul(i as u32 + 7) % 0x7800_0001)
    });
    let apow: Vec<EF> = alpha.powers().take(tape.outputs.len()).collect();
    const CH: usize = 4096;
    (0..n.div_ceil(CH)).into_par_iter().all(|k| {
        let r0 = k * CH;
        let len = CH.min(n - r0);
        // rows r0 .. r0+len and the next row of the last one (wrapping)
        let mut buf = vec![F::ZERO; (len + 1) * w];
        for (c, col) in tr.cols.iter().enumerate() {
            let rows = (r0..r0 + len).chain(std::iter::once((r0 + len) % n));
            match col {
                Col::U8(v) => rows
                    .enumerate()
                    .for_each(|(i, r)| buf[i * w + c] = F::new(v[r] as u32)),
                Col::U16(v) => rows
                    .enumerate()
                    .for_each(|(i, r)| buf[i * w + c] = F::new(v[r] as u32)),
                Col::U32(v) => rows
                    .enumerate()
                    .for_each(|(i, r)| buf[i * w + c] = F::new(v[r])),
            }
        }
        let next: Vec<u32> = (1..=len as u32).collect();
        let sf: Vec<F> = (0..len).map(|i| F::from_bool(r0 + i == 0)).collect();
        let sl: Vec<F> = (0..len).map(|i| F::from_bool(r0 + i + 1 == n)).collect();
        let mut out = vec![EF::ZERO; len];
        be.eval_rows(&buf, w, 0, &next, &sf, &sl, &apow, &mut out);
        out.iter().all(|x| *x == EF::ZERO)
    })
}

/// Bus balance on compact column storage: per bus, the number of distinct
/// messages whose net multiplicity (sent − received) is non-zero, and the
/// total number of (bus, message) multiplicity units sent. Messages are keyed
/// by a 128-bit hash of `(bus, msg)` (two independently salted SipHashes) so
/// the max case fits in memory.
pub fn bus_imbalance_cols(
    air: &Air,
    trs: &[crate::cols::TraceCols],
    pubs: &[F],
) -> (BTreeMap<usize, usize>, u64) {
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};
    fn key(bus: usize, msg: &[u32]) -> u128 {
        let mut a = std::collections::hash_map::DefaultHasher::new();
        (bus, msg).hash(&mut a);
        let mut b = std::collections::hash_map::DefaultHasher::new();
        (0x9e37_79b9u32, bus, msg).hash(&mut b);
        ((a.finish() as u128) << 64) | b.finish() as u128
    }
    let mut net: HashMap<u128, (usize, i64)> = HashMap::new();
    let mut total = 0u64;
    for (t, tr) in air.tables.iter().zip(trs) {
        let n = tr.height();
        for it in &t.interactions {
            let exprs: Vec<Expr> = it.mult.iter().chain(&it.msg).cloned().collect();
            let tape = Tape::compile(&exprs);
            let nb = it.mult.len();
            const CH: usize = 1 << 16;
            for c0 in (0..n).step_by(CH) {
                let part: Vec<(u128, i64)> = (c0..(c0 + CH).min(n))
                    .into_par_iter()
                    .filter_map(|r| {
                        let mut regs = vec![];
                        tape.eval(
                            &mut regs,
                            |c, next| tr.get(if next { (r + 1) % n } else { r }, c),
                            pubs,
                            sel(r, n),
                        );
                        let out: Vec<F> = tape.outputs.iter().map(|&o| regs[o as usize]).collect();
                        let mult: i64 = (0..nb)
                            .map(|k| if out[k] == F::ONE { 1i64 << k } else { 0 })
                            .sum();
                        if mult == 0 {
                            return None;
                        }
                        let msg: Vec<u32> =
                            out[nb..].iter().map(|x| x.as_canonical_u32()).collect();
                        Some((key(it.bus, &msg), if it.send { mult } else { -mult }))
                    })
                    .collect();
                for (k, d) in part {
                    if d > 0 {
                        total += d as u64;
                    }
                    let e = net.entry(k).or_insert((it.bus, 0));
                    e.1 += d;
                    if e.1 == 0 {
                        net.remove(&k);
                    }
                }
            }
        }
    }
    let mut per_bus = BTreeMap::new();
    for (_, (bus, _)) in net {
        *per_bus.entry(bus).or_insert(0usize) += 1;
    }
    (per_bus, total)
}
