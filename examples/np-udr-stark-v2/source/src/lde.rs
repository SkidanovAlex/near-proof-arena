//! Cache-blocked coset DFT with bit-reversed output, for the LDE blocks of
//! the large tables.
//!
//! [`CosetDft::eval`] computes, for coefficients `C` (`T × w`, natural order,
//! row-major) and a coset shift `c`, the evaluations
//! `dst[u] = Σ_i C_i · (c · ω_T^{rev(u)})^i` (`u < T`, bit-reversed order) —
//! exactly what [`crate::lowmem::eval_range`] returns for a whole LDE block —
//! with a decimation-in-frequency network (natural input, bit-reversed
//! output), so no permutation pass is needed:
//!
//! * `T = R · S`; the first `log R` layers pair rows of equal residue
//!   `s = i mod S`: residues are processed in batches, each batch gathered
//!   (and multiplied by the coset powers `c^i`) from the source into an
//!   L2-sized scratch, transformed, and scattered into `dst`;
//! * the last `log S` layers act on contiguous blocks of `S` rows of `dst`,
//!   in place.
//!
//! The arithmetic is exact, so the output is bit for bit the same as any
//! other DFT (tested against `eval_range`).

use p3_field::{Field, PackedValue, PrimeCharacteristicRing};
use rayon::prelude::*;

use crate::field::{F, omega};

type PF = <F as Field>::Packing;

/// Twiddles of a size-`2^n` coset DFT (see the module docs).
pub struct CosetDft {
    n: usize,
    n1: usize,
    /// layer `k < n1`, `r' < R >> (k+1)`: `ω_R^{2^k r'}`
    tw1: Vec<Vec<F>>,
    /// layer `k < n1`, `s < S`: `ω_T^{2^k s}`
    tws: Vec<Vec<F>>,
    /// layer `k ≥ n1` (half-size `h = 2^(n-1-k)`), `j < h`: `ω_{2h}^j`
    tw2: Vec<Vec<F>>,
}

/// `a, b ← a + b, (a − b)·tw` on two rows.
#[inline(always)]
fn bfly(a: &mut [F], b: &mut [F], tw: F) {
    let (ap, at) = PF::pack_slice_with_suffix_mut(a);
    let (bp, bt) = PF::pack_slice_with_suffix_mut(b);
    let t = PF::from(tw);
    for (x, y) in ap.iter_mut().zip(bp.iter_mut()) {
        let s = *x + *y;
        let d = (*x - *y) * t;
        *x = s;
        *y = d;
    }
    for (x, y) in at.iter_mut().zip(bt.iter_mut()) {
        let s = *x + *y;
        let d = (*x - *y) * tw;
        *x = s;
        *y = d;
    }
}

/// `a, b ← a + b, a − b` on two rows.
#[inline(always)]
fn bfly1(a: &mut [F], b: &mut [F]) {
    let (ap, at) = PF::pack_slice_with_suffix_mut(a);
    let (bp, bt) = PF::pack_slice_with_suffix_mut(b);
    for (x, y) in ap.iter_mut().zip(bp.iter_mut()) {
        let s = *x + *y;
        let d = *x - *y;
        *x = s;
        *y = d;
    }
    for (x, y) in at.iter_mut().zip(bt.iter_mut()) {
        let s = *x + *y;
        let d = *x - *y;
        *x = s;
        *y = d;
    }
}

/// `dst = src · k` (rows of equal length).
#[inline(always)]
fn scale_into(dst: &mut [F], src: &[F], k: F) {
    let (dp, dt) = PF::pack_slice_with_suffix_mut(dst);
    let n = dp.len() * PF::WIDTH;
    let (sp, st) = src.split_at(n);
    let kp = PF::from(k);
    for (d, s) in dp.iter_mut().zip(PF::pack_slice(sp)) {
        *d = *s * kp;
    }
    for (d, s) in dt.iter_mut().zip(st) {
        *d = *s * k;
    }
}

/// Rows `i` and `i + h` of a row-major buffer of width `w`.
#[inline(always)]
fn two_rows(buf: &mut [F], w: usize, i: usize, h: usize) -> (&mut [F], &mut [F]) {
    let (lo, hi) = buf.split_at_mut((i + h) * w);
    (&mut lo[i * w..(i + 1) * w], &mut hi[..w])
}

impl CosetDft {
    pub fn new(n: usize) -> CosetDft {
        let n1 = n / 2;
        let (r, s) = (1usize << n1, 1usize << (n - n1));
        let wr = omega(n1);
        let wt = omega(n);
        let tw1 = (0..n1)
            .map(|k| wr.exp_power_of_2(k).powers().take(r >> (k + 1)).collect())
            .collect();
        let tws = (0..n1)
            .map(|k| wt.exp_power_of_2(k).powers().take(s).collect())
            .collect();
        let tw2 = (n1..n)
            .map(|k| {
                let h = 1usize << (n - 1 - k);
                omega(n - k).powers().take(h).collect()
            })
            .collect();
        CosetDft {
            n,
            n1,
            tw1,
            tws,
            tw2,
        }
    }

    pub fn log_size(&self) -> usize {
        self.n
    }

    /// Evaluations of the `w` polynomials with coefficients `src` (`T × w`)
    /// on `c·⟨ω_T⟩`, in bit-reversed order, into `dst` (`T × w`).
    pub fn eval(&self, src: &[F], w: usize, c: F, dst: &mut [F]) {
        let n = self.n;
        let t = 1usize << n;
        assert_eq!(src.len(), t * w);
        assert_eq!(dst.len(), t * w);
        if w == 0 {
            return;
        }
        let n1 = self.n1;
        let (r, s) = (1usize << n1, 1usize << (n - n1));
        // ---- phase 1: layers 0..n1 on residue batches ----
        // batch: `bs` residues (rows `r·S + s0 .. r·S + s0 + bs` are contiguous)
        let bs = (256 / (w * 4)).clamp(1, s).next_power_of_two().min(s);
        let cs = c.exp_u64(s as u64);
        let cpow_r: Vec<F> = cs.powers().take(r).collect();
        let cpow_s: Vec<F> = c.powers().take(s).collect();
        let bw = bs * w;
        {
            let dptr = SendPtr(dst.as_mut_ptr());
            (0..s / bs).into_par_iter().for_each_init(
                || vec![F::ZERO; r * bw],
                |scr, bi| {
                    let s0 = bi * bs;
                    // gather × c^i
                    for rr in 0..r {
                        let row0 = (rr * s + s0) * w;
                        for b in 0..bs {
                            let k = cpow_r[rr] * cpow_s[s0 + b];
                            scale_into(
                                &mut scr[rr * bw + b * w..rr * bw + (b + 1) * w],
                                &src[row0 + b * w..row0 + (b + 1) * w],
                                k,
                            );
                        }
                    }
                    let mut tw = vec![F::ZERO; bs];
                    for k in 0..n1 {
                        let hr = r >> (k + 1);
                        let t1 = &self.tw1[k];
                        let ts = &self.tws[k][s0..s0 + bs];
                        for blk in (0..r).step_by(2 * hr) {
                            for rp in 0..hr {
                                let (a, bb) = two_rows(scr, bw, blk + rp, hr);
                                for (x, &y) in tw.iter_mut().zip(ts) {
                                    *x = t1[rp] * y;
                                }
                                for b in 0..bs {
                                    bfly(
                                        &mut a[b * w..(b + 1) * w],
                                        &mut bb[b * w..(b + 1) * w],
                                        tw[b],
                                    );
                                }
                            }
                        }
                    }
                    // scatter
                    for rr in 0..r {
                        let row0 = (rr * s + s0) * w;
                        // SAFETY: batches write disjoint rows `r·S + s0 .. + bs`.
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                scr[rr * bw..(rr + 1) * bw].as_ptr(),
                                dptr.get().add(row0),
                                bw,
                            );
                        }
                    }
                },
            );
        }
        // ---- phase 2: layers n1..n on contiguous blocks of S rows ----
        dst.par_chunks_mut(s * w).for_each(|blk| {
            for (k2, t2) in self.tw2.iter().enumerate() {
                let h = 1usize << (n - n1 - 1 - k2);
                for b0 in (0..s).step_by(2 * h) {
                    {
                        let (a, bb) = two_rows(blk, w, b0, h);
                        bfly1(a, bb);
                    }
                    for j in 1..h {
                        let (a, bb) = two_rows(blk, w, b0 + j, h);
                        bfly(a, bb, t2[j]);
                    }
                }
            }
        });
    }
}

/// Shared [`CosetDft`] of size `2^n` (twiddles computed once).
pub fn coset_dft(n: usize) -> std::sync::Arc<CosetDft> {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<HashMap<usize, Arc<CosetDft>>>> = OnceLock::new();
    let m = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    m.lock()
        .unwrap()
        .entry(n)
        .or_insert_with(|| Arc::new(CosetDft::new(n)))
        .clone()
}

#[derive(Clone, Copy)]
struct SendPtr(*mut F);
// SAFETY: used only for disjoint writes from parallel tasks.
unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}
impl SendPtr {
    #[inline(always)]
    fn get(self) -> *mut F {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::shift;
    use crate::lowmem::{Dft, eval_range};
    use crate::mmcs::rev;
    use p3_dft::TwoAdicSubgroupDft;
    use p3_matrix::dense::RowMajorMatrix;

    #[test]
    fn matches_eval_range() {
        let dft = Dft::default();
        for (n, w) in [
            (0usize, 3usize),
            (1, 8),
            (2, 1),
            (3, 5),
            (5, 8),
            (6, 13),
            (9, 32),
            (10, 7),
            (11, 64),
        ] {
            let t = 1usize << n;
            let vals: Vec<F> = (0..(t * w) as u64)
                .map(|i| F::from_u64(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 33))
                .collect();
            let co = dft.idft_batch(RowMajorMatrix::new(vals, w));
            let cd = CosetDft::new(n);
            let l = n + 4;
            let sh = shift().exp_power_of_2(2);
            for b in [0usize, 1, 5, 15] {
                let p0 = b * t;
                let want = eval_range(&dft, &co, l, sh, p0, t, None);
                let c = sh * omega(l).exp_u64(rev(b, 4) as u64);
                let mut got = vec![F::ZERO; t * w];
                cd.eval(&co.values, w, c, &mut got);
                assert_eq!(got, want.values, "n {n} w {w} block {b}");
            }
        }
    }
}
