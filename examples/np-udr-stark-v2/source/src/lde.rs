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
    /// inverse, phase A, layer `a < n2` (half-size `2^a`), `j < 2^a`: `ω_{2^(a+1)}^{-j}`
    itwa: Vec<Vec<F>>,
    /// inverse, phase B, layer `k < n1` (half-size `2^k·S`), `r' < 2^k`: `ω_{2^(k+1)}^{-r'}`
    itw1: Vec<Vec<F>>,
    /// inverse, phase B, layer `k < n1`, `s < S`: `ω_{2^(k+1)·S}^{-s}`
    itws: Vec<Vec<F>>,
}

/// Row operations of the transforms (whole rows of equal length).
trait Rows {
    /// `a, b ← a + b, (a − b)·tw`
    fn bfly(a: &mut [F], b: &mut [F], tw: F);
    /// `a, b ← a + b, a − b`
    fn bfly1(a: &mut [F], b: &mut [F]);
    /// `a, b ← a + b·tw, a − b·tw` (decimation in time)
    fn bfly_dit(a: &mut [F], b: &mut [F], tw: F);
    /// `dst = src · k`
    fn scale_into(dst: &mut [F], src: &[F], k: F);
    /// `x ← x · k`
    fn scale(x: &mut [F], k: F);
}

/// Plonky3's packed field (AVX2 with the crate's target flags).
struct Packed;

impl Rows for Packed {
    #[inline(always)]
    fn bfly_dit(a: &mut [F], b: &mut [F], tw: F) {
        let (ap, at) = PF::pack_slice_with_suffix_mut(a);
        let (bp, bt) = PF::pack_slice_with_suffix_mut(b);
        let t = PF::from(tw);
        for (x, y) in ap.iter_mut().zip(bp.iter_mut()) {
            let m = *y * t;
            let s = *x + m;
            *y = *x - m;
            *x = s;
        }
        for (x, y) in at.iter_mut().zip(bt.iter_mut()) {
            let m = *y * tw;
            let s = *x + m;
            *y = *x - m;
            *x = s;
        }
    }

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

    #[inline(always)]
    fn scale(x: &mut [F], k: F) {
        let (xp, xt) = PF::pack_slice_with_suffix_mut(x);
        let kp = PF::from(k);
        for v in xp.iter_mut() {
            *v *= kp;
        }
        for v in xt.iter_mut() {
            *v *= k;
        }
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
        let n2 = n - n1;
        let itwa = (0..n2)
            .map(|a| omega(a + 1).inverse().powers().take(1 << a).collect())
            .collect();
        let itw1 = (0..n1)
            .map(|k| omega(k + 1).inverse().powers().take(1 << k).collect())
            .collect();
        let itws = (0..n1)
            .map(|k| omega(k + 1 + n2).inverse().powers().take(s).collect())
            .collect();
        CosetDft {
            n,
            n1,
            tw1,
            tws,
            tw2,
            itwa,
            itw1,
            itws,
        }
    }

    pub fn log_size(&self) -> usize {
        self.n
    }

    /// Evaluations of the `w` polynomials with coefficients `src` (`T × w`)
    /// on `c·⟨ω_T⟩`, in bit-reversed order, into `dst` (`T × w`).
    pub fn eval(&self, src: &[F], w: usize, c: F, dst: &mut [F]) {
        self.eval_cols(src, w, 0, w, c, dst)
    }

    /// As [`Self::eval`] for the columns `c0 .. c0 + w` of `src` (rows of
    /// width `sw`), read in place.
    pub fn eval_cols(&self, src: &[F], sw: usize, c0: usize, w: usize, c: F, dst: &mut [F]) {
        let n = self.n;
        let t = 1usize << n;
        assert_eq!(src.len(), t * sw);
        assert!(c0 + w <= sw);
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
        let wide = avx512();
        {
            let dptr = SendPtr(dst.as_mut_ptr());
            let k = P1 {
                cd: self,
                src,
                sw,
                c0,
                w,
                bs,
                cpow_r: &cpow_r,
                cpow_s: &cpow_s,
                dptr,
            };
            (0..s / bs).into_par_iter().for_each_init(
                || (vec![F::ZERO; r * bw], vec![F::ZERO; bs]),
                |(scr, tw), bi| {
                    #[cfg(target_arch = "x86_64")]
                    if wide {
                        // SAFETY: AVX-512F is available (checked).
                        unsafe { k.run_avx512(scr, tw, bi * bs) };
                        return;
                    }
                    k.run::<Packed>(scr, tw, bi * bs);
                },
            );
        }
        // ---- phase 2: layers n1..n on contiguous blocks of S rows ----
        dst.par_chunks_mut(s * w).for_each(|blk| {
            #[cfg(target_arch = "x86_64")]
            if wide {
                // SAFETY: as above.
                unsafe { p2_block_avx512(self, blk, w) };
                return;
            }
            p2_block::<Packed>(self, blk, w);
        });
    }
}

/// Phase 1 of [`CosetDft::eval_cols`] on one residue batch.
struct P1<'a> {
    cd: &'a CosetDft,
    src: &'a [F],
    sw: usize,
    c0: usize,
    w: usize,
    bs: usize,
    cpow_r: &'a [F],
    cpow_s: &'a [F],
    dptr: SendPtr,
}

impl P1<'_> {
    #[inline(always)]
    fn run<R: Rows>(&self, scr: &mut [F], tw: &mut [F], s0: usize) {
        let (cd, w, bs, sw, c0) = (self.cd, self.w, self.bs, self.sw, self.c0);
        let n1 = cd.n1;
        let (r, s) = (1usize << n1, 1usize << (cd.n - n1));
        let bw = bs * w;
        // gather × c^i
        for rr in 0..r {
            for b in 0..bs {
                let k = self.cpow_r[rr] * self.cpow_s[s0 + b];
                let row = (rr * s + s0 + b) * sw + c0;
                R::scale_into(
                    &mut scr[rr * bw + b * w..rr * bw + (b + 1) * w],
                    &self.src[row..row + w],
                    k,
                );
            }
        }
        for k in 0..n1 {
            let hr = r >> (k + 1);
            let t1 = &cd.tw1[k];
            let ts = &cd.tws[k][s0..s0 + bs];
            for blk in (0..r).step_by(2 * hr) {
                for rp in 0..hr {
                    let (a, bb) = two_rows(scr, bw, blk + rp, hr);
                    for (x, &y) in tw.iter_mut().zip(ts) {
                        *x = t1[rp] * y;
                    }
                    for b in 0..bs {
                        R::bfly(
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
                    self.dptr.get().add(row0),
                    bw,
                );
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx512f")]
    unsafe fn run_avx512(&self, scr: &mut [F], tw: &mut [F], s0: usize) {
        self.run::<avx512::Wide>(scr, tw, s0)
    }
}

/// Phase 2 of [`CosetDft::eval_cols`] on one block of `S` rows.
#[inline(always)]
fn p2_block<R: Rows>(cd: &CosetDft, blk: &mut [F], w: usize) {
    let n = cd.n;
    let n1 = cd.n1;
    let s = 1usize << (n - n1);
    for (k2, t2) in cd.tw2.iter().enumerate() {
        let h = 1usize << (n - n1 - 1 - k2);
        for b0 in (0..s).step_by(2 * h) {
            {
                let (a, bb) = two_rows(blk, w, b0, h);
                R::bfly1(a, bb);
            }
            for j in 1..h {
                let (a, bb) = two_rows(blk, w, b0 + j, h);
                R::bfly(a, bb, t2[j]);
            }
        }
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx512f")]
unsafe fn p2_block_avx512(cd: &CosetDft, blk: &mut [F], w: usize) {
    p2_block::<avx512::Wide>(cd, blk, w)
}

/// Inverse DFT of a `2^n × w` value matrix (natural order) into
/// coefficients: [`CosetDft::idft`] from `2^10` rows on, Plonky3 below.
pub fn idft(
    dft: &crate::lowmem::Dft,
    m: p3_matrix::dense::RowMajorMatrix<F>,
) -> p3_matrix::dense::RowMajorMatrix<F> {
    use p3_dft::TwoAdicSubgroupDft;
    use p3_matrix::Matrix;
    let (h, w) = (m.height(), m.width());
    if w == 0 || h < 1 << 10 {
        return dft.idft_batch(m);
    }
    let mut out = crate::bufpool::take(h * w);
    coset_dft(p3_util::log2_strict_usize(h)).idft(&m.values, w, &mut out);
    crate::bufpool::give(m.values);
    p3_matrix::dense::RowMajorMatrix::new(out, w)
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

impl CosetDft {
    /// Coefficients (natural order) of the `w` polynomials whose values on
    /// `⟨ω_T⟩` (natural order) are `src` (`T × w`), into `dst` — the inverse
    /// DFT, decimation in time:
    ///
    /// * phase A: `dst` block `j` (rows `j·S ..`) = the bit-reversed input
    ///   rows `rev(j·S + q)` = source rows `rev_{n1}(j) + R·rev_{n2}(q)`,
    ///   gathered and put through the first `log S` layers in place;
    /// * phase B: the last `log R` layers on residue batches (rows of equal
    ///   `i mod S`), scaled by `1/T` on the way out.
    pub fn idft(&self, src: &[F], w: usize, dst: &mut [F]) {
        self.idft_from(src, w, false, dst)
    }

    /// As [`Self::idft`]; with `bitrev`, the values `src` are given in
    /// bit-reversed order (row `u` = the value at `ω_T^{rev(u)}`).
    pub fn idft_from(&self, src: &[F], w: usize, bitrev: bool, dst: &mut [F]) {
        let n = self.n;
        let t = 1usize << n;
        assert_eq!(src.len(), t * w);
        assert_eq!(dst.len(), t * w);
        if w == 0 {
            return;
        }
        let n1 = self.n1;
        let n2 = n - n1;
        let (r, s) = (1usize << n1, 1usize << n2);
        let wide = avx512();
        // ---- phase A ----
        dst.par_chunks_mut(s * w).enumerate().for_each(|(j, blk)| {
            if bitrev {
                blk.copy_from_slice(&src[j * s * w..(j + 1) * s * w]);
            } else {
                let rj = crate::mmcs::rev(j, n1);
                for q in 0..s {
                    let row = rj + r * crate::mmcs::rev(q, n2);
                    blk[q * w..(q + 1) * w].copy_from_slice(&src[row * w..(row + 1) * w]);
                }
            }
            #[cfg(target_arch = "x86_64")]
            if wide {
                // SAFETY: AVX-512F is available (checked).
                unsafe { ia_block_avx512(self, blk, w) };
                return;
            }
            ia_block::<Packed>(self, blk, w);
        });
        // ---- phase B ----
        let tinv = F::from_u64(t as u64).inverse();
        let bs = (256 / (w * 4)).clamp(1, s).next_power_of_two().min(s);
        let bw = bs * w;
        let k = IB {
            cd: self,
            w,
            bs,
            tinv,
            dptr: SendPtr(dst.as_mut_ptr()),
        };
        (0..s / bs).into_par_iter().for_each_init(
            || (vec![F::ZERO; r * bw], vec![F::ZERO; bs]),
            |(scr, tw), bi| {
                #[cfg(target_arch = "x86_64")]
                if wide {
                    // SAFETY: as above.
                    unsafe { k.run_avx512(scr, tw, bi * bs) };
                    return;
                }
                k.run::<Packed>(scr, tw, bi * bs);
            },
        );
    }
}

/// Phase A of [`CosetDft::idft_from`] on one gathered block of `S` rows.
#[inline(always)]
fn ia_block<R: Rows>(cd: &CosetDft, blk: &mut [F], w: usize) {
    let s = 1usize << (cd.n - cd.n1);
    for (a, tw) in cd.itwa.iter().enumerate() {
        let h = 1usize << a;
        for b0 in (0..s).step_by(2 * h) {
            {
                let (x, y) = two_rows(blk, w, b0, h);
                R::bfly1(x, y);
            }
            for jj in 1..h {
                let (x, y) = two_rows(blk, w, b0 + jj, h);
                R::bfly_dit(x, y, tw[jj]);
            }
        }
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx512f")]
unsafe fn ia_block_avx512(cd: &CosetDft, blk: &mut [F], w: usize) {
    ia_block::<avx512::Wide>(cd, blk, w)
}

/// Phase B of [`CosetDft::idft_from`] on one residue batch.
struct IB<'a> {
    cd: &'a CosetDft,
    w: usize,
    bs: usize,
    tinv: F,
    dptr: SendPtr,
}

impl IB<'_> {
    #[inline(always)]
    fn run<R: Rows>(&self, scr: &mut [F], tw: &mut [F], s0: usize) {
        let (cd, w, bs) = (self.cd, self.w, self.bs);
        let n1 = cd.n1;
        let (r, s) = (1usize << n1, 1usize << (cd.n - n1));
        let bw = bs * w;
        for rr in 0..r {
            let row0 = (rr * s + s0) * w;
            // SAFETY: batches read and write disjoint rows `r·S + s0 .. + bs`.
            unsafe {
                std::ptr::copy_nonoverlapping(
                    self.dptr.get().add(row0),
                    scr[rr * bw..(rr + 1) * bw].as_mut_ptr(),
                    bw,
                );
            }
        }
        for k in 0..n1 {
            let hr = 1usize << k;
            let t1 = &cd.itw1[k];
            let ts = &cd.itws[k][s0..s0 + bs];
            for blk in (0..r).step_by(2 * hr) {
                for rp in 0..hr {
                    let (x, y) = two_rows(scr, bw, blk + rp, hr);
                    for (z, &v) in tw.iter_mut().zip(ts) {
                        *z = t1[rp] * v;
                    }
                    for b in 0..bs {
                        R::bfly_dit(
                            &mut x[b * w..(b + 1) * w],
                            &mut y[b * w..(b + 1) * w],
                            tw[b],
                        );
                    }
                }
            }
        }
        for rr in 0..r {
            let row0 = (rr * s + s0) * w;
            let blk = &mut scr[rr * bw..(rr + 1) * bw];
            R::scale(blk, self.tinv);
            // SAFETY: as above.
            unsafe {
                std::ptr::copy_nonoverlapping(blk.as_ptr(), self.dptr.get().add(row0), bw);
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx512f")]
    unsafe fn run_avx512(&self, scr: &mut [F], tw: &mut [F], s0: usize) {
        self.run::<avx512::Wide>(scr, tw, s0)
    }
}

/// Whether the AVX-512 row backend is used (`NPUDR_NO_AVX512=1` disables it).
fn avx512() -> bool {
    use std::sync::OnceLock;
    static A: OnceLock<bool> = OnceLock::new();
    *A.get_or_init(|| {
        #[cfg(target_arch = "x86_64")]
        {
            std::arch::is_x86_feature_detected!("avx512f")
                && std::env::var("NPUDR_NO_AVX512").map_or(true, |v| v != "1")
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            false
        }
    })
}

/// AVX-512 row backend (runtime-detected): 16 Montgomery-form BabyBear
/// elements per vector; canonical add / sub / Montgomery multiply exactly as
/// Plonky3's packed fields (same canonical results; tested against `F`).
#[cfg(target_arch = "x86_64")]
mod avx512 {
    use core::arch::x86_64::*;

    use super::{F, Packed, Rows};

    const P: u32 = 0x7800_0001;
    /// `P^{-1} mod 2^32`
    const MU: u32 = 0x8800_0001;
    const L: usize = 16;

    pub(super) struct Wide;

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn ld(x: &[F]) -> __m512i {
        unsafe { _mm512_loadu_si512(x.as_ptr() as *const __m512i) }
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn st(x: &mut [F], v: __m512i) {
        unsafe { _mm512_storeu_si512(x.as_mut_ptr() as *mut __m512i, v) }
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn splat(x: F) -> __m512i {
        // F is the Montgomery-form u32 (`repr(transparent)`)
        let v: u32 = unsafe { core::mem::transmute::<F, u32>(x) };
        _mm512_set1_epi32(v as i32)
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(super) unsafe fn add(a: __m512i, b: __m512i) -> __m512i {
        let t = _mm512_add_epi32(a, b);
        let u = _mm512_sub_epi32(t, _mm512_set1_epi32(P as i32));
        _mm512_min_epu32(t, u)
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(super) unsafe fn sub(a: __m512i, b: __m512i) -> __m512i {
        let t = _mm512_sub_epi32(a, b);
        let u = _mm512_add_epi32(t, _mm512_set1_epi32(P as i32));
        _mm512_min_epu32(t, u)
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn hdup(a: __m512i) -> __m512i {
        _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(a)))
    }
    /// Montgomery product `a·b·2^{-32} mod P` of canonical inputs.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(super) unsafe fn mul(a: __m512i, b: __m512i) -> __m512i {
        let p = _mm512_set1_epi32(P as i32);
        let mu = _mm512_set1_epi32(MU as i32);
        let prod_evn = _mm512_mul_epu32(a, b);
        let prod_odd = _mm512_mul_epu32(unsafe { hdup(a) }, unsafe { hdup(b) });
        let qp_evn = _mm512_mul_epu32(_mm512_mul_epu32(prod_evn, mu), p);
        let qp_odd = _mm512_mul_epu32(_mm512_mul_epu32(prod_odd, mu), p);
        // high doublewords: odd lanes from the odd products, even lanes from
        // the even products (their odd doublewords)
        const EVENS: __mmask16 = 0x5555;
        let prod_hi = _mm512_castps_si512(_mm512_mask_movehdup_ps(
            _mm512_castsi512_ps(prod_odd),
            EVENS,
            _mm512_castsi512_ps(prod_evn),
        ));
        let qp_hi = _mm512_castps_si512(_mm512_mask_movehdup_ps(
            _mm512_castsi512_ps(qp_odd),
            EVENS,
            _mm512_castsi512_ps(qp_evn),
        ));
        // prod − q·P ≡ 0 mod 2^32, so the difference is that of the highs
        let under = _mm512_cmplt_epu32_mask(prod_hi, qp_hi);
        let r = _mm512_sub_epi32(prod_hi, qp_hi);
        _mm512_mask_add_epi32(r, under, r, p)
    }

    /// Whole vectors of a row and the tail (left to [`Packed`]).
    #[inline(always)]
    fn split(n: usize) -> usize {
        n / L * L
    }

    impl Rows for Wide {
        #[inline(always)]
        fn bfly(a: &mut [F], b: &mut [F], tw: F) {
            let n = split(a.len());
            // SAFETY: only reached from `#[target_feature(enable = "avx512f")]`
            // callers (runtime-checked); in-bounds 16-element loads/stores.
            unsafe {
                let t = splat(tw);
                for i in (0..n).step_by(L) {
                    let (x, y) = (ld(&a[i..]), ld(&b[i..]));
                    st(&mut a[i..], add(x, y));
                    st(&mut b[i..], mul(sub(x, y), t));
                }
            }
            Packed::bfly(&mut a[n..], &mut b[n..], tw);
        }
        #[inline(always)]
        fn bfly1(a: &mut [F], b: &mut [F]) {
            let n = split(a.len());
            // SAFETY: as above.
            unsafe {
                for i in (0..n).step_by(L) {
                    let (x, y) = (ld(&a[i..]), ld(&b[i..]));
                    st(&mut a[i..], add(x, y));
                    st(&mut b[i..], sub(x, y));
                }
            }
            Packed::bfly1(&mut a[n..], &mut b[n..]);
        }
        #[inline(always)]
        fn bfly_dit(a: &mut [F], b: &mut [F], tw: F) {
            let n = split(a.len());
            // SAFETY: as above.
            unsafe {
                let t = splat(tw);
                for i in (0..n).step_by(L) {
                    let (x, y) = (ld(&a[i..]), ld(&b[i..]));
                    let m = mul(y, t);
                    st(&mut a[i..], add(x, m));
                    st(&mut b[i..], sub(x, m));
                }
            }
            Packed::bfly_dit(&mut a[n..], &mut b[n..], tw);
        }
        #[inline(always)]
        fn scale_into(dst: &mut [F], src: &[F], k: F) {
            let n = split(dst.len());
            // SAFETY: as above.
            unsafe {
                let kv = splat(k);
                for i in (0..n).step_by(L) {
                    st(&mut dst[i..], mul(ld(&src[i..]), kv));
                }
            }
            Packed::scale_into(&mut dst[n..], &src[n..], k);
        }
        #[inline(always)]
        fn scale(x: &mut [F], k: F) {
            let n = split(x.len());
            // SAFETY: as above.
            unsafe {
                let kv = splat(k);
                for i in (0..n).step_by(L) {
                    let v = ld(&x[i..]);
                    st(&mut x[i..], mul(v, kv));
                }
            }
            Packed::scale(&mut x[n..], k);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use p3_field::{PrimeCharacteristicRing, PrimeField32};

        #[test]
        fn ops_match_field() {
            if !std::arch::is_x86_feature_detected!("avx512f") {
                return;
            }
            let vals: Vec<F> = (0..4096u64)
                .map(|i| match i % 7 {
                    0 => F::ZERO,
                    1 => F::NEG_ONE,
                    2 => F::from_u64(i),
                    _ => F::from_u64(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 33),
                })
                .collect();
            for ch in vals.chunks(32) {
                let (x, y) = (&ch[..16], &ch[16..]);
                // SAFETY: AVX-512F checked above.
                let (s, d, m) = unsafe {
                    let (a, b) = (ld(x), ld(y));
                    let mut o = [[F::ZERO; 16]; 3];
                    st(&mut o[0], add(a, b));
                    st(&mut o[1], sub(a, b));
                    st(&mut o[2], mul(a, b));
                    (o[0], o[1], o[2])
                };
                for i in 0..16 {
                    assert_eq!(s[i], x[i] + y[i]);
                    assert_eq!(d[i], x[i] - y[i]);
                    assert_eq!(m[i], x[i] * y[i]);
                    assert!(m[i].as_canonical_u32() < P);
                }
            }
        }
    }
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
    use p3_matrix::Matrix;
    use p3_matrix::bitrev::BitReversibleMatrix;
    use p3_matrix::dense::RowMajorMatrix;

    /// `eval_range` (which uses `CosetDft` for ranges of `≥ 2^10` positions,
    /// after folding for sub-block ranges) against a full Plonky3 LDE.
    #[test]
    fn eval_range_large_matches_full_lde() {
        let dft = Dft::default();
        let (h, w) = (12usize, 9usize);
        let t = 1usize << h;
        let vals: Vec<F> = (0..(t * w) as u64)
            .map(|i| F::from_u64(i.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 35))
            .collect();
        let m = RowMajorMatrix::new(vals, w);
        let co = dft.idft_batch(m.clone());
        let sh = shift().exp_power_of_2(1);
        let full = dft
            .coset_lde_batch(m, 4, sh)
            .bit_reverse_rows()
            .to_row_major_matrix();
        let l = h + 4;
        for (p0, len) in [
            (0usize, 1usize << 10),
            (3 << 10, 1 << 10),
            (5 << 11, 1 << 11),
            (7 * t, t),
            (2 * t, 2 * t),
        ] {
            let e = eval_range(&dft, &co, l, sh, p0, len, None);
            assert_eq!(
                e.values,
                full.values[p0 * w..(p0 + len) * w],
                "p0 {p0} len {len}"
            );
        }
    }

    /// `eval_ranges` (8-chunk delayed-reduction fold) against `eval_range`.
    #[test]
    fn eval_ranges_matches_eval_range() {
        let dft = Dft::default();
        for (h, w, len) in [
            (12usize, 9usize, 64usize),
            (10, 8, 64),
            (11, 3, 16),
            (9, 5, 32),
        ] {
            let t = 1usize << h;
            let vals: Vec<F> = (0..(t * w) as u64)
                .map(|i| F::from_u64(i.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 35))
                .collect();
            let co = dft.idft_batch(RowMajorMatrix::new(vals, w));
            let l = h + 4;
            let sh = shift().exp_power_of_2(3);
            let p0s: Vec<usize> = [0usize, 5, 77, 200, 1000, 15 * t / len]
                .iter()
                .map(|&g| (g % (16 * t / len)) * len)
                .collect();
            let got = crate::lowmem::eval_ranges(&dft, &co, l, sh, &p0s, len);
            for (p0, e) in p0s.iter().zip(&got) {
                let want = eval_range(&dft, &co, l, sh, *p0, len, None);
                assert_eq!(e.values, want.values, "h {h} w {w} len {len} p0 {p0}");
            }
        }
    }

    /// The AVX-512 backend gives the same transforms as the packed one.
    #[test]
    #[cfg(target_arch = "x86_64")]
    fn wide_backend_matches_packed() {
        if !std::arch::is_x86_feature_detected!("avx512f") {
            return;
        }
        for (n, w) in [(10usize, 32usize), (11, 13), (12, 64), (10, 40), (9, 7)] {
            let t = 1usize << n;
            let src: Vec<F> = (0..(t * w) as u64)
                .map(|i| F::from_u64(i.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 35))
                .collect();
            let cd = CosetDft::new(n);
            let c = shift() * omega(n + 4).exp_u64(3);
            let (mut a, mut b) = (src.clone(), src.clone());
            let (mut ta, mut tb) = (vec![F::ZERO; 1], vec![F::ZERO; 1]);
            let _ = (&mut ta, &mut tb);
            // phase-2 / phase-A kernels on whole blocks
            let s = 1usize << (n - n / 2);
            for blk in a.chunks_mut(s * w) {
                p2_block::<Packed>(&cd, blk, w);
            }
            for blk in b.chunks_mut(s * w) {
                unsafe { p2_block_avx512(&cd, blk, w) };
            }
            assert_eq!(a, b, "p2 n {n} w {w}");
            let (mut a, mut b) = (src.clone(), src.clone());
            for blk in a.chunks_mut(s * w) {
                ia_block::<Packed>(&cd, blk, w);
            }
            for blk in b.chunks_mut(s * w) {
                unsafe { ia_block_avx512(&cd, blk, w) };
            }
            assert_eq!(a, b, "ia n {n} w {w}");
            // full transforms (dispatching to AVX-512 here) vs Plonky3
            let dft = Dft::default();
            let want = dft
                .coset_dft_batch(RowMajorMatrix::new(src.clone(), w), c)
                .bit_reverse_rows()
                .to_row_major_matrix();
            let mut got = vec![F::ZERO; t * w];
            cd.eval(&src, w, c, &mut got);
            assert_eq!(got, want.values, "eval n {n} w {w}");
            let want = dft.idft_batch(RowMajorMatrix::new(src.clone(), w));
            cd.idft(&src, w, &mut got);
            assert_eq!(got, want.values, "idft n {n} w {w}");
        }
    }

    #[test]
    fn eval_cols_matches_eval() {
        let (n, sw) = (11usize, 40usize);
        let t = 1usize << n;
        let src: Vec<F> = (0..(t * sw) as u64)
            .map(|i| F::from_u64(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 33))
            .collect();
        let cd = CosetDft::new(n);
        let c = shift() * omega(n + 4).exp_u64(5);
        for (c0, w) in [(0usize, 40usize), (3, 13), (24, 16), (39, 1)] {
            let sub: Vec<F> = (0..t)
                .flat_map(|r| src[r * sw + c0..r * sw + c0 + w].to_vec())
                .collect();
            let (mut a, mut b) = (vec![F::ZERO; t * w], vec![F::ZERO; t * w]);
            cd.eval(&sub, w, c, &mut a);
            cd.eval_cols(&src, sw, c0, w, c, &mut b);
            assert_eq!(a, b, "c0 {c0} w {w}");
        }
    }

    #[test]
    fn idft_matches_plonky3() {
        let dft = Dft::default();
        for (n, w) in [
            (0usize, 3usize),
            (1, 8),
            (2, 1),
            (3, 5),
            (6, 13),
            (9, 32),
            (10, 7),
            (11, 64),
        ] {
            let t = 1usize << n;
            let vals: Vec<F> = (0..(t * w) as u64)
                .map(|i| F::from_u64(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 33))
                .collect();
            let want = dft.idft_batch(RowMajorMatrix::new(vals.clone(), w));
            let mut got = vec![F::ZERO; t * w];
            let cd = CosetDft::new(n);
            cd.idft(&vals, w, &mut got);
            assert_eq!(got, want.values, "n {n} w {w}");
            // bit-reversed input
            let mut br = RowMajorMatrix::new(vals, w);
            p3_matrix::util::reverse_matrix_index_bits(&mut br);
            let mut got2 = vec![F::ZERO; t * w];
            cd.idft_from(&br.values, w, true, &mut got2);
            assert_eq!(got2, want.values, "bitrev n {n} w {w}");
        }
    }

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
                let c = sh * omega(l).exp_u64(rev(b, 4) as u64);
                // independent reference: Plonky3's coset DFT (bit-reversed rows)
                let want = if n == 0 {
                    eval_range(&dft, &co, l, sh, p0, t, None)
                } else {
                    dft.coset_dft_batch(co.clone(), c)
                        .bit_reverse_rows()
                        .to_row_major_matrix()
                };
                let mut got = vec![F::ZERO; t * w];
                cd.eval(&co.values, w, c, &mut got);
                assert_eq!(got, want.values, "n {n} w {w} block {b}");
            }
        }
    }
}
