//! `cargo run --release --example ldebench -- <log_h> <width> [reps]`: one LDE block
//! (coset DFT of `2^log_h × width` coefficients) by the current `eval_range`, by
//! Plonky3's `coset_dft_batch` on a reused buffer, and by `lde::CosetDft`.
use npudr::field::{F, omega, shift};
use npudr::lde::CosetDft;
use npudr::lowmem::{Dft, eval_range};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use rayon::prelude::*;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let h: usize = a[1].parse().unwrap();
    let w: usize = a[2].parse().unwrap();
    let reps: usize = a.get(3).map(|x| x.parse().unwrap()).unwrap_or(4);
    let t = 1usize << h;
    let co = RowMajorMatrix::new(
        (0..(w << h) as u64)
            .into_par_iter()
            .map(|i| F::from_u64(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 33))
            .collect(),
        w,
    );
    let dft = Dft::default();
    let l = h + 4;
    let sh = shift();
    let c = |b: usize| sh * omega(l).exp_u64(npudr::mmcs::rev(b, 4) as u64);
    let time = |name: &str, f: &mut dyn FnMut(usize)| {
        f(0);
        let t0 = Instant::now();
        for b in 1..=reps {
            f(b);
        }
        println!(
            "{name:28} {:.3} s/block",
            t0.elapsed().as_secs_f64() / reps as f64
        );
    };
    let mut r1 = vec![];
    time("eval_range (current)", &mut |b| {
        r1 = eval_range(&dft, &co, l, sh, b * t, t, None).values;
    });
    let mut buf = vec![F::ZERO; t * w];
    time("p3 coset_dft, reused buf", &mut |b| {
        let mut v = std::mem::take(&mut buf);
        v.par_chunks_mut(1 << 16)
            .zip(co.values.par_chunks(1 << 16))
            .for_each(|(d, s)| d.copy_from_slice(s));
        let m = dft
            .coset_dft_batch(RowMajorMatrix::new(v, w), c(b))
            .bit_reverse_rows()
            .to_row_major_matrix();
        buf = m.values;
    });
    let cd = CosetDft::new(h);
    let mut dst = vec![F::ZERO; t * w];
    time("lde::CosetDft", &mut |b| {
        cd.eval(&co.values, w, c(b), &mut dst)
    });
    assert_eq!(dst, r1, "mismatch");
    let vals = co.clone();
    let mut r = None;
    time("p3 idft_batch (+clone)", &mut |_| {
        r = Some(dft.idft_batch(vals.clone()));
    });
    println!("ok");
}
