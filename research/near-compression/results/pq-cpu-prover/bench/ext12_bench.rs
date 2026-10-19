//! lane/pq-cpu-prover: Ext12 arithmetic microbenchmarks (1 thread unless noted).
//!   scalar mul (p3 BinomialExtensionField<BabyBear,12> `*`), Ext12 x base, packed SoA PE mul
//!   (per element), PreMul (fixed multiplier), and a correctness cross-check of all of them.
use openvm_cpu_backend::fast::pext::{coeffs, from_coeffs, PreMul, PE};
use openvm_recursion_circuit::sha384::config::{EF, F};
use p3_field::{BasedVectorSpace, Field, PackedValue, PrimeCharacteristicRing};
use std::hint::black_box;
use std::time::Instant;

type P = <F as Field>::Packing;

fn mk(s: u32) -> EF {
    EF::from_basis_coefficients_fn(|i| F::from_u32(s.wrapping_mul(2654435761).wrapping_add(i as u32 * 97 + 1) % 2013265921))
}

fn main() {
    let w = openvm_cpu_backend::fast::detect_w::<F, EF>().expect("Ext12");
    let n = 4_000_000usize;
    // throughput: 8 independent chains
    let mut xs: Vec<EF> = (0..8).map(|i| mk(i + 1)).collect();
    let y = mk(99);
    let t = Instant::now();
    for _ in 0..n / 8 {
        for x in xs.iter_mut() {
            *x = *x * y;
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL scalar(p3 *) ns_per={:.2} ({:?})", 1e9 * s / n as f64, coeffs::<F, EF>(&black_box(xs[0]))[0]);
    // the pre-lane Ext12 patch's schoolbook (each product Montgomery-reduced, w applied per product)
    let old_mul = |a: &EF, c: &EF| -> EF {
        let (ac, cc) = (coeffs::<F, EF>(a), coeffs::<F, EF>(c));
        let mut res = [F::ZERO; 12];
        for x in 0..12 {
            for z in 0..12 {
                let pr = ac[x] * cc[z];
                if x + z < 12 { res[x + z] += pr } else { res[x + z - 12] += pr * w }
            }
        }
        from_coeffs::<F, EF>(&res)
    };
    let t = Instant::now();
    for _ in 0..n / 8 {
        for x in xs.iter_mut() {
            *x = old_mul(x, &y);
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL scalar(old schoolbook) ns_per={:.2} ({:?})", 1e9 * s / n as f64, coeffs::<F, EF>(&black_box(xs[0]))[0]);
    let b = F::from_u32(12345);
    let t = Instant::now();
    for _ in 0..n / 8 {
        for x in xs.iter_mut() {
            *x = *x * b;
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL_BASE scalar ns_per={:.2} ({:?})", 1e9 * s / n as f64, coeffs::<F, EF>(&black_box(xs[0]))[0]);
    let lanes = <P as PackedValue>::WIDTH;
    let mut ps: Vec<PE<P>> = (0..8).map(|i| PE(core::array::from_fn(|j| P::from_fn(|l| coeffs::<F, EF>(&mk((i * 100 + l) as u32 + 7))[j])))).collect();
    let py: PE<P> = PE(core::array::from_fn(|j| P::from_fn(|l| coeffs::<F, EF>(&mk(l as u32 + 1000))[j])));
    let t = Instant::now();
    let iters = n / 8 / lanes;
    for _ in 0..iters {
        for x in ps.iter_mut() {
            *x = x.mul(&py, w);
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL packed lanes={lanes} ns_per_element={:.2} ({:?})", 1e9 * s / (iters * 8 * lanes) as f64, black_box(ps[0]).lane(0)[0]);
    let pm = PreMul::<P>::new(coeffs::<F, EF>(&y), w);
    let t = Instant::now();
    for _ in 0..iters {
        for x in ps.iter_mut() {
            *x = pm.mul(x);
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL premul lanes={lanes} ns_per_element={:.2} ({:?})", 1e9 * s / (iters * 8 * lanes) as f64, black_box(ps[0]).lane(0)[0]);
    // cross-check
    let mut ok = true;
    for i in 0..1000u32 {
        let (a, c) = (mk(i), mk(i * 7 + 3));
        let r = a * c;
        let pa: PE<P> = PE::broadcast(coeffs::<F, EF>(&a));
        let pc: PE<P> = PE::broadcast(coeffs::<F, EF>(&c));
        ok &= from_coeffs::<F, EF>(&pa.mul(&pc, w).lane(lanes - 1)) == r;
        ok &= from_coeffs::<F, EF>(&PreMul::<P>::new(coeffs::<F, EF>(&c), w).mul(&pa).lane(0)) == r;
        // schoolbook reference
        let (ac, cc) = (coeffs::<F, EF>(&a), coeffs::<F, EF>(&c));
        let mut sb = [F::ZERO; 12];
        for x in 0..12 {
            for z in 0..12 {
                let pr = ac[x] * cc[z];
                if x + z < 12 { sb[x + z] += pr } else { sb[x + z - 12] += pr * w }
            }
        }
        ok &= from_coeffs::<F, EF>(&sb) == r;
    }
    println!("EXT12_CHECK {}", if ok { "ok" } else { "MISMATCH" });
    let _ = <EF as BasedVectorSpace<F>>::DIMENSION;
}
