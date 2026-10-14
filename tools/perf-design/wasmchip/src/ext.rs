//! Spike #2: cost of one logUp bus fraction at extension degree E (BabyBear, X^E - W), CPU.
//! Generic schoolbook extension over the Montgomery base field; E = 8 cross-checked against
//! Plonky3's `BinomialExtensionField<BabyBear, 8>` timing.
use npudr::field::{EF, F};
use p3_field::PrimeCharacteristicRing;
use std::time::Instant;

#[derive(Clone, Copy)]
pub struct X<const E: usize>(pub [F; E]);

impl<const E: usize> X<E> {
    #[inline]
    pub fn mul(&self, o: &Self, w: F) -> Self {
        let mut lo = [F::ZERO; E];
        let mut hi = [F::ZERO; E];
        for i in 0..E {
            for j in 0..E {
                let p = self.0[i] * o.0[j];
                if i + j < E { lo[i + j] += p } else { hi[i + j - E] += p }
            }
        }
        for k in 0..E {
            lo[k] += w * hi[k];
        }
        X(lo)
    }
    #[inline]
    pub fn add(&self, o: &Self) -> Self {
        X(std::array::from_fn(|i| self.0[i] + o.0[i]))
    }
    #[inline]
    pub fn mul_base(&self, b: F) -> Self {
        X(std::array::from_fn(|i| self.0[i] * b))
    }
}

/// One fraction, committed-logUp style: fingerprint of a 7-field message, the batched-inverse
/// share (3 ext mults), accumulation, and the aux-constraint evaluation at 2 LDE points
/// (fingerprint + 2 ext mults each).
fn frac_cost<const E: usize>(n: usize, w: F) -> f64 {
    let alpha: Vec<X<E>> = (0..8).map(|k| X(std::array::from_fn(|i| F::from_u64((k * 31 + i * 7 + 3) as u64)))).collect();
    let msgs: Vec<[F; 7]> = (0..n).map(|r| std::array::from_fn(|i| F::from_u64((r * 13 + i * 101) as u64))).collect();
    let t0 = Instant::now();
    let mut acc = X([F::ZERO; E]);
    let mut prefix = X([F::ONE; E]);
    for m in &msgs {
        // fingerprint
        let mut fp = alpha[7];
        for (i, v) in m.iter().enumerate() {
            fp = fp.add(&alpha[i].mul_base(*v));
        }
        // batched inverse share: prefix product, back-substitution (2 more mults)
        prefix = prefix.mul(&fp, w);
        let inv_share = prefix.mul(&fp, w).mul(&alpha[0], w);
        acc = acc.add(&inv_share);
        // aux constraint at 2 LDE points
        for pt in 0..2 {
            let mut g = alpha[7];
            for (i, v) in m.iter().enumerate() {
                g = g.add(&alpha[i].mul_base(*v + F::from_u64(pt)));
            }
            acc = acc.add(&g.mul(&acc, w).mul(&fp, w));
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    std::hint::black_box((acc.0[0], prefix.0[0]));
    dt / n as f64
}

fn ext_mul_cost<const E: usize>(n: usize, w: F) -> f64 {
    let mut a = X::<E>(std::array::from_fn(|i| F::from_u64(i as u64 + 5)));
    let b = X::<E>(std::array::from_fn(|i| F::from_u64(3 * i as u64 + 1)));
    let t0 = Instant::now();
    for _ in 0..n {
        a = a.mul(&b, w);
    }
    std::hint::black_box(a.0[0]);
    t0.elapsed().as_secs_f64() / n as f64
}

pub fn bench_ext() {
    let n = 2_000_000;
    // W = 11 for E = 8 (Plonky3); for E = 10 any W works for timing (a valid binomial: W must be a
    // non-residue of the right order; irrelevant to cost).
    let w = F::from_u64(11);
    let m8 = ext_mul_cost::<8>(n, w);
    let m10 = ext_mul_cost::<10>(n, w);
    let m12 = ext_mul_cost::<12>(n, w);
    let mut a = EF::from(F::from_u64(7));
    let b = npudr::field::ef_from_coeffs(&(0..8).map(|i| F::from_u64(3 * i + 1)).collect::<Vec<_>>());
    let t0 = Instant::now();
    for _ in 0..n {
        a = a * b;
    }
    std::hint::black_box(a);
    let p3 = t0.elapsed().as_secs_f64() / n as f64;
    let f8 = frac_cost::<8>(n / 4, w);
    let f10 = frac_cost::<10>(n / 4, w);
    let f12 = frac_cost::<12>(n / 4, w);
    println!(
        "bench-ext (1 thread, scalar): ext mul E=8 {:.1} ns (Plonky3 Fp8 {:.1} ns), E=10 {:.1} ns, E=12 {:.1} ns | logUp fraction compute E=8 {:.0} ns, E=10 {:.0} ns, E=12 {:.0} ns",
        m8 * 1e9, p3 * 1e9, m10 * 1e9, m12 * 1e9, f8 * 1e9, f10 * 1e9, f12 * 1e9
    );
}
