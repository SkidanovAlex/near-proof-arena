//! Spike #3: a SHA-512-family compression AIR (SHA-384 Merkle nodes = one compression each).
//!
//! Layout (per compression):
//! * `rounds`: 41 rows. Row s (0..39) performs rounds 2s and 2s+1. It holds the bits of
//!   a_{2s-2}, a_{2s-1}, a_{2s} and the limbs of a_{2s-3} (likewise e); the next row holds
//!   a_{2s}, a_{2s+1}, a_{2s+2} (2 new words per row). Row 40 holds the final state and sends it to
//!   `final`. Two rounds per row halve the copied bit-words (constraints see rows s and s+1 only).
//! * `sched`: 80 rows, the message schedule W_t as bits; σ0/σ1 travel as bus messages.
//! * `final`: 1 row, H_out = IV + state (mod 2^64 per word), the digest.
//! * `input`: the 16 message words per block (the data being hashed; not part of the cost).
//! K_t and the position flags are periodic (preprocessed in a production AIR); they are committed
//! columns here and reported separately.
use npudr::air::Air;
use npudr::field::F;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::sha512k::{IV256, IV384, K, K256};

#[derive(Clone, Copy)]
pub struct Spec {
    pub bits: usize,
    pub rounds: usize,
    pub bs0: [i64; 3],
    pub bs1: [i64; 3],
    pub ss0: [i64; 3],
    pub ss1: [i64; 3],
    pub k: &'static [u64],
    pub iv: [u64; 8],
    pub name: &'static str,
}
pub const SHA384: Spec = Spec { bits: 64, rounds: 80, bs0: [28, 34, 39], bs1: [14, 18, 41], ss0: [1, 8, 7], ss1: [19, 61, 6], k: &K, iv: IV384, name: "SHA-512 family (SHA-384 IV)" };
pub const SHA256: Spec = Spec { bits: 32, rounds: 64, bs0: [2, 13, 22], bs1: [6, 11, 25], ss0: [7, 18, 3], ss1: [17, 19, 10], k: &K256, iv: IV256, name: "SHA-256" };
use crate::v1::{TB, X, k, nx, x};

const WB: usize = 0; // schedule messages (blk, t, kind, limbs)
const INP: usize = 1; // input words (blk, t, limbs)
const FIN: usize = 2; // final state (blk, 8 words x limbs)

impl Spec {
    fn mask(&self) -> u64 {
        if self.bits == 64 { u64::MAX } else { (1u64 << self.bits) - 1 }
    }
    fn rotr(&self, v: u64, r: i64) -> u64 {
        let b = self.bits as u32;
        ((v >> r) | (v << (b - r as u32))) & self.mask()
    }
    fn big_s0(&self, a: u64) -> u64 {
        self.rotr(a, self.bs0[0]) ^ self.rotr(a, self.bs0[1]) ^ self.rotr(a, self.bs0[2])
    }
    fn big_s1(&self, e: u64) -> u64 {
        self.rotr(e, self.bs1[0]) ^ self.rotr(e, self.bs1[1]) ^ self.rotr(e, self.bs1[2])
    }
    fn s0(&self, w: u64) -> u64 {
        self.rotr(w, self.ss0[0]) ^ self.rotr(w, self.ss0[1]) ^ (w >> self.ss0[2])
    }
    fn s1(&self, w: u64) -> u64 {
        self.rotr(w, self.ss1[0]) ^ self.rotr(w, self.ss1[1]) ^ (w >> self.ss1[2])
    }
    fn add(&self, a: u64, b: u64) -> u64 {
        a.wrapping_add(b) & self.mask()
    }
    /// reference compression; a_t, e_t for t = -3..=R (index t+3), W_t, output
    fn reference(&self, m: &[u64; 16]) -> (Vec<u64>, Vec<u64>, Vec<u64>, [u64; 8]) {
        let iv = &self.iv;
        let mut w = m.to_vec();
        for t in 16..self.rounds {
            let v = self.add(self.add(self.s1(w[t - 2]), w[t - 7]), self.add(self.s0(w[t - 15]), w[t - 16]));
            w.push(v);
        }
        let mut a = vec![iv[3], iv[2], iv[1], iv[0]];
        let mut e = vec![iv[7], iv[6], iv[5], iv[4]];
        for t in 0..self.rounds {
            let i = t + 3;
            let (aa, bb, cc, dd) = (a[i], a[i - 1], a[i - 2], a[i - 3]);
            let (ee, ff, gg, hh) = (e[i], e[i - 1], e[i - 2], e[i - 3]);
            let ch = (ee & ff) ^ (!ee & gg & self.mask());
            let maj = (aa & bb) ^ (aa & cc) ^ (bb & cc);
            let t1 = self.add(self.add(self.add(hh, self.big_s1(ee)), self.add(ch, self.k[t])), w[t]);
            let t2 = self.add(self.big_s0(aa), maj);
            a.push(self.add(t1, t2));
            e.push(self.add(dd, t1));
        }
        let r = self.rounds + 3;
        let fin = [a[r], a[r - 1], a[r - 2], a[r - 3], e[r], e[r - 1], e[r - 2], e[r - 3]];
        let mut out = [0u64; 8];
        for i in 0..8 {
            out[i] = self.add(iv[i], fin[i]);
        }
        (a, e, w, out)
    }
}

type Bits = Vec<usize>;
fn bitx(cols: &Bits, i: i64, next: bool) -> X {
    if !(0..cols.len() as i64).contains(&i) {
        return k(0);
    }
    if next { nx(cols[i as usize]) } else { x(cols[i as usize]) }
}
fn xor2(a: X, b: X) -> X {
    a.clone() + b.clone() - k(2) * a * b
}
fn xor3(a: X, b: X, c: X) -> X {
    xor2(xor2(a, b), c)
}
fn limb_of(f: &dyn Fn(i64) -> X, l: usize) -> X {
    let mut acc = k(0);
    for j in 0..16 {
        acc = acc + k(1 << j) * f((16 * l + j) as i64);
    }
    acc
}
fn limbs_bits(cols: &Bits, next: bool, l: usize) -> X {
    limb_of(&|i| bitx(cols, i, next), l)
}

pub struct Built {
    pub air: Air,
    pub traces: Vec<RowMajorMatrix<F>>,
    pub nblk: usize,
    pub preprocessed: Vec<usize>,
    pub rows_per: [usize; 4],
    pub a0_col: usize,
    pub bytes_per_block: usize,
}

pub fn build(sp: Spec, nblk: usize, seed: u64) -> Built {
    let mut sp = sp;
    if let Ok(r) = std::env::var("SHA_ROUNDS") {
        sp.rounds = r.parse().unwrap();
    }
    let nb = sp.bits;
    let nl = nb / 16;
    let rr = sp.rounds / 2 + 1; // round rows per block
    let rot = |i: i64, r: i64| (i + r).rem_euclid(nb as i64);
    let bits = |tb: &mut TB, n: &str| -> Bits { (0..nb).map(|i| tb.c(&format!("{n}{i}"))).collect() };
    let lcols = |tb: &mut TB, n: &str| -> Vec<usize> { (0..nl).map(|i| tb.c(&format!("{n}{i}"))).collect() };
    // ------------------------------ rounds ------------------------------
    let mut tb = TB::new("sha_rounds");
    let blk = tb.c("blk");
    let ri = tb.c("ri");
    let isr = tb.c("is_round");
    let isf = tb.c("is_first");
    let isl = tb.c("is_last");
    let am2 = bits(&mut tb, "am2_");
    let am1 = bits(&mut tb, "am1_");
    let a0 = bits(&mut tb, "a0_");
    let ad = lcols(&mut tb, "ad");
    let em2 = bits(&mut tb, "em2_");
    let em1 = bits(&mut tb, "em1_");
    let e0 = bits(&mut tb, "e0_");
    let ed = lcols(&mut tb, "ed");
    let w0 = lcols(&mut tb, "wA");
    let w1 = lcols(&mut tb, "wB");
    let k0 = lcols(&mut tb, "kA");
    let k1 = lcols(&mut tb, "kB");
    let ca: Vec<[usize; 3]> = (0..2 * nl).map(|i| tb.cs(&format!("ca{i}_"))).collect();
    let ce: Vec<[usize; 3]> = (0..2 * nl).map(|i| tb.cs(&format!("ce{i}_"))).collect();
    let n_pre_r = 4 + 2 * nl;
    let r = x(isr);
    for c in am1.iter().chain(&a0).chain(&em1).chain(&e0).chain(&am2).chain(&em2) {
        tb.con(x(*c) * (x(*c) - k(1)));
    }
    for c in ca.iter().chain(&ce).flatten() {
        tb.con(x(*c) * (x(*c) - k(1)));
    }
    let ivb = |w: u64, cols: &Bits, tb: &mut TB| {
        for i in 0..nb {
            tb.con(x(isf) * (x(cols[i]) - k((w >> i) & 1)));
        }
    };
    ivb(sp.iv[2], &am2, &mut tb);
    ivb(sp.iv[1], &am1, &mut tb);
    ivb(sp.iv[0], &a0, &mut tb);
    ivb(sp.iv[6], &em2, &mut tb);
    ivb(sp.iv[5], &em1, &mut tb);
    ivb(sp.iv[4], &e0, &mut tb);
    for l in 0..nl {
        tb.con(x(isf) * (x(ad[l]) - k((sp.iv[3] >> (16 * l)) & 0xffff)));
        tb.con(x(isf) * (x(ed[l]) - k((sp.iv[7] >> (16 * l)) & 0xffff)));
    }
    for i in 0..nb {
        tb.con(r.clone() * (nx(am2[i]) - x(a0[i])));
        tb.con(r.clone() * (nx(em2[i]) - x(e0[i])));
    }
    for l in 0..nl {
        tb.con(r.clone() * (nx(ad[l]) - limbs_bits(&am1, false, l)));
        tb.con(r.clone() * (nx(ed[l]) - limbs_bits(&em1, false, l)));
    }
    tb.con(r.clone() * (nx(blk) - x(blk)));
    struct Rd<'a> {
        a: (&'a Bits, bool),
        b: (&'a Bits, bool),
        c: (&'a Bits, bool),
        e: (&'a Bits, bool),
        f: (&'a Bits, bool),
        g: (&'a Bits, bool),
        oa: &'a Bits,
        oe: &'a Bits,
        kk: &'a Vec<usize>,
        ww: &'a Vec<usize>,
        ci: usize,
    }
    let rounds = [
        Rd { a: (&a0, false), b: (&am1, false), c: (&am2, false), e: (&e0, false), f: (&em1, false), g: (&em2, false), oa: &am1, oe: &em1, kk: &k0, ww: &w0, ci: 0 },
        Rd { a: (&am1, true), b: (&a0, false), c: (&am1, false), e: (&em1, true), f: (&e0, false), g: (&em1, false), oa: &a0, oe: &e0, kk: &k1, ww: &w1, ci: nl },
    ];
    for (ri_, rd) in rounds.iter().enumerate() {
        for l in 0..nl {
            let d = if ri_ == 0 { x(ad[l]) } else { limbs_bits(&am2, false, l) };
            let h = if ri_ == 0 { x(ed[l]) } else { limbs_bits(&em2, false, l) };
            let (a, b, c, e, f, g) = (rd.a, rd.b, rd.c, rd.e, rd.f, rd.g);
            let sig1 = limb_of(&|i| xor3(bitx(e.0, rot(i, sp.bs1[0]), e.1), bitx(e.0, rot(i, sp.bs1[1]), e.1), bitx(e.0, rot(i, sp.bs1[2]), e.1)), l);
            let ch = limb_of(&|i| {
                let (ei, fi, gi) = (bitx(e.0, i, e.1), bitx(f.0, i, f.1), bitx(g.0, i, g.1));
                ei.clone() * fi + (k(1) - ei) * gi
            }, l);
            let sig0 = limb_of(&|i| xor3(bitx(a.0, rot(i, sp.bs0[0]), a.1), bitx(a.0, rot(i, sp.bs0[1]), a.1), bitx(a.0, rot(i, sp.bs0[2]), a.1)), l);
            let maj = limb_of(&|i| {
                let (ai, bi, ci) = (bitx(a.0, i, a.1), bitx(b.0, i, b.1), bitx(c.0, i, c.1));
                ai.clone() * bi.clone() + ai.clone() * ci.clone() + bi.clone() * ci.clone() - k(2) * ai * bi * ci
            }, l);
            let carry = |cs: &[usize; 3]| x(cs[0]) + k(2) * x(cs[1]) + k(4) * x(cs[2]);
            let cin_a = if l == 0 { k(0) } else { carry(&ca[rd.ci + l - 1]) };
            let cin_e = if l == 0 { k(0) } else { carry(&ce[rd.ci + l - 1]) };
            let t1 = h + sig1 + ch + x(rd.kk[l]) + x(rd.ww[l]);
            let na = limbs_bits(rd.oa, true, l);
            let ne = limbs_bits(rd.oe, true, l);
            tb.con(r.clone() * (t1.clone() + sig0 + maj + cin_a - na - k(65536) * carry(&ca[rd.ci + l])));
            tb.con(r.clone() * (t1 + d + cin_e - ne - k(65536) * carry(&ce[rd.ci + l])));
        }
    }
    for (j, ww) in [&w0, &w1].iter().enumerate() {
        let mut m = vec![x(blk), k(2) * x(ri) + k(j as u64), k(0)];
        m.extend(ww.iter().map(|c| x(*c)));
        tb.int(WB, false, vec![x(isr)], m);
    }
    {
        let mut m = vec![x(blk)];
        for cols in [&a0, &am1, &am2] {
            for l in 0..nl {
                m.push(limbs_bits(cols, false, l));
            }
        }
        m.extend(ad.iter().map(|c| x(*c)));
        for cols in [&e0, &em1, &em2] {
            for l in 0..nl {
                m.push(limbs_bits(cols, false, l));
            }
        }
        m.extend(ed.iter().map(|c| x(*c)));
        tb.int(FIN, true, vec![x(isl)], m);
    }
    let rounds_t = tb.table();
    // ------------------------------ schedule ------------------------------
    let mut ts = TB::new("sha_sched");
    let sact = ts.c("act");
    let sblk = ts.c("blk");
    let st = ts.c("t");
    let isin = ts.c("is_input");
    let us0 = ts.c("use_s0");
    let us1 = ts.c("use_s1");
    let m0 = ts.c("mw0");
    let m1 = ts.c("mw1");
    let wb = bits(&mut ts, "w_");
    let rs1 = lcols(&mut ts, "rs1_");
    let rw7 = lcols(&mut ts, "rw7_");
    let rs0 = lcols(&mut ts, "rs0_");
    let rw16 = lcols(&mut ts, "rw16_");
    let sc: Vec<[usize; 2]> = (0..nl).map(|i| ts.cs(&format!("sc{i}_"))).collect();
    // σ0/σ1 of W_t as committed limbs (linear bus messages, table degree 4 instead of 6)
    let s0c = lcols(&mut ts, "s0c_");
    let s1c = lcols(&mut ts, "s1c_");
    let n_pre_s = 6;
    for c in wb.iter().chain(sc.iter().flatten()) {
        ts.con(x(*c) * (x(*c) - k(1)));
    }
    let nin = x(sact) - x(isin);
    for l in 0..nl {
        let carry = |cs: &[usize; 2]| x(cs[0]) + k(2) * x(cs[1]);
        let cin = if l == 0 { k(0) } else { carry(&sc[l - 1]) };
        ts.con(nin.clone() * (x(rs1[l]) + x(rw7[l]) + x(rs0[l]) + x(rw16[l]) + cin - limbs_bits(&wb, false, l) - k(65536) * carry(&sc[l])));
    }
    let wl: Vec<X> = (0..nl).map(|l| limbs_bits(&wb, false, l)).collect();
    let mut m = vec![x(sblk), x(st), k(0)];
    m.extend(wl.clone());
    ts.int(WB, true, vec![x(m0), x(m1)], m);
    for l in 0..nl {
        let e0 = limb_of(&|i| xor3(bitx(&wb, rot(i, sp.ss0[0]), false), bitx(&wb, rot(i, sp.ss0[1]), false), bitx(&wb, i + sp.ss0[2], false)), l);
        let e1 = limb_of(&|i| xor3(bitx(&wb, rot(i, sp.ss1[0]), false), bitx(&wb, rot(i, sp.ss1[1]), false), bitx(&wb, i + sp.ss1[2], false)), l);
        ts.con(x(s0c[l]) - e0);
        ts.con(x(s1c[l]) - e1);
    }
    let mut m = vec![x(sblk), x(st), k(1)];
    m.extend(s0c.iter().map(|c| x(*c)));
    ts.int(WB, true, vec![x(us0)], m);
    let mut m = vec![x(sblk), x(st), k(2)];
    m.extend(s1c.iter().map(|c| x(*c)));
    ts.int(WB, true, vec![x(us1)], m);
    for (cols, dt, kind) in [(&rs1, 2u64, 2u64), (&rw7, 7, 0), (&rs0, 15, 1), (&rw16, 16, 0)] {
        let mut m = vec![x(sblk), x(st) - k(dt), k(kind)];
        m.extend(cols.iter().map(|c| x(*c)));
        ts.int(WB, false, vec![nin.clone()], m);
    }
    let mut m = vec![x(sblk), x(st)];
    m.extend(wl);
    ts.int(INP, false, vec![x(isin)], m);
    let sched_t = ts.table();
    // ------------------------------ final ------------------------------
    let mut tf = TB::new("sha_final");
    let fact = tf.c("act");
    let fb = tf.c("blk");
    let fw: Vec<Vec<usize>> = (0..8).map(|i| lcols(&mut tf, &format!("s{i}_"))).collect();
    let fo: Vec<Vec<usize>> = (0..8).map(|i| lcols(&mut tf, &format!("o{i}_"))).collect();
    let fc: Vec<Vec<usize>> = (0..8).map(|i| lcols(&mut tf, &format!("c{i}_"))).collect();
    let mut m = vec![x(fb)];
    for wd in &fw {
        m.extend(wd.iter().map(|c| x(*c)));
    }
    tf.int(FIN, false, vec![x(fact)], m);
    for i in 0..8 {
        for l in 0..nl {
            let cin = if l == 0 { k(0) } else { x(fc[i][l - 1]) };
            tf.con(x(fact) * (x(fw[i][l]) + k((sp.iv[i] >> (16 * l)) & 0xffff) + cin - x(fo[i][l]) - k(65536) * x(fc[i][l])));
            tf.con(x(fc[i][l]) * (x(fc[i][l]) - k(1)));
        }
    }
    let final_t = tf.table();
    // ------------------------------ input ------------------------------
    let mut ti = TB::new("sha_input");
    let iact = ti.c("act");
    let ib = ti.c("blk");
    let it = ti.c("t");
    let iw = lcols(&mut ti, "w");
    let mut m = vec![x(ib), x(it)];
    m.extend(iw.iter().map(|c| x(*c)));
    ti.int(INP, true, vec![x(iact)], m);
    let input_t = ti.table();
    // ------------------------------ traces ------------------------------
    let pad = |n: usize| n.max(4).next_power_of_two();
    let rs = sp.rounds;
    let (wr, ws, wf, wi) = (rounds_t.width, sched_t.width, final_t.width, input_t.width);
    let (hr, hs, hf, hi) = (pad(rr * nblk), pad(rs * nblk), pad(nblk), pad(16 * nblk));
    let mut vr = vec![F::ZERO; wr * hr];
    let mut vs = vec![F::ZERO; ws * hs];
    let mut vf = vec![F::ZERO; wf * hf];
    let mut vi = vec![F::ZERO; wi * hi];
    let mut rng = seed;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng & sp.mask()
    };
    let setb = |row: &mut [F], cols: &Bits, v: u64| {
        for i in 0..cols.len() {
            row[cols[i]] = F::from_u64((v >> i) & 1);
        }
    };
    let setl = |row: &mut [F], cols: &[usize], v: u64| {
        for (l, c) in cols.iter().enumerate() {
            row[*c] = F::from_u64((v >> (16 * l)) & 0xffff);
        }
    };
    for b in 0..nblk {
        let msg: [u64; 16] = std::array::from_fn(|_| next());
        let (a, e, w, out) = sp.reference(&msg);
        if sp.rounds != 64 && sp.rounds != 80 {
        } else if nb == 64 {
            let mut hst: [u64; 8] = sp.iv;
            let mut block = [0u8; 128];
            for (i, wd) in msg.iter().enumerate() {
                block[8 * i..8 * i + 8].copy_from_slice(&wd.to_be_bytes());
            }
            sha2::compress512(&mut hst, &[block.into()]);
            assert_eq!(hst, out, "reference disagrees with sha2::compress512");
        } else {
            let mut hst: [u32; 8] = sp.iv.map(|v| v as u32);
            let mut block = [0u8; 64];
            for (i, wd) in msg.iter().enumerate() {
                block[4 * i..4 * i + 4].copy_from_slice(&(*wd as u32).to_be_bytes());
            }
            sha2::compress256(&mut hst, &[block.into()]);
            assert_eq!(hst.map(|v| v as u64), out, "reference disagrees with sha2::compress256");
        }
        let at = |t: i64| a[(t + 3) as usize];
        let et = |t: i64| e[(t + 3) as usize];
        for s in 0..rr {
            let row = &mut vr[(rr * b + s) * wr..(rr * b + s + 1) * wr];
            let t0 = 2 * s as i64;
            row[blk] = F::from_usize(b);
            row[ri] = F::from_usize(s);
            row[isr] = F::from_bool(s + 1 < rr);
            row[isf] = F::from_bool(s == 0);
            row[isl] = F::from_bool(s + 1 == rr);
            setb(row, &am2, at(t0 - 2));
            setb(row, &am1, at(t0 - 1));
            setb(row, &a0, at(t0));
            setl(row, &ad, at(t0 - 3));
            setb(row, &em2, et(t0 - 2));
            setb(row, &em1, et(t0 - 1));
            setb(row, &e0, et(t0));
            setl(row, &ed, et(t0 - 3));
            if s + 1 < rr {
                for (j, (ww, kk)) in [(&w0, &k0), (&w1, &k1)].iter().enumerate() {
                    let t = 2 * s + j;
                    setl(row, ww, w[t]);
                    setl(row, kk, sp.k[t]);
                    let (aa, bb, cc, dd) = (at(t as i64), at(t as i64 - 1), at(t as i64 - 2), at(t as i64 - 3));
                    let (ee, ff, gg, hh) = (et(t as i64), et(t as i64 - 1), et(t as i64 - 2), et(t as i64 - 3));
                    let ch = (ee & ff) ^ (!ee & gg & sp.mask());
                    let maj = (aa & bb) ^ (aa & cc) ^ (bb & cc);
                    let terms_a = [hh, sp.big_s1(ee), ch, sp.k[t], w[t], sp.big_s0(aa), maj];
                    let terms_e = [hh, sp.big_s1(ee), ch, sp.k[t], w[t], dd];
                    for (terms, cs) in [(&terms_a[..], &ca), (&terms_e[..], &ce)] {
                        let mut carry = 0u64;
                        for l in 0..nl {
                            let sm: u64 = terms.iter().map(|v| (v >> (16 * l)) & 0xffff).sum::<u64>() + carry;
                            carry = sm >> 16;
                            for q in 0..3 {
                                row[cs[nl * j + l][q]] = F::from_u64((carry >> q) & 1);
                            }
                        }
                    }
                }
            }
        }
        for t in 0..rs {
            let row = &mut vs[(rs * b + t) * ws..(rs * b + t + 1) * ws];
            row[sact] = F::ONE;
            row[sblk] = F::from_usize(b);
            row[st] = F::from_usize(t);
            row[isin] = F::from_bool(t < 16);
            row[us0] = F::from_bool(t + 15 >= 16 && t + 15 < rs);
            row[us1] = F::from_bool(t + 2 >= 16 && t + 2 < rs);
            let mult = 1 + (t + 7 >= 16 && t + 7 < rs) as u64 + (t + 16 < rs) as u64;
            row[m0] = F::from_u64(mult & 1);
            row[m1] = F::from_u64(mult >> 1);
            setb(row, &wb, w[t]);
            setl(row, &s0c, sp.s0(w[t]));
            setl(row, &s1c, sp.s1(w[t]));
            if t >= 16 {
                let terms = [sp.s1(w[t - 2]), w[t - 7], sp.s0(w[t - 15]), w[t - 16]];
                setl(row, &rs1, terms[0]);
                setl(row, &rw7, terms[1]);
                setl(row, &rs0, terms[2]);
                setl(row, &rw16, terms[3]);
                let mut carry = 0u64;
                for l in 0..nl {
                    let sm: u64 = terms.iter().map(|v| (v >> (16 * l)) & 0xffff).sum::<u64>() + carry;
                    carry = sm >> 16;
                    row[sc[l][0]] = F::from_u64(carry & 1);
                    row[sc[l][1]] = F::from_u64(carry >> 1);
                }
            }
        }
        {
            let row = &mut vf[b * wf..(b + 1) * wf];
            row[fact] = F::ONE;
            row[fb] = F::from_usize(b);
            let q = rs + 3;
            let fin = [a[q], a[q - 1], a[q - 2], a[q - 3], e[q], e[q - 1], e[q - 2], e[q - 3]];
            for i in 0..8 {
                setl(row, &fw[i], fin[i]);
                setl(row, &fo[i], out[i]);
                let mut carry = 0u64;
                for l in 0..nl {
                    let sm = ((fin[i] >> (16 * l)) & 0xffff) + ((sp.iv[i] >> (16 * l)) & 0xffff) + carry;
                    carry = sm >> 16;
                    row[fc[i][l]] = F::from_u64(carry);
                }
            }
        }
        for t in 0..16 {
            let row = &mut vi[(16 * b + t) * wi..(16 * b + t + 1) * wi];
            row[iact] = F::ONE;
            row[ib] = F::from_usize(b);
            row[it] = F::from_usize(t);
            setl(row, &iw, msg[t]);
        }
    }
    let air = Air::v1(vec![rounds_t, sched_t, final_t, input_t], 3, 0);
    Built {
        air,
        traces: vec![RowMajorMatrix::new(vr, wr), RowMajorMatrix::new(vs, ws), RowMajorMatrix::new(vf, wf), RowMajorMatrix::new(vi, wi)],
        nblk,
        preprocessed: vec![n_pre_r, n_pre_s],
        rows_per: [rr, rs, 1, 16],
        a0_col: a0[7],
        bytes_per_block: 2 * nb,
    }
}
