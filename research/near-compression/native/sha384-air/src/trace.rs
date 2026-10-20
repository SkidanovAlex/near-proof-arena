//! Trace generation for the packed-digit SHA-512 compression AIR, plus a native
//! reference round function checked against `sha2::compress512`.
use crate::air::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Comp {
    pub h: [u64; 8],
    pub block: [u64; 16],
}

pub const SHA384_IV: [u64; 8] = [
    0xcbbb9d5dc1059ed8,
    0x629a292a367cd507,
    0x9159015a3070dd17,
    0x152fecd8f70e5939,
    0x67332667ffc00b31,
    0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7,
    0x47b5481dbefa4fa4,
];
pub const SHA512_IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// Reference: sha2 crate compression.
pub fn sha2_compress(c: &Comp) -> [u64; 8] {
    let mut st = c.h;
    let bytes: Vec<u8> = c.block.iter().flat_map(|w| w.to_be_bytes()).collect();
    let blk = sha2::digest::generic_array::GenericArray::clone_from_slice(&bytes);
    sha2::compress512(&mut st, &[blk]);
    st
}

/// Message padding (FIPS 180-4 §5.1.2) into 1024-bit blocks.
pub fn pad_message(msg: &[u8]) -> Vec<[u64; 16]> {
    let mut m = msg.to_vec();
    m.push(0x80);
    while m.len() % 128 != 112 {
        m.push(0);
    }
    m.extend_from_slice(&(0u64).to_be_bytes());
    m.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    m.chunks(128)
        .map(|ch| {
            std::array::from_fn(|i| u64::from_be_bytes(ch[8 * i..8 * i + 8].try_into().unwrap()))
        })
        .collect()
}

pub fn bsig0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}
pub fn bsig1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}
pub fn ssig0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}
pub fn ssig1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}
pub fn chf(e: u64, f: u64, g: u64) -> u64 {
    (e & f) ^ (!e & g)
}
pub fn majf(a: u64, b: u64, c: u64) -> u64 {
    (a & b) ^ (a & c) ^ (b & c)
}

/// Words of one compression: a[-4..80), e[-4..80) (index +4), W[0..80), output.
pub struct Words {
    pub a: [u64; 84],
    pub e: [u64; 84],
    pub w: [u64; 80],
    pub out: [u64; 8],
}
pub fn round_words(c: &Comp) -> Words {
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(&c.block);
    for t in 16..80 {
        w[t] = ssig1(w[t - 2])
            .wrapping_add(w[t - 7])
            .wrapping_add(ssig0(w[t - 15]))
            .wrapping_add(w[t - 16]);
    }
    let mut a = [0u64; 84];
    let mut e = [0u64; 84];
    for k in 0..4 {
        a[3 - k] = c.h[k]; // a[-1] = H0 ... a[-4] = H3
        e[3 - k] = c.h[4 + k];
    }
    for t in 0..80 {
        let i = t + 4;
        let t1 = e[i - 4]
            .wrapping_add(bsig1(e[i - 1]))
            .wrapping_add(chf(e[i - 1], e[i - 2], e[i - 3]))
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let t2 = bsig0(a[i - 1]).wrapping_add(majf(a[i - 1], a[i - 2], a[i - 3]));
        a[i] = t1.wrapping_add(t2);
        e[i] = a[i - 4].wrapping_add(t1);
    }
    let mut out = [0u64; 8];
    for k in 0..4 {
        out[k] = c.h[k].wrapping_add(a[83 - k]);
        out[4 + k] = c.h[4 + k].wrapping_add(e[83 - k]);
    }
    Words { a, e, w, out }
}

pub struct Traces {
    pub lay: Layout,
    pub main: Vec<u32>,
    pub main_height: usize,
    pub table: Vec<u32>,
    pub harness: Vec<u32>,
    pub harness_height: usize,
}

pub fn main_height(n: usize) -> usize {
    (n * ROWS).next_power_of_two().max(4)
}

type L3 = [i64; 3];
fn sum3(xs: &[L3]) -> L3 {
    std::array::from_fn(|i| xs.iter().map(|x| x[i]).sum())
}
fn neg3(x: L3) -> L3 {
    std::array::from_fn(|i| -x[i])
}

struct Gen<'a> {
    lay: Layout,
    t: &'a mut [u32],
}
impl Gen<'_> {
    fn row(&self, gi: usize) -> &[u32] {
        &self.t[gi * self.lay.width..(gi + 1) * self.lay.width]
    }
    fn put_word(&mut self, gi: usize, base: usize, x: u64) {
        let w = self.lay.width;
        for (j, d) in self.lay.digits(x).into_iter().enumerate() {
            self.t[gi * w + base + j] = d as u32;
        }
    }
    fn get_word(&self, gi: usize, base: usize) -> u64 {
        let row = self.row(gi);
        (0..self.lay.nd).fold(0u64, |acc, j| acc | ((row[base + j] as u64) << (self.lay.k * j)))
    }
    fn l3(&self, x: u64) -> L3 {
        self.lay.limbs(x).map(|v| v as i64)
    }
    fn get3(&self, gi: usize, c: usize) -> L3 {
        let row = self.row(gi);
        std::array::from_fn(|i| row[c + i] as i64)
    }
    fn put3(&mut self, gi: usize, c: usize, v: L3) {
        let w = self.lay.width;
        for i in 0..3 {
            assert!(v[i] >= 0 && v[i] < (1 << 30), "value out of range: {v:?}");
            self.t[gi * w + c + i] = v[i] as u32;
        }
    }
    /// Carries for out_i + 2^{w_i} c_i - c_{i-1} = rhs_i, stored with offset `off`.
    fn carries(&self, out: u64, rhs: L3, off: i64) -> L3 {
        let ol = self.l3(out);
        let mut c = [0i64; 3];
        let mut prev = 0i64;
        for i in 0..3 {
            let w = self.lay.lw(i) as i64;
            let v = rhs[i] + prev - ol[i];
            assert_eq!(v.rem_euclid(1 << w), 0, "limb mismatch");
            c[i] = v >> w;
            prev = c[i];
            assert!((0..CARRY_RANGE as i64).contains(&(c[i] + off)), "carry {} off {off}", c[i]);
        }
        c.map(|x| x + off)
    }
}

/// Main trace (row-major).  `height` >= n*ROWS, a power of two.
pub fn gen_main(lay: Layout, comps: &[Comp], height: usize) -> Vec<u32> {
    assert!(height >= comps.len() * ROWS && height.is_power_of_two());
    let w = lay.width;
    let mut t = vec![0u32; height * w];
    let mut gn = Gen { lay, t: &mut t };
    // Pass 1: r, g, flags on real rows; padding rows stay all zero.
    for gi in 0..comps.len() * ROWS {
        let r = gi % ROWS;
        let e = ctl_entry(r);
        gn.t[gi * w + lay.r] = r as u32;
        gn.t[gi * w + lay.g] = gi as u32;
        for f in 0..NFLAGS {
            gn.t[gi * w + lay.flags + f] = e[1 + f] as u32;
        }
    }
    // Pass 2: word digits.
    let words: Vec<Words> = comps.iter().map(round_words).collect();
    for (s, wd) in words.iter().enumerate() {
        let base = s * ROWS;
        for r in 0..ROWS {
            let gi = base + r;
            let (sa, se): ([u64; 2], [u64; 2]) = if r < 42 {
                ([wd.a[2 * r], wd.a[2 * r + 1]], [wd.e[2 * r], wd.e[2 * r + 1]])
            } else {
                ([wd.out[1], wd.out[0]], [wd.out[5], wd.out[4]])
            };
            gn.put_word(gi, lay.a0, sa[0]);
            gn.put_word(gi, lay.a1, sa[1]);
            gn.put_word(gi, lay.e0, se[0]);
            gn.put_word(gi, lay.e1, se[1]);
            if (2..42).contains(&r) {
                gn.put_word(gi, lay.w0, wd.w[2 * r - 4]);
                gn.put_word(gi, lay.w1, wd.w[2 * r - 3]);
            } else if r < 2 {
                // output pairs (H'2, H'3) on row 0 and (H'6, H'7) on row 1
                gn.put_word(gi, lay.w0, wd.out[2 + 4 * r]);
                gn.put_word(gi, lay.w1, wd.out[3 + 4 * r]);
            }
        }
    }
    // Pass 3: S and DE on every row, cyclically, from (previous row, row); h, Ch and DE
    // are gated by is_real(row), so rows after the last real row stay zero.
    let nreal = comps.len() * ROWS;
    for gi in 0..height {
        let rl = (gi < nreal) as i64;
        let p = (gi + height - 1) % height;
        let gw = |gn: &Gen, r: usize, b: usize| gn.get_word(r, b);
        let (a1l, e0l, e1l) = (gw(&gn, p, lay.a1), gw(&gn, p, lay.e0), gw(&gn, p, lay.e1));
        let (a0n, a1n, e0n, e1n) = (
            gw(&gn, gi, lay.a0),
            gw(&gn, gi, lay.a1),
            gw(&gn, gi, lay.e0),
            gw(&gn, gi, lay.e1),
        );
        let hc = sum3(&[gn.l3(e0l), gn.l3(chf(e1n, e0n, e1l))]).map(|v| v * rl);
        let sa = sum3(&[hc, gn.l3(bsig1(e1n)), gn.l3(bsig0(a1n)), gn.l3(majf(a1n, a0n, a1l))]);
        let de = gn.l3(e1l).map(|v| v * rl);
        gn.put3(gi, lay.sa, sa);
        gn.put3(gi, lay.de, de);
    }
    // Pass 4: carries and received values on row x, for the additions of row x+1.
    for (s, wd) in words.iter().enumerate() {
        let base = s * ROWS;
        for x in base..base + ROWS {
            let n = x + 1;
            let rn = n - base; // segment row of x+1 (44 = next segment)
            if (2..42).contains(&rn) {
                let get = |b: usize, gi: usize| gn.get_word(gi, b);
                let (a0l, a1l, e0l, e1l) =
                    (get(lay.a0, x), get(lay.a1, x), get(lay.e0, x), get(lay.e1, x));
                let (a0n, a1n, e0n, e1n) =
                    (get(lay.a0, n), get(lay.a1, n), get(lay.e0, n), get(lay.e1, n));
                let (w0n, w1n) = (get(lay.w0, n), get(lay.w1, n));
                let (sa, de) = (gn.get3(x, lay.sa), gn.get3(x, lay.de));
                // d - T2 for slot 0, from rows x-1 and x
                let a1x = get(lay.a1, x - 1);
                let d0 = get(lay.a0, x - 1);
                let dmt2 = sum3(&[
                    gn.l3(d0),
                    neg3(gn.l3(bsig0(a1l))),
                    neg3(gn.l3(majf(a1l, a0l, a1x))),
                ]);
                let k0 = gn.l3(K[2 * rn - 4]);
                let k1 = gn.l3(K[2 * rn - 3]);
                // slot 0
                let c0a = gn.carries(a0n, sum3(&[sa, gn.l3(w0n), k0]), 0);
                let c0e = gn.carries(e0n, sum3(&[gn.l3(a0n), dmt2]), CARRY_OFF);
                // slot 1
                let t2 = sum3(&[gn.l3(bsig0(a0n)), gn.l3(majf(a0n, a1l, a0l))]);
                let t1 = sum3(&[
                    de,
                    gn.l3(bsig1(e0n)),
                    gn.l3(chf(e0n, e1l, e0l)),
                    k1,
                    gn.l3(w1n),
                ]);
                let c1a = gn.carries(a1n, sum3(&[t1, t2]), 0);
                let d = gn.get_word(x - 1, lay.a1);
                let c1e = gn.carries(e1n, sum3(&[gn.l3(a1n), neg3(t2), gn.l3(d)]), CARRY_OFF);
                gn.put3(x, lay.c0a, c0a);
                gn.put3(x, lay.c0e, c0e);
                gn.put3(x, lay.c1a, c1a);
                gn.put3(x, lay.c1e, c1e);
                if rn >= 10 {
                    let tw = |t: usize| wd.w[t];
                    let t0 = 2 * rn - 4;
                    let v0 = sum3(&[gn.l3(tw(t0 - 16)), gn.l3(ssig0(tw(t0 - 15)))]);
                    let v1 = sum3(&[gn.l3(tw(t0 - 15)), gn.l3(ssig0(tw(t0 - 14)))]);
                    let cw0 = gn.carries(
                        tw(t0),
                        sum3(&[gn.l3(ssig1(tw(t0 - 2))), v0, gn.l3(tw(t0 - 7))]),
                        0,
                    );
                    let cw1 = gn.carries(
                        tw(t0 + 1),
                        sum3(&[gn.l3(ssig1(tw(t0 - 1))), v1, gn.l3(tw(t0 - 6))]),
                        0,
                    );
                    gn.put3(x, lay.v0, v0);
                    gn.put3(x, lay.v1, v1);
                    gn.put3(x, lay.cw0, cw0);
                    gn.put3(x, lay.cw1, cw1);
                }
            } else if rn == 42 {
                // feed-forward on row 42: slot q = IV word q (row 1) + final word q (row 41)
                let fin = [wd.a[82], wd.a[83], wd.e[82], wd.e[83]];
                let carries = [lay.c0a, lay.c1a, lay.c0e, lay.c1e];
                for (q, &slot) in lay.slots().iter().enumerate() {
                    let iv = gn.get_word(base + 1, slot);
                    let out = gn.get_word(n, slot);
                    assert_eq!(out, iv.wrapping_add(fin[q]));
                    let c = gn.carries(out, sum3(&[gn.l3(iv), gn.l3(fin[q])]), 0);
                    gn.put3(x, carries[q], c);
                }
            } else if rn == 1 {
                // feed-forward into the W slots of rows 0 and 1, carries on row 0:
                // (output row, slot, IV slot of row 0, final word, carry columns)
                let cases = [
                    (x, lay.w0, lay.a1, wd.a[81], lay.c0a), // H'2 = H2 + a_77
                    (x, lay.w1, lay.a0, wd.a[80], lay.c1a), // H'3 = H3 + a_76
                    (n, lay.w0, lay.e1, wd.e[81], lay.c0e), // H'6 = H6 + e_77
                    (n, lay.w1, lay.e0, wd.e[80], lay.c1e), // H'7 = H7 + e_76
                ];
                for (orow, oslot, islot, fin, cc) in cases {
                    let iv = gn.get_word(x, islot);
                    let out = gn.get_word(orow, oslot);
                    assert_eq!(out, iv.wrapping_add(fin));
                    let c = gn.carries(out, sum3(&[gn.l3(iv), gn.l3(fin)]), 0);
                    gn.put3(x, cc, c);
                }
            }
        }
    }
    t
}

/// Table trace (64 rows) with multiplicities counted from the main trace.
pub fn gen_table(lay: &Layout, main: &[u32], height: usize) -> Vec<u32> {
    let w = lay.width;
    let mut t = vec![0u32; 64 * T_WIDTH];
    for i in 0..64 {
        let e = table_index(i);
        t[i * T_WIDTH + T_U + e % 4] = 1;
        t[i * T_WIDTH + T_V + (e / 4) % 4] = 1;
        t[i * T_WIDTH + T_W + e / 16] = 1;
    }
    for gi in 0..height {
        let real: u32 = [FI_IV, FI_ROUND, FI_OUT].iter().map(|&f| main[gi * w + lay.flags + f]).sum();
        let r = main[gi * w + lay.r] as usize;
        t[r * T_WIDTH + T_MC] += real;
        let nx = (gi + 1) % height;
        if main[nx * w + lay.flags + FI_ROUND] == 1 {
            t[r * T_WIDTH + T_MK] += 1;
        }
    }
    t
}

/// Interface consumer rows from the reference compression (independent of the AIR trace).
pub fn gen_harness(lay: &Layout, comps: &[Comp]) -> (Vec<u32>, usize) {
    let height = (comps.len() * 16).next_power_of_two().max(4);
    let mut t = vec![0u32; height * H_WIDTH];
    for (s, c) in comps.iter().enumerate() {
        let out = sha2_compress(c);
        let ws: Vec<u64> = c.h.iter().chain(c.block.iter()).chain(out.iter()).copied().collect();
        for m in 0..16 {
            let row = &mut t[(s * 16 + m) * H_WIDTH..][..H_WIDTH];
            row[0] = (s * ROWS) as u32;
            row[1] = m as u32;
            for (h, wv) in [ws[2 * m], ws[2 * m + 1]].into_iter().enumerate() {
                for (i, v) in lay.limbs(wv).into_iter().enumerate() {
                    row[2 + 3 * h + i] = v as u32;
                }
            }
            row[8] = 1;
        }
    }
    (t, height)
}

pub fn gen_all(lay: Layout, comps: &[Comp]) -> Traces {
    let h = main_height(comps.len());
    let main = gen_main(lay, comps, h);
    let table = gen_table(&lay, &main, h);
    let (harness, hh) = gen_harness(&lay, comps);
    Traces { lay, main, main_height: h, table, harness, harness_height: hh }
}

/// Output state read back from the trace's OUT rows of compression s.
pub fn trace_output(lay: &Layout, main: &[u32], s: usize) -> [u64; 8] {
    let w = lay.width;
    let get = |r: usize, base: usize| {
        let row = &main[(s * ROWS + r) * w..][..w];
        (0..lay.nd).fold(0u64, |acc, j| acc | ((row[base + j] as u64) << (lay.k * j)))
    };
    [
        get(42, lay.a1),
        get(42, lay.a0),
        get(0, lay.w0),
        get(0, lay.w1),
        get(42, lay.e1),
        get(42, lay.e0),
        get(1, lay.w0),
        get(1, lay.w1),
    ]
}

/// Deterministic xorshift for test inputs (no extra dependency).
pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    pub fn comp(&mut self) -> Comp {
        Comp {
            h: std::array::from_fn(|_| self.next()),
            block: std::array::from_fn(|_| self.next()),
        }
    }
}
