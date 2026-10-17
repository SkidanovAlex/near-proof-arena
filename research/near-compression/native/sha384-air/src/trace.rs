//! Trace generation for the narrow SHA-512 compression AIR, plus a native
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

fn bsig0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}
fn bsig1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}
fn ssig0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}
fn ssig1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}
fn chf(e: u64, f: u64, g: u64) -> u64 {
    (e & f) ^ (!e & g)
}
fn majf(a: u64, b: u64, c: u64) -> u64 {
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

fn put(row: &mut [u32], base: usize, x: u64) {
    for i in 0..64 {
        row[base + i] = ((x >> i) & 1) as u32;
    }
}
pub fn get(row: &[u32], base: usize) -> u64 {
    (0..64).fold(0u64, |acc, i| acc | ((row[base + i] as u64 & 1) << i))
}
fn put3(row: &mut [u32], base: usize, v: [u64; 3]) {
    for i in 0..3 {
        assert!(v[i] < (1 << 31));
        row[base + i] = v[i] as u32;
    }
}
fn l3(x: u64) -> [u64; 3] {
    limbs3(x)
}
fn sum3(xs: &[[u64; 3]]) -> [u64; 3] {
    std::array::from_fn(|i| xs.iter().map(|x| x[i]).sum())
}
/// Carries for out + 2^{s_i} c_i - c_{i-1} = rhs_i; checks the output limbs.
fn carries(out: u64, rhs: [u64; 3]) -> [u64; 3] {
    let ol = l3(out);
    let mut c = [0u64; 3];
    let mut prev = 0u64;
    for i in 0..3 {
        let w = LIMB_OFF[i + 1] - LIMB_OFF[i];
        let v = rhs[i] + prev;
        assert_eq!(v & ((1 << w) - 1), ol[i], "limb mismatch");
        c[i] = v >> w;
        assert!(c[i] < RANGE as u64);
        prev = c[i];
    }
    c
}

pub struct Traces {
    pub main: Vec<u32>,
    pub main_height: usize,
    pub table: Vec<u32>,
    pub harness: Vec<u32>,
    pub harness_height: usize,
}

pub fn main_height(n: usize) -> usize {
    (n * ROWS).next_power_of_two().max(4)
}

/// Main trace (row-major, WIDTH).  `height` >= n*ROWS, a power of two.
pub fn gen_main(comps: &[Comp], height: usize) -> Vec<u32> {
    assert!(height >= comps.len() * ROWS && height.is_power_of_two());
    let mut t = vec![0u32; height * WIDTH];
    // Pass 1: bits, control, round constants.
    for gi in 0..height {
        let row = &mut t[gi * WIDTH..(gi + 1) * WIDTH];
        let s = gi / ROWS;
        let r = if s < comps.len() {
            gi % ROWS
        } else {
            PAD_R as usize
        };
        let e = ctl_entry(r);
        row[R] = r as u32;
        row[G] = gi as u32;
        for (k, col) in (F_IV..=F_S3).enumerate() {
            row[col] = e[1 + k] as u32;
        }
        for k in 0..6 {
            row[K0 + k] = e[9 + k] as u32;
        }
    }
    for (s, c) in comps.iter().enumerate() {
        let wd = round_words(c);
        let base = s * ROWS;
        for r in 0..ROWS {
            let row = &mut t[(base + r) * WIDTH..(base + r + 1) * WIDTH];
            let (sa, se): ([u64; 2], [u64; 2]) = if r < 42 {
                // a index (j+4) for slots j = 2r-4, 2r-3
                (
                    [wd.a[2 * r], wd.a[2 * r + 1]],
                    [wd.e[2 * r], wd.e[2 * r + 1]],
                )
            } else if r == 42 {
                ([wd.out[1], wd.out[0]], [wd.out[5], wd.out[4]])
            } else {
                ([wd.out[3], wd.out[2]], [wd.out[7], wd.out[6]])
            };
            put(row, A0, sa[0]);
            put(row, A1, sa[1]);
            put(row, E0, se[0]);
            put(row, E1, se[1]);
            if (2..42).contains(&r) {
                put(row, W0, wd.w[2 * r - 4]);
                put(row, W1, wd.w[2 * r - 3]);
            }
        }
    }
    // Pass 2: S and D for every non-OUT row, from the (cyclic) previous row.
    let gs = |t: &[u32], gi: usize, base: usize| get(&t[gi * WIDTH..(gi + 1) * WIDTH], base);
    for gi in 0..height {
        if t[gi * WIDTH + F_OUT] == 1 {
            continue;
        }
        let p = (gi + height - 1) % height;
        let (a0l, a1l, e0l, e1l) = (gs(&t, p, A0), gs(&t, p, A1), gs(&t, p, E0), gs(&t, p, E1));
        let (a0n, a1n, e0n, e1n) = (
            gs(&t, gi, A0),
            gs(&t, gi, A1),
            gs(&t, gi, E0),
            gs(&t, gi, E1),
        );
        let t1 = sum3(&[l3(e0l), l3(bsig1(e1n)), l3(chf(e1n, e0n, e1l))]);
        let sa = sum3(&[t1, l3(bsig0(a1n)), l3(majf(a1n, a0n, a1l))]);
        let se = sum3(&[t1, l3(a0l)]);
        let row = &mut t[gi * WIDTH..(gi + 1) * WIDTH];
        put3(row, SA, sa);
        put3(row, SE, se);
        put3(row, DA, l3(a1l));
        put3(row, DE, l3(e1l));
    }
    // Pass 3: received values and carries (needs S/D of the previous row).
    for s in 0..comps.len() {
        let base = s * ROWS;
        for r in 0..ROWS {
            let gi = base + r;
            let prev: Vec<u32> = t[(gi - if gi > 0 { 1 } else { 0 }) * WIDTH..][..WIDTH].to_vec();
            let at = |rr: usize, col: usize| gs(&t, base + rr, col);
            let mut row: Vec<u32> = t[gi * WIDTH..(gi + 1) * WIDTH].to_vec();
            if (2..42).contains(&r) {
                let (a0l, a1l, e0l, e1l) = (
                    get(&prev, A0),
                    get(&prev, A1),
                    get(&prev, E0),
                    get(&prev, E1),
                );
                let (a0n, a1n, e0n, e1n) =
                    (get(&row, A0), get(&row, A1), get(&row, E0), get(&row, E1));
                let (w0n, w1n) = (get(&row, W0), get(&row, W1));
                let pv = |c: usize| -> [u64; 3] { std::array::from_fn(|i| prev[c + i] as u64) };
                let k0: [u64; 3] = std::array::from_fn(|i| row[K0 + i] as u64);
                let k1: [u64; 3] = std::array::from_fn(|i| row[K1 + i] as u64);
                // slot 1
                let t1 = sum3(&[pv(DE), l3(bsig1(e0n)), l3(chf(e0n, e1l, e0l)), k1, l3(w1n)]);
                let ra = sum3(&[t1, l3(bsig0(a0n)), l3(majf(a0n, a1l, a0l))]);
                let re = sum3(&[t1, pv(DA)]);
                put3(&mut row, C1A, carries(a1n, ra));
                put3(&mut row, C1E, carries(e1n, re));
                // slot 0
                put3(&mut row, C0A, carries(a0n, sum3(&[pv(SA), l3(w0n), k0])));
                put3(&mut row, C0E, carries(e0n, sum3(&[pv(SE), l3(w0n), k0])));
                if r >= 10 {
                    let v0 = sum3(&[l3(at(r - 8, W0)), l3(ssig0(at(r - 8, W1)))]);
                    let v1 = sum3(&[l3(at(r - 8, W1)), l3(ssig0(at(r - 7, W0)))]);
                    put3(&mut row, RV0, v0);
                    put3(&mut row, RV1, v1);
                    put3(&mut row, R7A, l3(at(r - 4, W1)));
                    put3(&mut row, R7B, l3(at(r - 3, W0)));
                    let (w0l, w1l) = (get(&prev, W0), get(&prev, W1));
                    put3(
                        &mut row,
                        CW0,
                        carries(w0n, sum3(&[l3(ssig1(w0l)), l3(at(r - 4, W1)), v0])),
                    );
                    put3(
                        &mut row,
                        CW1,
                        carries(w1n, sum3(&[l3(ssig1(w1l)), l3(at(r - 3, W0)), v1])),
                    );
                }
            } else if r >= 42 {
                let (ivr, finr) = if r == 42 { (1, 41) } else { (0, 40) };
                for (q, &slot) in SLOTS.iter().enumerate() {
                    let iv = at(ivr, slot);
                    let fin = at(finr, slot);
                    put3(&mut row, OUT_IV + 3 * q, l3(iv));
                    put3(&mut row, OUT_FIN + 3 * q, l3(fin));
                    let outw = get(&row, slot);
                    assert_eq!(outw, iv.wrapping_add(fin));
                    put3(
                        &mut row,
                        OUT_C + 3 * q,
                        carries(outw, sum3(&[l3(iv), l3(fin)])),
                    );
                }
            }
            t[gi * WIDTH..(gi + 1) * WIDTH].copy_from_slice(&row);
        }
    }
    t
}

/// Table trace (64 rows) with multiplicities counted from the main trace.
pub fn gen_table(main: &[u32], height: usize) -> Vec<u32> {
    let mut t = vec![0u32; 64 * T_WIDTH];
    for i in 0..64 {
        t[i * T_WIDTH + T_U + i % 8] = 1;
        t[i * T_WIDTH + T_V + i / 8] = 1;
    }
    for gi in 0..height {
        let row = &main[gi * WIDTH..(gi + 1) * WIDTH];
        t[row[R] as usize * T_WIDTH + T_MC] += 1;
        for col in C1A..C1A + NCARRY {
            t[row[col] as usize * T_WIDTH + T_MR] += 1;
        }
    }
    t
}

/// Interface consumer rows from the reference compression (independent of the AIR trace).
pub fn gen_harness(comps: &[Comp]) -> (Vec<u32>, usize) {
    let height = (comps.len() * 32).next_power_of_two().max(4);
    let mut t = vec![0u32; height * H_WIDTH];
    for (s, c) in comps.iter().enumerate() {
        let out = sha2_compress(c);
        let ws: Vec<u64> =
            c.h.iter()
                .chain(c.block.iter())
                .chain(out.iter())
                .copied()
                .collect();
        for (idx, w) in ws.into_iter().enumerate() {
            let row = &mut t[(s * 32 + idx) * H_WIDTH..][..H_WIDTH];
            row[0] = (s * ROWS) as u32;
            row[1] = idx as u32;
            for k in 0..4 {
                row[2 + k] = ((w >> (16 * k)) & 0xffff) as u32;
            }
            row[6] = 1;
        }
    }
    (t, height)
}

pub fn gen_all(comps: &[Comp]) -> Traces {
    let h = main_height(comps.len());
    let main = gen_main(comps, h);
    let table = gen_table(&main, h);
    let (harness, hh) = gen_harness(comps);
    Traces {
        main,
        main_height: h,
        table,
        harness,
        harness_height: hh,
    }
}

/// Output state read back from the trace's OUT rows of compression s.
pub fn trace_output(main: &[u32], s: usize) -> [u64; 8] {
    let row = |r: usize| &main[(s * ROWS + r) * WIDTH..][..WIDTH];
    let (r42, r43) = (row(42), row(43));
    [
        get(r42, A1),
        get(r42, A0),
        get(r43, A1),
        get(r43, A0),
        get(r42, E1),
        get(r42, E0),
        get(r43, E1),
        get(r43, E0),
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
