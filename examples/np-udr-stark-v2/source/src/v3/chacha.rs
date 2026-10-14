//! Honest ChaCha20 trace generators for `nearAirV3` — tables 8/9/10 (part 2
//! extension).  Rust twins of the three Lean generators:
//!
//! * table 8 `chachaV3` — `ZkFormal.Chacha.Gen` (`posRow`/`blockRows`/`rowCell`);
//! * table 9 `rngV3`    — `ZkFormal.Chacha.Rng.Gen` (`callRows`/`drawCell`), plus
//!   the A9 word counter of `Rng.Table.table22` (`Render/RngW0.lean`
//!   `rngTraceW0`: `w` col 137, the 20 bits of `W0 − w` in cols 138..157);
//! * table 10 `shufV3`  — `ZkFormal.Chacha.Shuffle.Gen` (`instRows`/`SInst.cell`).
//!
//! The trusted ChaCha20 core is `NearSpecV3.ChaCha20` (`add32`, `rotl32`, `qr`,
//! `doubleRound`, `rounds`, `chachaBlock`) and the Lemire draw is
//! `NearSpecV3.genIndex` (implemented here as `gen_at`, fuel 64).
//!
//! Heights follow the aligned convention of the other `v3::*` generators:
//! `2^pad_log22 (log_of rows)` for the generator's honest row count (`86·|reqs|`
//! for `chacha`, `Σ nd` for `rng`, `Σ L` for `shuf`), padding with the Lean
//! padding row.  Every honest cell is `< 2^16` (limbs, bits, carries, flags), so
//! `Fp.ofNat` is the identity and [`Tab::set`]'s `% P` is exact.  The
//! `conformance` differential compares the dumps with `np-lean-render-v3`.
//!
//! Entry JSON field names (the Lean structures of the same name):
//! * `ChachaReq` (`ZkFormal.Chacha.Gen.Req`): `key`, `ctr`, `used`;
//! * `RngCall`   (`ZkFormal.Chacha.Rng.Gen.Call`): `key`, `kstart`, `n`;
//! * `ShuffleInst` (`ZkFormal.Chacha.Shuffle.Gen.SInst`): `lid`, `key`,
//!   `kstart`, `vals`.

use serde::Deserialize;

use super::{Tab, get, log_of, pad_log22};

pub const CHACHA_WIDTH: usize = 272;
/// `Rng.Table.widthW0`: the base 137 columns, the A9 word counter `w` (137)
/// and the 20 bits `Wb e` (138 + e) of `W0 − w` (`nearAirV3` table 9 =
/// `Rng.Table.table22`).
pub const RNG_WIDTH: usize = 158;
/// The base `Rng.Table.width`.
pub const RNG_BASE_WIDTH: usize = 137;
/// `Rng.Table.W0` (`NearSpecV3.W0`): the A9 bound on drawn words.
pub const W0: u64 = 770_000;
/// `Rng.Table.colA` (active row), `colW`, `colWb 0`.
const RNG_COL_A: usize = 129;
const RNG_COL_W: usize = 137;
const RNG_COL_WB: usize = 138;
pub const SHUF_WIDTH: usize = 77;

/// `NearSpecV3.M32`.
const M32: u64 = 1u64 << 32;
/// `ZkFormal.Chacha.consts` (`0x61707865 0x3320646e 0x79622d32 0x6b206574`).
const CONSTS: [u64; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];

// ------------------------------------------------------------- JSON mirrors

/// One `chachaV3` request (`ZkFormal.Chacha.Gen.Req`): block `ctr` of `key`;
/// `used[w]` says whether word `w` is provided on `busChacha`.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct ChachaReq {
    pub key: Vec<u64>,
    pub ctr: u64,
    pub used: Vec<bool>,
}

/// One `rngV3` call (`ZkFormal.Chacha.Rng.Gen.Call`): `gen_index(n)` on the
/// stream of `key` from position `kstart`.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct RngCall {
    pub key: Vec<u64>,
    pub kstart: u64,
    pub n: u64,
}

/// One `shufV3` instance (`ZkFormal.Chacha.Shuffle.Gen.SInst`): Fisher–Yates on
/// `vals` with the RNG stream of `key` from `kstart`.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct ShuffleInst {
    pub lid: u64,
    pub key: Vec<u64>,
    pub kstart: u64,
    pub vals: Vec<u64>,
}

// ------------------------------------------------------------ ChaCha20 core

/// `limbN x l = x / 2^(16·l) % 65536`.
fn limb_n(x: u64, l: u32) -> u64 {
    (x >> (16 * l)) & 0xffff
}

/// `bt x b = x / 2^b % 2`.
fn bt(x: u64, b: u32) -> u64 {
    (x >> b) & 1
}

/// `add32`.
fn add32(a: u64, b: u64) -> u64 {
    (a + b) % M32
}

/// `rotl32 a n` (`n ∈ [1, 31]`).
fn rotl32(a: u64, n: u32) -> u64 {
    let a = a % M32;
    (((a << n) & (M32 - 1)) | (a >> (32 - n))) & (M32 - 1)
}

/// `grp p`: slots of quarter-round `p < 8`.
fn grp(p: usize) -> (usize, usize, usize, usize) {
    match p {
        0 => (0, 4, 8, 12),
        1 => (1, 5, 9, 13),
        2 => (2, 6, 10, 14),
        3 => (3, 7, 11, 15),
        4 => (0, 5, 10, 15),
        5 => (1, 6, 11, 12),
        6 => (2, 7, 8, 13),
        _ => (3, 4, 9, 14),
    }
}

/// `NearSpecV3.qr` on the four slots `(a, b, c, d)`.
fn qr(s: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = add32(s[a], s[b]);
    s[d] = rotl32(s[d] ^ s[a], 16);
    s[c] = add32(s[c], s[d]);
    s[b] = rotl32(s[b] ^ s[c], 12);
    s[a] = add32(s[a], s[b]);
    s[d] = rotl32(s[d] ^ s[a], 8);
    s[c] = add32(s[c], s[d]);
    s[b] = rotl32(s[b] ^ s[c], 7);
}

/// `NearSpecV3.initArr key ctr`.
fn init_arr(key: &[u64], ctr: u64) -> [u64; 16] {
    let mut s = [0u64; 16];
    s[..4].copy_from_slice(&CONSTS);
    for (i, slot) in s[4..12].iter_mut().enumerate() {
        *slot = get(key, i);
    }
    s[12] = ctr % M32;
    s[13] = (ctr / M32) % M32;
    s
}

/// `NearSpecV3.chachaBlock key ctr` (16 output words).
fn chacha_block(key: &[u64], ctr: u64) -> [u64; 16] {
    let init = init_arr(key, ctr);
    let mut s = init;
    for _ in 0..10 {
        for p in 0..8 {
            let (a, b, c, d) = grp(p);
            qr(&mut s, a, b, c, d);
        }
    }
    let mut out = [0u64; 16];
    for i in 0..16 {
        out[i] = add32(s[i], init[i]);
    }
    out
}

/// Lazy word stream: `streamWord key k`, caching the current block.
struct Stream {
    key: [u64; 8],
    ctr: u64,
    blk: [u64; 16],
}

impl Stream {
    fn new(key: &[u64]) -> Stream {
        let k = std::array::from_fn(|i| get(key, i));
        Stream {
            key: k,
            ctr: u64::MAX,
            blk: [0; 16],
        }
    }
    /// `(chachaBlock key (k / 16))[k % 16]`.
    fn word(&mut self, k: u64) -> u64 {
        let c = k / 16;
        if c != self.ctr {
            self.blk = chacha_block(&self.key, c);
            self.ctr = c;
        }
        self.blk[(k % 16) as usize]
    }
}

/// `NearSpecV3.bitLen 64 n`.
fn bit_len(n: u64) -> u32 {
    if n == 0 { 0 } else { 64 - n.leading_zeros() }
}

/// `NearSpecV3.lz32 n = 32 − bitLen 64 n`.
fn lz32(n: u64) -> u32 {
    32 - bit_len(n)
}

/// `NearSpecV3.zoneOf n`.
fn zone_of(n: u64) -> u64 {
    (((n << lz32(n)) % M32) + M32 - 1) % M32
}

/// `NearSpecV3.accepts n v`.
fn accepts(n: u64, v: u64) -> bool {
    (v.wrapping_mul(n)) % M32 <= zone_of(n)
}

/// `NearSpecV3.genAt 64 n key k` — `(index, position after)`, fuel 64.
fn gen_at(stream: &mut Stream, n: u64, mut k: u64) -> Option<(u64, u64)> {
    for _ in 0..64 {
        let v = stream.word(k);
        if accepts(n, v) {
            return Some((v.wrapping_mul(n) / M32, k + 1));
        }
        k += 1;
    }
    None
}

/// `leadingBit n = n.log2` (floor; `Nat.log2 0 = 0`).
fn top_bit(n: u64) -> u32 {
    if n == 0 { 0 } else { 63 - n.leading_zeros() }
}

// ============================================================ table 8 chacha

/// Cell values of one block row (`Chacha.Gen.rowCell`).
struct ChachaCalc {
    req: ChachaReq,
    init: [u64; 16],
    /// `st[q] = stBefore init q` for `q = 0 ..= 80`.
    st: Vec<[u64; 16]>,
    out: [u64; 16],
}

/// `qw` (`Chacha.Gen.QW`): all intermediate words of one quarter-round.
struct Qw {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    d1: u64,
    a1: u64,
    b1: u64,
    c1: u64,
    d2: u64,
    a2: u64,
    c2: u64,
    b2: u64,
}

fn qw(a: u64, b: u64, c: u64, d: u64) -> Qw {
    let a1 = add32(a, b);
    let d1 = rotl32(d ^ a1, 16);
    let c1 = add32(c, d1);
    let b1 = rotl32(b ^ c1, 12);
    let a2 = add32(a1, b1);
    let d2 = rotl32(d1 ^ a2, 8);
    let c2 = add32(c1, d2);
    let b2 = rotl32(b1 ^ c2, 7);
    Qw {
        a,
        b,
        c,
        d,
        d1,
        a1,
        b1,
        c1,
        d2,
        a2,
        c2,
        b2,
    }
}

/// `Chacha.Gen.carry x y l`: carry out of limb `l` of the limb-wise addition.
fn carry(x: u64, y: u64, l: u32) -> u64 {
    let c0 = (limb_n(x, 0) + limb_n(y, 0)) / 65536;
    if l == 0 {
        c0
    } else {
        (limb_n(x, 1) + limb_n(y, 1) + c0) / 65536
    }
}

impl ChachaCalc {
    fn new(req: &ChachaReq) -> ChachaCalc {
        let init = init_arr(&req.key, req.ctr);
        let mut st = Vec::with_capacity(81);
        st.push(init);
        for q in 0..80 {
            let mut next = st[q];
            let (a, b, c, d) = grp(q % 8);
            qr(&mut next, a, b, c, d);
            st.push(next);
        }
        let mut out = [0u64; 16];
        for i in 0..16 {
            out[i] = add32(st[80][i], init[i]);
        }
        ChachaCalc {
            req: req.clone(),
            init,
            st,
            out,
        }
    }

    /// `Chacha.Gen.Row` classification of block row `m < 86`.
    fn kd(&self, m: usize) -> Kd {
        if m == 0 {
            Kd::I0
        } else if m == 1 {
            Kd::I1
        } else if m < 82 {
            Kd::Q((m - 2) / 8, (m - 2) % 8)
        } else {
            Kd::F(m - 82)
        }
    }

    /// `sWord`: state word `i` before the row's quarter-round.
    fn s_word(&self, m: usize, i: usize) -> u64 {
        match self.kd(m) {
            Kd::I0 | Kd::I1 => self.init[i],
            Kd::Q(dr, p) => self.st[8 * dr + p][i],
            Kd::F(_) => self.st[80][i],
        }
    }

    /// `xWord`: the six bit-decomposed words `X m`.
    fn x_word(&self, m: usize, x: usize) -> u64 {
        match self.kd(m) {
            Kd::I0 => {
                if x < 6 {
                    get(&self.req.key, x)
                } else {
                    0
                }
            }
            Kd::I1 => {
                if x < 2 {
                    get(&self.req.key, 6 + x)
                } else if x == 2 {
                    self.req.ctr
                } else {
                    0
                }
            }
            Kd::Q(dr, p) => {
                let (a, b, c, d) = grp(p);
                let w = qw(
                    self.st[8 * dr + p][a],
                    self.st[8 * dr + p][b],
                    self.st[8 * dr + p][c],
                    self.st[8 * dr + p][d],
                );
                match x {
                    0 => w.b,
                    1 => w.d,
                    2 => w.a1,
                    3 => w.c1,
                    4 => w.a2,
                    5 => w.c2,
                    _ => 0,
                }
            }
            Kd::F(j) => {
                if x < 4 {
                    self.out[4 * x + j]
                } else {
                    0
                }
            }
        }
    }

    /// `cCell`: carry bit of limb `l` of addition `q`.
    fn c_cell(&self, m: usize, q: usize, l: u32) -> u64 {
        match self.kd(m) {
            Kd::Q(dr, p) => {
                let (a, b, c, d) = grp(p);
                let w = qw(
                    self.st[8 * dr + p][a],
                    self.st[8 * dr + p][b],
                    self.st[8 * dr + p][c],
                    self.st[8 * dr + p][d],
                );
                match q {
                    0 => carry(w.a, w.b, l),
                    1 => carry(w.c, w.d1, l),
                    2 => carry(w.a1, w.b1, l),
                    3 => carry(w.c1, w.d2, l),
                    _ => 0,
                }
            }
            Kd::F(j) => {
                if q < 4 {
                    // `carry (fin R)[4·q+j] (init R)[4·q+j] l`.
                    carry(self.st[80][4 * q + j], self.init[4 * q + j], l)
                } else {
                    0
                }
            }
            _ => 0,
        }
    }

    /// `kWord`: key word `j < 8` / counter (`j = 8`).
    fn k_word(&self, j: usize) -> u64 {
        if j < 8 {
            get(&self.req.key, j)
        } else if j == 8 {
            self.req.ctr
        } else {
            0
        }
    }

    /// `kflag`: flag / counter columns `250 + k`, `k < 18`.
    fn k_flag(&self, m: usize, k: usize) -> u64 {
        match self.kd(m) {
            Kd::I0 => (k == 0) as u64,
            Kd::I1 => (k == 1) as u64,
            Kd::Q(dr, p) => {
                if k == 2 + p {
                    1
                } else if (14..18).contains(&k) {
                    bt(dr as u64, (k - 14) as u32)
                } else {
                    0
                }
            }
            Kd::F(j) => (k == 10 + j) as u64,
        }
    }

    /// `mflag`: multiplicity bit `M kk`.
    fn m_flag(&self, m: usize, kk: usize) -> u64 {
        match self.kd(m) {
            Kd::F(j) => get_bool(&self.req.used, 4 * kk + j) as u64,
            _ => 0,
        }
    }

    /// `rowCell` for block row `m`.
    fn cell(&self, m: usize, c: usize) -> u64 {
        if c < 32 {
            limb_n(self.s_word(m, c / 2), (c % 2) as u32)
        } else if c < 224 {
            bt(self.x_word(m, (c - 32) / 32), ((c - 32) % 32) as u32)
        } else if c < 232 {
            self.c_cell(m, (c - 224) / 2, ((c - 224) % 2) as u32)
        } else if c < 250 {
            limb_n(self.k_word((c - 232) / 2), ((c - 232) % 2) as u32)
        } else if c < 268 {
            self.k_flag(m, c - 250)
        } else if c < 272 {
            self.m_flag(m, c - 268)
        } else {
            0
        }
    }
}

/// Row kind of a block row (`Chacha.Gen.Kd`; padding is handled by the `Tab`).
#[derive(Clone, Copy, Debug)]
enum Kd {
    I0,
    I1,
    Q(usize, usize),
    F(usize),
}

fn get_bool(xs: &[bool], i: usize) -> bool {
    xs.get(i).copied().unwrap_or(false)
}

/// `Chacha.Gen.honestRows.length = 86 · |reqs|`.
pub fn chacha_height(reqs: &[ChachaReq]) -> usize {
    86 * reqs.len()
}

/// `chachaTraceAligned reqs` (`Render/PaddedChacha.lean`): the honest
/// `chachaV3` rows at `padLog22 (logOf (86·|reqs|))`, zero padding.
pub fn chacha_aligned(reqs: &[ChachaReq]) -> Tab {
    let rows = chacha_height(reqs);
    let mut t = Tab::zero(pad_log22(log_of(rows)), CHACHA_WIDTH);
    let h = t.height();
    let mut r = 0usize;
    for req in reqs {
        let calc = ChachaCalc::new(req);
        for m in 0..86 {
            if r >= h {
                break;
            }
            for c in 0..CHACHA_WIDTH {
                t.set(r, c, calc.cell(m, c));
            }
            r += 1;
        }
    }
    t
}

// =============================================================== table 9 rng

/// `Rng.Gen.nd C = kend − kstart` and the calls' `(j, kend)`.
fn rng_result(c: &RngCall, stream: &mut Stream) -> (u64, u64) {
    gen_at(stream, c.n, c.kstart).unwrap_or((0, c.kstart + 1))
}

/// `Rng.Gen.honestRows.length = Σ nd C`.
pub fn rng_rows(calls: &[RngCall]) -> usize {
    calls
        .iter()
        .map(|c| {
            let mut s = Stream::new(&c.key);
            let (_, kend) = rng_result(c, &mut s);
            (kend - c.kstart) as usize
        })
        .sum()
}

/// Cell `c` of draw row `d` of call `C` (`Rng.Gen.drawCell`).
fn rng_cell(c: &RngCall, stream: &mut Stream, d: u64, nd: u64, kstart: u64, col: usize) -> u64 {
    let k = kstart + d;
    let v = stream.word(k);
    let vlo = v % 65536;
    let vhi = v / 65536 % 65536;
    let m0 = vlo * c.n % 65536;
    let c0 = vlo * c.n / 65536;
    let m1 = (vhi * c.n + c0) % 65536;
    let m2 = (vhi * c.n + c0) / 65536;
    let z = c.n * (1u64 << (15 - top_bit(c.n)));
    let last = d + 1 == nd;
    let dl = if last {
        (z - 1).saturating_sub(m1)
    } else {
        m1.saturating_sub(z)
    };
    let acc = last as u64;
    let st = (d == 0) as u64;
    if col < 16 {
        limb_n(get(&c.key, col / 2), (col % 2) as u32)
    } else if col == 16 {
        k / 16
    } else if col < 21 {
        bt(k % 16, (col - 17) as u32)
    } else if col == 21 {
        vlo
    } else if col == 22 {
        vhi
    } else if col < 37 {
        bt(c.n, (col - 23) as u32)
    } else if col < 51 {
        ((col - 37) as u32 == top_bit(c.n)) as u64
    } else if col < 67 {
        bt(m0, (col - 51) as u32)
    } else if col < 81 {
        bt(c0, (col - 67) as u32)
    } else if col < 97 {
        bt(m1, (col - 81) as u32)
    } else if col < 111 {
        bt(m2, (col - 97) as u32)
    } else if col < 127 {
        bt(dl, (col - 111) as u32)
    } else if col == 127 {
        acc
    } else if col == 128 {
        st
    } else if col == 129 {
        1
    } else if col < 136 {
        bt(d, (col - 130) as u32)
    } else if col == 136 {
        kstart
    } else {
        0
    }
}

/// `rngTraceW0 calls 9` (`Render/RngW0.lean`): the aligned base render
/// (`rngTraceAligned`, columns `< 137`) with the A9 counter columns filled:
/// `w_r` = active rows (`a = 1`) among rows `0..=r`, and the bits of
/// `W0 − (active rows)` (truncating; constant) in columns `138 + e`, `e < 20`.
pub fn rng_aligned(calls: &[RngCall]) -> Tab {
    let mut t = rng_base_aligned(calls);
    let h = t.height();
    let mut w = 0u64;
    for r in 0..h {
        if t.cells[r * RNG_WIDTH + RNG_COL_A] == 1 {
            w += 1;
        }
        t.set(r, RNG_COL_W, w);
    }
    let rest = W0.saturating_sub(w);
    for r in 0..h {
        for e in 0..20 {
            t.set(r, RNG_COL_WB + e, bt(rest, e as u32));
        }
    }
    t
}

/// `rngTraceAligned calls`: the base generator's cells (columns `< 137`) at the
/// aligned height `padLog22 (logOf (Σ nd))`.
fn rng_base_aligned(calls: &[RngCall]) -> Tab {
    let rows = rng_rows(calls);
    let mut t = Tab::zero(pad_log22(log_of(rows)), RNG_WIDTH);
    let h = t.height();
    let mut r = 0usize;
    'calls: for c in calls {
        let mut probe = Stream::new(&c.key);
        let (_, kend) = rng_result(c, &mut probe);
        let nd = kend - c.kstart;
        let mut stream = Stream::new(&c.key);
        for d in 0..nd {
            if r >= h {
                break 'calls;
            }
            for col in 0..RNG_BASE_WIDTH {
                t.set(r, col, rng_cell(c, &mut stream, d, nd, c.kstart, col));
            }
            r += 1;
        }
    }
    t
}

// ============================================================ table 10 shuf

/// `Shuffle.Gen.SInst.L`.
fn shuf_l(i: &ShuffleInst) -> usize {
    i.vals.len()
}

/// `Shuffle.Gen.SInst.kAt` for `m = 0 ..= L−1`.
fn shuf_kat(i: &ShuffleInst, stream: &mut Stream) -> Vec<u64> {
    let l = shuf_l(i);
    let mut kat = vec![0u64; l];
    if l == 0 {
        return kat;
    }
    kat[0] = i.kstart;
    for m in 0..l - 1 {
        let n = (l - m) as u64;
        let kend = gen_at(stream, n, kat[m]).map(|(_, kend)| kend).unwrap_or(0);
        kat[m + 1] = kend;
    }
    kat
}

/// `Shuffle.Gen.SInst.js q` for `q = 1 ..= L−1` (`js[0] = 0`).
fn shuf_js(i: &ShuffleInst, stream: &mut Stream, kat: &[u64]) -> Vec<u64> {
    let l = shuf_l(i);
    let mut js = vec![0u64; l];
    for q in 1..l {
        let kq = kat[l - 1 - q];
        js[q] = gen_at(stream, q as u64 + 1, kq)
            .map(|(j, _)| j)
            .unwrap_or(0);
    }
    js
}

/// `Shuffle.Gen.honestRows.length = Σ L`.
pub fn shuf_rows(insts: &[ShuffleInst]) -> usize {
    insts.iter().map(shuf_l).sum()
}

/// `shufTraceAligned insts` (`Render/PaddedChacha.lean`): the honest `shufV3`
/// rows at `padLog22 (logOf (Σ L))`, padding rows `rc = r`.
pub fn shuf_aligned(insts: &[ShuffleInst]) -> Tab {
    let rows = shuf_rows(insts);
    let mut t = Tab::zero(pad_log22(log_of(rows)), SHUF_WIDTH);
    let h = t.height();
    let mut r = 0usize;
    'insts: for inst in insts {
        let l = shuf_l(inst);
        if l == 0 {
            continue;
        }
        let mut stream = Stream::new(&inst.key);
        let kat = shuf_kat(inst, &mut stream);
        let js = shuf_js(inst, &mut stream, &kat);
        // arr(q) built incrementally, q descending; `next_write[x]` is the
        // smallest step `q' > q` with `js q' = x` and `x < q'` (`lw`, else `L`).
        let mut arr = inst.vals.clone();
        let mut next_write = vec![l as u64; l];
        for q in (0..l).rev() {
            if r >= h {
                break 'insts;
            }
            let step = q >= 1;
            let s2 = step && js[q] < q as u64;
            let jj = if step { js[q] } else { 0 };
            let t1 = next_write[q];
            let t2 = if s2 { next_write[js[q] as usize] } else { 0 };
            let c_val = arr[q];
            let o_val = if s2 { arr[js[q] as usize] } else { 0 };
            let v0 = arr_value(&inst.vals, q);
            let mut cell = [0u64; SHUF_WIDTH];
            cell[0] = inst.lid;
            cell[1] = r as u64;
            cell[2] = (r - (l - 1 - q)) as u64;
            cell[3] = l as u64;
            cell[4] = q as u64;
            cell[5] = jj;
            for k in 0..16 {
                cell[6 + k] = limb_n(get(&inst.key, k / 2), (k % 2) as u32);
            }
            cell[22] = kat[l - 1 - q];
            cell[23] = if step { kat[l - q] } else { 0 };
            cell[24] = inst.kstart;
            cell[25] = v0;
            cell[26] = c_val;
            cell[27] = o_val;
            cell[28] = t1;
            cell[29] = t2;
            let d1 = t1.saturating_sub(q as u64 + 1);
            for b in 0..14 {
                cell[30 + b] = bt(d1, b as u32);
            }
            if s2 {
                let d2 = t2.saturating_sub(q as u64 + 1);
                let dj = (q as u64).saturating_sub(js[q] + 1);
                for b in 0..14 {
                    cell[44 + b] = bt(d2, b as u32);
                    cell[58 + b] = bt(dj, b as u32);
                }
            }
            cell[72] = 1;
            cell[73] = (q + 1 == l) as u64;
            cell[74] = (q == 0) as u64;
            cell[75] = (!s2) as u64;
            cell[76] = s2 as u64;
            for (c, x) in cell.into_iter().enumerate() {
                t.set(r, c, x);
            }
            r += 1;
            if step {
                let x = js[q] as usize;
                if js[q] < q as u64 {
                    next_write[x] = q as u64;
                }
                arr.swap(q, x);
            }
        }
    }
    // `rowCell .pad r c = if c = colRc then r else 0`.
    while r < h {
        t.set(r, 1, r as u64);
        r += 1;
    }
    t
}

fn arr_value(vals: &[u64], q: usize) -> u64 {
    vals.get(q).copied().unwrap_or(0)
}

// ------------------------------------------------- lane entries from runs

/// The ChaCha-lane entries of a list of scheduler runs (`Render/ChachaLane.lean`):
/// `laneReqs rs`, `laneCalls rs`, `laneInsts rs`.
pub fn lane(rs: &[&super::sched::Run]) -> (Vec<ChachaReq>, Vec<RngCall>, Vec<ShuffleInst>) {
    let mut insts = Vec::new();
    let mut reqs = Vec::new();
    for r in rs {
        // `runInsts R`: `roundInst R rd = ⟨lidOf τ T, R.key, kst, entries.map ein⟩`
        for rd in &r.rounds {
            insts.push(ShuffleInst {
                lid: r.tau * 4_194_304 + rd.t,
                key: r.key.clone(),
                kstart: rd.kst,
                vals: rd.entries.iter().map(|e| e.ein).collect(),
            });
        }
        // `Gen.Lane.chachaReqs R`: every block of the words `0 … kfin − 1`
        for ctr in 0..r.kfin.div_ceil(16) {
            reqs.push(ChachaReq {
                key: r.key.clone(),
                ctr,
                used: (0..16).map(|w| 16 * ctr + w < r.kfin).collect(),
            });
        }
    }
    // `instCalls I = (range (L − 1)).map (e ↦ ⟨key, kAt e, L − e⟩)`
    let mut calls = Vec::new();
    for i in &insts {
        let mut stream = Stream::new(&i.key);
        let kat = shuf_kat(i, &mut stream);
        let l = shuf_l(i);
        for e in 0..l.saturating_sub(1) {
            calls.push(RngCall {
                key: i.key.clone(),
                kstart: kat[e],
                n: (l - e) as u64,
            });
        }
    }
    (reqs, calls, insts)
}

/// A list of scheduler blocks (`sched::SchedIn`, objects with a `run`) is read
/// as its runs' lane entries.
fn lane_of_json(json: &str) -> Option<(Vec<ChachaReq>, Vec<RngCall>, Vec<ShuffleInst>)> {
    let v: serde_json::Value = serde_json::from_str(json).ok()?;
    let first = v.as_array()?.first()?;
    first.get("run")?;
    let bs = super::sched::parse_all(json).ok()?;
    Some(lane(&bs.iter().map(|b| &b.run).collect::<Vec<_>>()))
}

// -------------------------------------------------------------------- render

/// Parse `json` as `List ChachaReq` (or a scheduler block list: `laneReqs`) and render the aligned `chachaV3` trace.
pub fn render(json: &str) -> Result<Tab, String> {
    if let Some((reqs, _, _)) = lane_of_json(json) {
        return Ok(chacha_aligned(&reqs));
    }
    let reqs: Vec<ChachaReq> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(chacha_aligned(&reqs))
}

/// Parse `json` as `List RngCall` (or a scheduler block list: `laneCalls`) and render the aligned `rngV3` trace.
pub fn render_rng(json: &str) -> Result<Tab, String> {
    if let Some((_, calls, _)) = lane_of_json(json) {
        return Ok(rng_aligned(&calls));
    }
    let calls: Vec<RngCall> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(rng_aligned(&calls))
}

/// Parse `json` as `List ShuffleInst` (or a scheduler block list: `laneInsts`) and render the aligned `shufV3` trace.
pub fn render_shuf(json: &str) -> Result<Tab, String> {
    if let Some((_, _, insts)) = lane_of_json(json) {
        return Ok(shuf_aligned(&insts));
    }
    let insts: Vec<ShuffleInst> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(shuf_aligned(&insts))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn req(key: [u64; 8], ctr: u64, used: [bool; 16]) -> ChachaReq {
        ChachaReq {
            key: key.to_vec(),
            ctr,
            used: used.to_vec(),
        }
    }

    /// A single block's `F j` row encodes output word `4·m + j`.
    #[test]
    fn chacha_single_block_outputs() {
        let key = [0u64, 1, 2, 3, 4, 5, 6, 7];
        let t = chacha_aligned(&[req(key, 0, [true; 16])]);
        // 86 rows -> logOf 86 = 7 -> padLog22 7 = 7 -> height 128
        assert_eq!(t.log, 7);
        assert_eq!(t.height(), 128);
        assert_eq!(t.width, CHACHA_WIDTH);
        let at = |r: usize, c: usize| t.cells[r * CHACHA_WIDTH + c] as u64;
        // I0 row (0): flag, S limbs = init state, K limbs = key words.
        assert_eq!(at(0, 250), 1);
        assert_eq!(at(0, 0), 0x7865); // S0 limb0
        assert_eq!(at(0, 1), 0x6170); // S0 limb1
        assert_eq!(at(0, 2 * 4 + 0), 0); // S4 = key[0] = 0
        assert_eq!(at(0, 2 * 4 + 1), 0);
        assert_eq!(at(0, 232), 0); // K0 limb0 = key[0] (column 232 + 2·0)
        assert_eq!(at(0, 232 + 2 * 4 + 1), 0); // K4 limb1 = key[4] >> 16
        assert_eq!(at(0, 2 * 12 + 0), 0); // S12 limb0 = ctr % 2^16 = 0
        assert_eq!(at(0, 2 * 12 + 1), 0); // S12 limb1 = ctr / 2^16 = 0
        assert_eq!(at(1, 251), 1); // I1 row
        // F j row = 82 + j encodes X m = outW(4·m + j).
        let word =
            |r: usize, m: usize| -> u64 { (0..32).map(|b| at(r, 32 + 32 * m + b) << b).sum() };
        // Reference block for key 0..7, ctr 0 (independently verified against
        // RFC 8439 A.1's quarter-round/double-round core).
        let out: [u64; 16] = [
            4062562330, 1058763918, 2822854854, 2671630309, 1688322078, 828310969, 186264792,
            3721351595, 3581065299, 2192213834, 2252836717, 3694146021, 3091522130, 2201483776,
            3292001902, 761995487,
        ];
        for j in 0..4 {
            for m in 0..4 {
                assert_eq!(word(82 + j, m), out[4 * m + j], "F{j} m{m}");
            }
            assert_eq!(at(82 + j, 260 + j), 1); // F j flag
        }
        // M kk on an F row = used[4·kk + j].
        assert_eq!(at(82, 268), 1);
        // Padding row is all zero.
        for c in 0..CHACHA_WIDTH {
            assert_eq!(at(100, c), 0, "pad col {c}");
        }
    }

    #[test]
    fn chacha_round_trips_json() {
        let j = serde_json::to_string(&[req([1, 2, 3, 4, 5, 6, 7, 8], 5, [false; 16])]).unwrap();
        let t = render(&j).unwrap();
        assert_eq!(t.width, CHACHA_WIDTH);
        assert!(t.height() >= 86);
    }

    /// Lemire: `key 0..7`, `n = 2`, `kstart = 0`: draw 0 is rejected, draw 1
    /// accepts with `m2 = 0`.
    #[test]
    fn rng_small_call() {
        let key = [0u64, 1, 2, 3, 4, 5, 6, 7];
        let call = RngCall {
            key: key.to_vec(),
            kstart: 0,
            n: 2,
        };
        let t = rng_aligned(&[call]);
        assert_eq!(t.log, 1); // Σ nd = 2 -> logOf 2 = 1 -> padLog22 1 = 1
        assert_eq!(t.height(), 2);
        assert_eq!(t.width, RNG_WIDTH);
        let at = |r: usize, c: usize| t.cells[r * RNG_WIDTH + c] as u64;
        // row 0: k = 0, key limbs, ctr 0, acc 0, st 1, a 1
        assert_eq!(at(0, 16), 0); // ctr
        assert_eq!(at(0, 127), 0); // acc
        assert_eq!(at(0, 128), 1); // st
        assert_eq!(at(0, 129), 1); // a
        // n = 2 -> N bits, top bit 1
        assert_eq!(at(0, 23 + 1), 1);
        assert_eq!(at(0, 37 + 1), 1); // H one-hot at i = 1
        // row 1: accepted, acc = 1, m2 = 0
        assert_eq!(at(1, 127), 1);
        assert_eq!(at(1, 128), 0);
        let m2: u64 = (0..14).map(|b| at(1, 97 + b) << b).sum();
        assert_eq!(m2, 0);
        // vlo/vhi of draw 0 (v = streamWord 0)
        let v = chacha_block(&key.to_vec(), 0)[0];
        assert_eq!(v, 4062562330);
        assert_eq!(at(0, 21), v % 65536);
        assert_eq!(at(0, 22), v / 65536 % 65536);
    }

    /// The A9 counter: `w` counts the active rows, the bits hold `W0 − w_last`.
    #[test]
    fn rng_w0_counter() {
        let call = RngCall {
            key: vec![0, 1, 2, 3, 4, 5, 6, 7],
            kstart: 0,
            n: 2,
        };
        // 3 calls of 2 draws: 6 rows -> logOf 6 = 3 -> padLog22 3 = 4 -> 16 rows
        let t = rng_aligned(&[call.clone(), call.clone(), call]);
        assert_eq!(t.height(), 16);
        let at = |r: usize, c: usize| t.cells[r * RNG_WIDTH + c] as u64;
        for r in 0..16 {
            assert_eq!(at(r, RNG_COL_W), (r as u64 + 1).min(6), "w at {r}");
            let wb: u64 = (0..20).map(|e| at(r, RNG_COL_WB + e) << e).sum();
            assert_eq!(wb, W0 - 6);
        }
    }

    /// Fisher–Yates `L = 2`, `js(1) = 0`: row `q = 1` is a step, `q = 0` final.
    #[test]
    fn shuf_small_instance() {
        let key = [0u64, 1, 2, 3, 4, 5, 6, 7];
        let inst = ShuffleInst {
            lid: 9,
            key: key.to_vec(),
            kstart: 0,
            vals: vec![10, 20],
        };
        let t = shuf_aligned(&[inst]);
        assert_eq!(t.log, 1);
        assert_eq!(t.height(), 2);
        assert_eq!(t.width, SHUF_WIDTH);
        let at = |r: usize, c: usize| t.cells[r * SHUF_WIDTH + c] as u64;
        // row 0 = q 1 (step), row 1 = q 0 (final)
        assert_eq!(at(0, 0), 9); // lid
        assert_eq!(at(0, 1), 0); // rc
        assert_eq!(at(0, 2), 0); // inst
        assert_eq!(at(0, 3), 2); // L
        assert_eq!(at(0, 4), 1); // q
        assert_eq!(at(0, 5), 0); // j = js(1) = 0
        assert_eq!(at(0, 24), 0); // ks = kstart
        assert_eq!(at(0, 25), 20); // v0 = vals[q] = vals[1] = 20
        assert_eq!(at(0, 26), 20); // c = arr(1)[1] = 20
        assert_eq!(at(0, 27), 10); // o = arr(1)[js=0] = 10
        assert_eq!(at(0, 28), 2); // t1 = lw(1,1) = L = 2 (no later writer of 1)
        assert_eq!(at(0, 29), 2); // t2 = lw(1,0) = L = 2 (no step after 1)
        assert_eq!(at(0, 73), 1); // st
        assert_eq!(at(0, 74), 0); // fin
        assert_eq!(at(0, 75), 0); // eqj (s2)
        assert_eq!(at(0, 76), 1); // s2
        // final row
        assert_eq!(at(1, 4), 0);
        assert_eq!(at(1, 26), 20); // arr(0)[0] = 20 (after swap)
        assert_eq!(at(1, 73), 0);
        assert_eq!(at(1, 74), 1); // fin
        assert_eq!(at(1, 75), 1); // eqj
        assert_eq!(at(1, 76), 0);
    }

    #[test]
    fn shuf_pads_with_row_counter() {
        // L = 3 -> logOf 3 = 2 -> padLog22 2 = 4 -> height 16.
        let inst = ShuffleInst {
            lid: 0,
            key: vec![0; 8],
            kstart: 0,
            vals: vec![1, 2, 3],
        };
        let t = shuf_aligned(&[inst]);
        assert_eq!(t.height(), 16);
        let at = |r: usize, c: usize| t.cells[r * SHUF_WIDTH + c] as u64;
        for q in 3..16 {
            assert_eq!(at(q, 1), q as u64, "pad rc at {q}");
            for c in (0..SHUF_WIDTH).filter(|&c| c != 1) {
                assert_eq!(at(q, c), 0, "pad col {c} at {q}");
            }
        }
    }

    #[test]
    fn empty_tables_have_min_height() {
        assert_eq!(chacha_aligned(&[]).height(), 2);
        assert_eq!(rng_aligned(&[]).height(), 2);
        assert_eq!(shuf_aligned(&[]).height(), 2);
    }
}
