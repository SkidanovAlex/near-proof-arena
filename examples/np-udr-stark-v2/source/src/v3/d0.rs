//! D0 native preprocessing: the Rust twin of `NearSpecV3.prepD0`
//! (`spec/lean/v3/NearSpecV3/PrepD0.lean`) — the claim-side (`prepClaim`) and
//! hint-side (`prepBody`) parts of the v3 prover.
//!
//! `prep(cb, h)` decodes a real `claim.bin`, walks the segment (`walkD0`), builds
//! the source lists (applied order, ChaCha20-shuffled), the per-block scheduler
//! public data (`Scheduler.pubOf`), the routing intervals and forwarding demands,
//! then parses the proof-carried `Hint` (`decodeBody`), does the header
//! comparisons and the Reed–Solomon `encodedMerkleRoot` over the body.  The
//! result is the `Prep` structure whose `encode()` is the STARK's public input.
//!
//! This module reuses `crate::near::reexec` (SHA-256, bytes), `crate::v3::prep`
//! (`Hint`, `decode_body`, the `Prep`/`SchedPub` codecs) and `crate::near::spec`
//! (receipts, merkle root).  Everything else (`decodeClaimE`, `decodeLayout`,
//! `decodeBlk`, `walkD0`, ChaCha20 shuffle, the bandwidth scheduler's public
//! part and the congestion `F64` model, `outgoingReceiptsRoot`,
//! `encodedMerkleRoot`) is ported here.

use crate::near::reexec::sha256;
use crate::near::reexec::spec::account_id_valid;
use crate::near::reexec::wire::{Reader, WResult};
use crate::near::spec::{
    self as ns, Bytes, PublicKey, Receipt, borsh_bytes, encode_receipts, u16b, u32b, u64b, u128b,
};
use crate::v3::prep::{self, Hint, Prep, PrepHdr, SchedParams, SchedPub, SrcList};

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}
pub(crate) fn mapw<T>(r: WResult<T>) -> Result<T, String> {
    r.map_err(|e| e.to_string())
}

/// First index of `x` in `ids` (`Scheduler.indexOf`).
pub fn index_of(ids: &[u64], x: u64) -> Option<usize> {
    ids.iter().position(|&y| y == x)
}

/// `BTreeMap::from_iter`-style insertion, sorted by key, a later equal key
/// overwrites (`Scheduler.mapInsert`).
fn map_insert<T: Clone>(k: u64, v: T, l: &mut Vec<(u64, T)>) {
    match l.iter().position(|(k2, _)| *k2 >= k) {
        Some(i) if l[i].0 == k => l[i] = (k, v),
        Some(i) => l.insert(i, (k, v)),
        None => l.push((k, v)),
    }
}
fn to_btree_map<T: Clone>(es: &[(u64, T)]) -> Vec<(u64, T)> {
    let mut out = Vec::new();
    for (k, v) in es {
        map_insert(*k, v.clone(), &mut out);
    }
    out
}

/// `NearSpec.lexLe`: byte-lexicographic `a ≤ b`.
fn lex_le(a: &[u8], b: &[u8]) -> bool {
    match (a.split_first(), b.split_first()) {
        (None, _) => true,
        (Some(_), None) => false,
        (Some((x, xs)), Some((y, ys))) => x < y || (x == y && lex_le(xs, ys)),
    }
}
fn lex_max(a: &[u8], b: &[u8]) -> Vec<u8> {
    if lex_le(a, b) { b.to_vec() } else { a.to_vec() }
}
fn lex_max_opt(l: &[Vec<u8>]) -> Option<Vec<u8>> {
    let mut acc: Option<Vec<u8>> = None;
    for b in l {
        acc = Some(match acc {
            None => b.clone(),
            Some(a) => lex_max(&a, b),
        });
    }
    acc
}

pub(crate) fn zero32() -> Bytes {
    vec![0u8; 32]
}

// ---------------------------------------------------------------------------
// F64: exact binary64 model (`NearSpecV3.F64`)
//
// Values are canonical `m · 2^e` with `m = 0, e = 0` or `2^52 ≤ m < 2^53`.
// The operations used by congestion control (`ofNat`, `div`, `mul`, `add`,
// `sub`, `max`, `beq 1`, `round`, `asU64`) are transcribed on the dyadic
// representation, with round-to-nearest-even (`round_mantissa`).
// ---------------------------------------------------------------------------

const TWO52: u128 = 4503599627370496;
const TWO53: u128 = 9007199254740992;
const U64_MAX: u128 = 18446744073709551615;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F64 {
    m: u128,
    e: i32,
}

fn bit_len_u128(n: u128) -> u32 {
    128 - n.leading_zeros()
}

impl F64 {
    fn zero() -> F64 {
        F64 { m: 0, e: 0 }
    }
    fn one() -> F64 {
        F64 { m: TWO52, e: -52 }
    }
    /// Round `ma · 2^e` (exact) to canonical form, ties to even.
    fn round_mantissa(ma: u128, e: i32) -> F64 {
        if ma == 0 {
            return F64::zero();
        }
        let b = bit_len_u128(ma) as i32;
        if b <= 53 {
            let sh = 53 - b;
            F64 {
                m: ma << sh,
                e: e - sh,
            }
        } else {
            let sh = (b - 53) as u32;
            let mant = ma >> sh;
            let rem = ma & ((1u128 << sh) - 1);
            let half = 1u128 << (sh - 1);
            let mut m = mant;
            if rem > half || (rem == half && mant & 1 == 1) {
                m += 1;
            }
            let e2 = e + sh as i32;
            if m == TWO53 {
                F64 {
                    m: TWO52,
                    e: e2 + 1,
                }
            } else {
                F64 { m, e: e2 }
            }
        }
    }
    /// `n as f64` (round to nearest, ties to even).
    fn of_nat(n: u128) -> F64 {
        if n == 0 {
            return F64::zero();
        }
        F64::round_mantissa(n, 0)
    }
    fn fmax(a: F64, b: F64) -> F64 {
        if F64::fle(a, b) { b } else { a }
    }
    /// `a ≤ b` on values.
    fn fle(a: F64, b: F64) -> bool {
        if a.m == 0 {
            return true;
        }
        if b.m == 0 {
            return false;
        }
        if a.e == b.e {
            return a.m <= b.m;
        }
        if a.e < b.e {
            let sh = (b.e - a.e) as u32;
            if sh >= 128 {
                return false;
            }
            a.m <= b.m << sh
        } else {
            let sh = (a.e - b.e) as u32;
            if sh >= 128 {
                return true;
            }
            a.m << sh <= b.m
        }
    }
    fn mul(a: F64, b: F64) -> F64 {
        F64::round_mantissa(a.m * b.m, a.e + b.e)
    }
    /// `a / b` (`b ≠ 0`): exact quotient `a.m/b.m · 2^(a.e−b.e)`.
    fn div(a: F64, b: F64) -> F64 {
        if a.m == 0 {
            return F64::zero();
        }
        let e = a.e - b.e;
        let shift = 60i32;
        let num = a.m << shift;
        let q = num / b.m;
        let r = num % b.m;
        let mut ma = q * 2;
        if 2 * r >= b.m {
            ma += 1;
        }
        F64::round_mantissa(ma, e - shift - 1)
    }
    /// `a + b`.
    fn add(a: F64, b: F64) -> F64 {
        if a.m == 0 {
            return b;
        }
        if b.m == 0 {
            return a;
        }
        let e = a.e.min(b.e);
        let sa = (a.e - e) as u32;
        let sb = (b.e - e) as u32;
        let ma = a.m.checked_shl(sa).unwrap_or(0);
        let mb = b.m.checked_shl(sb).unwrap_or(0);
        F64::round_mantissa(ma + mb, e)
    }
    /// `a − b` (assumes `a ≥ b`; `0` otherwise).
    fn sub(a: F64, b: F64) -> F64 {
        if b.m == 0 {
            return a;
        }
        if a.m == 0 || !F64::fle(b, a) {
            return F64::zero();
        }
        let e = a.e.min(b.e);
        let sa = (a.e - e) as u32;
        let sb = (b.e - e) as u32;
        let ma = a.m.checked_shl(sa).unwrap_or(0);
        let mb = b.m.checked_shl(sb).unwrap_or(0);
        F64::round_mantissa(ma.saturating_sub(mb), e)
    }
    /// `f64::round` (half away from zero; `x ≥ 0`).
    fn round_nat(&self) -> u128 {
        if self.m == 0 {
            return 0;
        }
        if self.e >= 0 {
            self.m.checked_shl(self.e as u32).unwrap_or(u128::MAX)
        } else {
            let sh = (-self.e) as u32;
            let q = self.m >> sh.min(127);
            let r = self.m & ((1u128 << sh.min(127)) - 1);
            let half = 1u128 << (sh.min(127) - 1);
            if r >= half { q + 1 } else { q }
        }
    }
    fn round(&self) -> F64 {
        F64::of_nat(self.round_nat())
    }
    /// `x as u64`: truncation toward zero, saturating at `u64::MAX`.
    fn as_u64(&self) -> u64 {
        let t = if self.e >= 0 {
            self.m.checked_shl(self.e as u32).unwrap_or(u128::MAX)
        } else {
            self.m >> ((-self.e) as u32)
        };
        t.min(U64_MAX) as u64
    }
}

// ---------------------------------------------------------------------------
// Congestion control (`NearSpecV3.Congestion`)
// ---------------------------------------------------------------------------

/// `CongestionInfoV1`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CongestionInfo {
    pub delayed_gas: u128,
    pub buffered_gas: u128,
    pub receipt_bytes: u64,
    pub allowed_shard: u64,
}

/// `CongestionControlConfig.pv86` (only the fields used here).
struct CongCfg;
impl CongCfg {
    const MAX_INCOMING: u128 = 400000000000000000;
    const MAX_OUTGOING: u128 = 10000000000000000;
    const MAX_MEMORY: u64 = 1000000000;
    const MAX_MISSED: u64 = 125;
    const MAX_OUTGOING_GAS: u128 = 300000000000000000;
    const MIN_OUTGOING_GAS: u128 = 1000000000000000;
    const ALLOWED_SHARD_OUTGOING_GAS: u128 = 1000000000000000;
}

fn clamped_fraction(v: u128, max: u128) -> F64 {
    if max <= v {
        F64::one()
    } else {
        F64::div(F64::of_nat(v), F64::of_nat(max))
    }
}

fn mix(left: u128, right: u128, ratio: F64) -> u128 {
    let left_part = F64::mul(F64::of_nat(left), F64::sub(F64::one(), ratio));
    let right_part = F64::mul(F64::of_nat(right), ratio);
    F64::add(left_part, right_part).round().as_u64() as u128
}

fn congestion_level(info: &CongestionInfo, missed: u64) -> F64 {
    let incoming = clamped_fraction(info.delayed_gas, CongCfg::MAX_INCOMING);
    let outgoing = clamped_fraction(info.buffered_gas, CongCfg::MAX_OUTGOING);
    let memory = clamped_fraction(info.receipt_bytes as u128, CongCfg::MAX_MEMORY as u128);
    let missed_c = if missed <= 1 {
        F64::zero()
    } else {
        clamped_fraction(missed as u128, CongCfg::MAX_MISSED as u128)
    };
    F64::fmax(F64::fmax(F64::fmax(incoming, outgoing), memory), missed_c)
}

fn is_fully_congested(info: &CongestionInfo, missed: u64) -> bool {
    congestion_level(info, missed) == F64::one()
}

/// `CongestionControl::outgoing_gas_limit` (`prims.outGas`).
fn outgoing_gas_limit(info: &CongestionInfo, missed: u64, sender_shard: u64) -> u128 {
    let l = congestion_level(info, missed);
    if l == F64::one() {
        if sender_shard == info.allowed_shard {
            CongCfg::ALLOWED_SHARD_OUTGOING_GAS
        } else {
            0
        }
    } else {
        mix(CongCfg::MAX_OUTGOING_GAS, CongCfg::MIN_OUTGOING_GAS, l)
    }
}

// ---------------------------------------------------------------------------
// GF(2^8) and Reed–Solomon (`NearSpecV3.GF256`, `ReedSolomon`)
// ---------------------------------------------------------------------------

const GF_POLY: u32 = 0x11D;

fn gf_mul(mut a: u32, mut b: u32) -> u32 {
    let mut acc = 0u32;
    for _ in 0..8 {
        if b & 1 == 1 {
            acc ^= a;
        }
        a <<= 1;
        if a >= 256 {
            a ^= GF_POLY;
        }
        b >>= 1;
    }
    acc & 0xff
}

fn gf_pow(a: u32, mut n: u32) -> u32 {
    let mut r = 1u32;
    let mut base = a & 0xff;
    while n > 0 {
        if n & 1 == 1 {
            r = gf_mul(r, base);
        }
        base = gf_mul(base, base);
        n >>= 1;
    }
    r
}

fn gf_inv(b: u32) -> u32 {
    gf_pow(b, 254)
}

type GFMat = Vec<Vec<u32>>;

fn gf_vandermonde(rows: usize, cols: usize) -> GFMat {
    (0..rows)
        .map(|r| (0..cols).map(|c| gf_pow(r as u32, c as u32)).collect())
        .collect()
}

fn gf_multiply(lhs: &GFMat, rhs: &GFMat) -> GFMat {
    if rhs.is_empty() {
        return Vec::new();
    }
    let cols: GFMat = (0..rhs[0].len())
        .map(|c| rhs.iter().map(|row| *row.get(c).unwrap_or(&0)).collect())
        .collect();
    lhs.iter()
        .map(|row| {
            cols.iter()
                .map(|col| {
                    row.iter()
                        .zip(col.iter())
                        .fold(0u32, |a, (x, y)| a ^ gf_mul(*x, *y))
                })
                .collect()
        })
        .collect()
}

#[allow(clippy::needless_range_loop)]
fn gf_invert(m: &GFMat, n: usize) -> Option<GFMat> {
    let mut a: GFMat = m
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let mut r = row.clone();
            for j in 0..n {
                r.push(if i == j { 1 } else { 0 });
            }
            r
        })
        .collect();
    for col in 0..n {
        let mut piv = None;
        for r in col..n {
            if a[r][col] != 0 {
                piv = Some(r);
                break;
            }
        }
        let p = piv?;
        a.swap(col, p);
        let inv = gf_inv(a[col][col]);
        for j in 0..2 * n {
            a[col][j] = gf_mul(a[col][j], inv);
        }
        for r in 0..n {
            if r != col && a[r][col] != 0 {
                let s = a[r][col];
                for j in 0..2 * n {
                    a[r][j] ^= gf_mul(s, a[col][j]);
                }
            }
        }
    }
    Some(a.iter().map(|row| row[n..2 * n].to_vec()).collect())
}

fn build_matrix(d: usize, t: usize) -> Option<GFMat> {
    let v = gf_vandermonde(t, d);
    let top: GFMat = v.iter().take(d).cloned().collect();
    let inv = gf_invert(&top, d)?;
    Some(gf_multiply(&v, &inv))
}

fn rs_params_ok(d: u64, t: u64) -> bool {
    d >= 1 && d < t && t <= 256
}

fn rs_part_length(n: usize, d: usize) -> usize {
    n.div_ceil(d)
}

/// `encodedMerkleRoot d t B` (nearcore `reed_solomon_encode` + `merklize`).
pub fn encoded_merkle_root(d: u64, t: u64, b: &[u8]) -> Option<(Bytes, u64)> {
    if !rs_params_ok(d, t) {
        return None;
    }
    let d = d as usize;
    let t = t as usize;
    let m = build_matrix(d, t)?;
    let l = rs_part_length(b.len(), d);
    if l == 0 {
        return None;
    }
    let total = d * l;
    let mut padded = b.to_vec();
    padded.resize(total, 0);
    let data: Vec<&[u8]> = (0..d).map(|j| &padded[j * l..(j + 1) * l]).collect();
    let mut parts: Vec<Bytes> = data.iter().map(|p| p.to_vec()).collect();
    for row in m.iter().skip(d) {
        let mut out = vec![0u8; l];
        for (j, coeff) in row.iter().enumerate() {
            let c = *coeff;
            if c == 0 {
                continue;
            }
            for x in 0..l {
                out[x] ^= gf_mul(c, data[j][x] as u32) as u8;
            }
        }
        parts.push(out);
    }
    let leaves: Vec<Bytes> = parts
        .iter()
        .map(|p| {
            let mut v = u32b(p.len() as u128);
            v.extend_from_slice(p);
            sha256(&v).to_vec()
        })
        .collect();
    Some((ns::merkle_root(&leaves), b.len() as u64))
}

// ---------------------------------------------------------------------------
// ChaCha20 + rand `SliceRandom::shuffle` (`NearSpecV3.ChaCha20`)
// ---------------------------------------------------------------------------

const M32: u64 = 4294967296;
const CHACHA_CONSTS: [u64; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

fn chacha_add32(a: u64, b: u64) -> u64 {
    (a + b) % M32
}
fn chacha_rotl32(a: u64, n: u32) -> u64 {
    let a = a % M32;
    (((a << n) & (M32 - 1)) | (a >> (32 - n))) & (M32 - 1)
}
fn chacha_qr(s: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = chacha_add32(s[a], s[b]);
    s[d] = chacha_rotl32(s[d] ^ s[a], 16);
    s[c] = chacha_add32(s[c], s[d]);
    s[b] = chacha_rotl32(s[b] ^ s[c], 12);
    s[a] = chacha_add32(s[a], s[b]);
    s[d] = chacha_rotl32(s[d] ^ s[a], 8);
    s[c] = chacha_add32(s[c], s[d]);
    s[b] = chacha_rotl32(s[b] ^ s[c], 7);
}
fn chacha_block(key: &[u64], ctr: u64) -> [u64; 16] {
    let mut init = [0u64; 16];
    init[..4].copy_from_slice(&CHACHA_CONSTS);
    for i in 0..8 {
        init[4 + i] = key.get(i).copied().unwrap_or(0);
    }
    init[12] = ctr % M32;
    init[13] = (ctr / M32) % M32;
    let mut s = init;
    for _ in 0..10 {
        chacha_qr(&mut s, 0, 4, 8, 12);
        chacha_qr(&mut s, 1, 5, 9, 13);
        chacha_qr(&mut s, 2, 6, 10, 14);
        chacha_qr(&mut s, 3, 7, 11, 15);
        chacha_qr(&mut s, 0, 5, 10, 15);
        chacha_qr(&mut s, 1, 6, 11, 12);
        chacha_qr(&mut s, 2, 7, 8, 13);
        chacha_qr(&mut s, 3, 4, 9, 14);
    }
    let mut out = [0u64; 16];
    for i in 0..16 {
        out[i] = chacha_add32(s[i], init[i]);
    }
    out
}

/// `NearSpecV3.leWords`: little-endian 32-bit words.
fn le_words(b: &[u8]) -> Vec<u64> {
    b.chunks_exact(4)
        .map(|w| w[0] as u64 + 256 * w[1] as u64 + 65536 * w[2] as u64 + 16777216 * w[3] as u64)
        .collect()
}

pub(crate) struct Stream {
    key: [u64; 8],
    ctr: u64,
    blk: [u64; 16],
}
impl Stream {
    pub(crate) fn of_seed(seed: &[u8]) -> Stream {
        let w = le_words(seed);
        let key = std::array::from_fn(|i| w.get(i).copied().unwrap_or(0));
        Stream {
            key,
            ctr: u64::MAX,
            blk: [0; 16],
        }
    }
    fn word(&mut self, k: u64) -> u64 {
        let c = k / 16;
        if c != self.ctr {
            self.blk = chacha_block(&self.key, c);
            self.ctr = c;
        }
        self.blk[(k % 16) as usize]
    }
}

fn lz32(n: u64) -> u32 {
    if n == 0 {
        32
    } else {
        32 - (64 - n.leading_zeros())
    }
}
fn zone_of(n: u64) -> u64 {
    (((n << lz32(n)) % M32) + M32 - 1) % M32
}
pub(crate) fn gen_at(stream: &mut Stream, n: u64, mut k: u64) -> Option<(u64, u64)> {
    for _ in 0..64 {
        let v = stream.word(k);
        if (v.wrapping_mul(n)) % M32 <= zone_of(n) {
            return Some((v.wrapping_mul(n) / M32, k + 1));
        }
        k += 1;
    }
    None
}
/// `shuffleWithSeed l seed`: `rand 0.8.5 SliceRandom::shuffle` on a fresh RNG.
pub(crate) fn shuffle_with_seed<T>(l: &mut [T], seed: &[u8]) -> bool {
    let mut stream = Stream::of_seed(seed);
    let n = l.len();
    if n == 0 {
        return true;
    }
    let mut k = 0u64;
    let mut i = n - 1;
    while i >= 1 {
        match gen_at(&mut stream, (i + 1) as u64, k) {
            Some((j, k2)) => {
                k = k2;
                l.swap(i, j as usize);
            }
            None => return false,
        }
        i -= 1;
    }
    true
}

// ---------------------------------------------------------------------------
// Wire decoders (`NearSpecV3.Wire`, `ClaimV3`, `Layout`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BwRequest {
    pub to_shard: u64,
    pub bitmap: Vec<u8>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ChunkInner {
    pub tag: u64,
    pub prev_block_hash: Bytes,
    pub prev_state_root: Bytes,
    pub prev_outcome_root: Bytes,
    pub encoded_merkle_root: Bytes,
    pub encoded_length: u64,
    pub height_created: u64,
    pub shard_id: u64,
    pub prev_gas_used: u64,
    pub gas_limit: u64,
    pub prev_balance_burnt: u128,
    pub prev_outgoing_receipts_root: Bytes,
    pub tx_root: Bytes,
    pub proposals: Vec<Bytes>,
    pub congestion: CongestionInfo,
    pub bw_requests: Vec<BwRequest>,
    pub proposed_split: Option<Bytes>,
}

#[derive(Clone, Debug, Default)]
pub struct BlockHdr {
    pub version: u64,
    pub prev_hash: Bytes,
    pub height: u64,
    pub epoch_id: Bytes,
    pub next_epoch_id: Bytes,
    pub timestamp: u64,
    pub random_value: Bytes,
    pub chunk_headers_root: Bytes,
    pub next_gas_price: u128,
    pub hash: Bytes,
}

#[derive(Clone, Debug, Default)]
pub struct ChunkSlot {
    pub inner: Bytes,
    pub height_included: u64,
}

#[derive(Clone, Debug, Default)]
pub struct BlockRec {
    pub header_version: u64,
    pub prev_hash: Bytes,
    pub inner_lite: Bytes,
    pub inner_rest: Bytes,
    pub slots: Vec<ChunkSlot>,
}

#[derive(Clone, Debug, Default)]
pub struct EpochRec {
    pub epoch_id: Bytes,
    pub protocol_version: u64,
    pub epoch_height: u64,
    pub shard_layout: Bytes,
    pub validators: Vec<(Bytes, u128)>,
}

#[derive(Clone, Debug, Default)]
pub struct ApplyFacts {
    pub has_validator_update: bool,
    pub minimum_stake: u128,
    pub has_split_gate: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Claim {
    pub protocol_version: u64,
    pub chain_id: Bytes,
    pub epoch_id: Bytes,
    pub chunk_inner: Bytes,
    pub blocks: Vec<BlockRec>,
    pub rs_data_parts: u64,
    pub rs_total_parts: u64,
    pub epochs: Vec<EpochRec>,
    pub epoch_start_after: Bytes,
    pub apply_facts: Vec<ApplyFacts>,
    pub tx_valid: Bytes,
    pub genesis_chunk_extra: Option<Bytes>,
}

const CLAIM_TAG: &[u8] = b"near-arena-claim-v3";
const STATEMENT_ID_V3: &[u8] = b"near/pv86/chunk-validation/v0";

pub(crate) fn d_tag(r: &mut Reader, want: &[u8], what: &str) -> Result<(), String> {
    let got = mapw(r.bytes("tag"))?;
    if got == want {
        Ok(())
    } else {
        err(format!("decode: wrong {what}"))
    }
}

pub(crate) fn p_account_id(r: &mut Reader, what: &'static str) -> Result<Bytes, String> {
    let a = mapw(r.bytes(what))?.to_vec();
    if account_id_valid(&a) || a == ns::SYSTEM {
        Ok(a)
    } else {
        err(format!("decode: invalid account id ({what})"))
    }
}

pub(crate) fn p_public_key(r: &mut Reader, what: &str) -> Result<PublicKey, String> {
    let tag = mapw(r.u8("key type"))?;
    let n = match tag {
        0 => 32usize,
        1 => 64,
        2 => 1952,
        _ => return err(format!("decode: unknown PublicKey tag ({what})")),
    };
    let data = mapw(r.take(n, "public key"))?.to_vec();
    Ok(PublicKey { tag, data })
}

fn p_consumed_stake(r: &mut Reader) -> Result<Bytes, String> {
    let start = r.pos;
    if mapw(r.u8("ValidatorStake tag"))? != 0 {
        return err("decode: ValidatorStake tag");
    }
    let _ = p_account_id(r, "stake account")?;
    let _ = p_public_key(r, "stake key")?;
    let _ = mapw(r.u128("stake"))?;
    Ok(r.buf[start..r.pos].to_vec())
}

fn p_congestion(r: &mut Reader) -> Result<CongestionInfo, String> {
    if mapw(r.u8("CongestionInfo tag"))? != 0 {
        return err("decode: CongestionInfo tag");
    }
    let delayed_gas = mapw(r.u128("delayed_receipts_gas"))?;
    let buffered_gas = mapw(r.u128("buffered_receipts_gas"))?;
    let receipt_bytes = mapw(r.u64("receipt_bytes"))?;
    let allowed_shard = mapw(r.u16("allowed_shard"))? as u64;
    Ok(CongestionInfo {
        delayed_gas,
        buffered_gas,
        receipt_bytes,
        allowed_shard,
    })
}

fn p_bw_requests(r: &mut Reader) -> Result<Vec<BwRequest>, String> {
    if mapw(r.u8("BandwidthRequests tag"))? != 0 {
        return err("decode: BandwidthRequests tag");
    }
    let n = mapw(r.u32("requests length"))? as usize;
    let mut out = Vec::with_capacity(n.min(1 << 16));
    for _ in 0..n {
        let to_shard = mapw(r.u16("to_shard"))? as u64;
        let bitmap = mapw(r.take(5, "bitmap"))?.to_vec();
        out.push(BwRequest { to_shard, bitmap });
    }
    Ok(out)
}

fn p_trie_split(r: &mut Reader) -> Result<Bytes, String> {
    let start = r.pos;
    let _ = p_account_id(r, "boundary_account")?;
    let _ = mapw(r.u64("left_memory"))?;
    let _ = mapw(r.u64("right_memory"))?;
    Ok(r.buf[start..r.pos].to_vec())
}

/// `pChunkInner` (tagged, V4/V5).
pub(crate) fn p_chunk_inner(r: &mut Reader) -> Result<ChunkInner, String> {
    let tag = mapw(r.u8("ShardChunkHeaderInner tag"))? as u64;
    if tag != 3 && tag != 4 {
        return err("invalid: chunk header inner version not V4/V5");
    }
    let prev_block_hash = mapw(r.hash("prev_block_hash"))?.to_vec();
    let prev_state_root = mapw(r.hash("prev_state_root"))?.to_vec();
    let prev_outcome_root = mapw(r.hash("prev_outcome_root"))?.to_vec();
    let encoded_merkle_root = mapw(r.hash("encoded_merkle_root"))?.to_vec();
    let encoded_length = mapw(r.u64("encoded_length"))?;
    let height_created = mapw(r.u64("height_created"))?;
    let shard_id = mapw(r.u64("shard_id"))?;
    let prev_gas_used = mapw(r.u64("prev_gas_used"))?;
    let gas_limit = mapw(r.u64("gas_limit"))?;
    let prev_balance_burnt = mapw(r.u128("prev_balance_burnt"))?;
    let prev_outgoing_receipts_root = mapw(r.hash("prev_outgoing_receipts_root"))?.to_vec();
    let tx_root = mapw(r.hash("tx_root"))?.to_vec();
    let np = mapw(r.u32("proposals length"))? as usize;
    let mut proposals = Vec::with_capacity(np.min(1 << 10));
    for _ in 0..np {
        proposals.push(p_consumed_stake(r)?);
    }
    let congestion = p_congestion(r)?;
    let bw_requests = p_bw_requests(r)?;
    let proposed_split = if tag == 4 {
        match mapw(r.u8("proposed_split tag"))? {
            0 => None,
            1 => Some(p_trie_split(r)?),
            _ => return err("decode: invalid option tag for proposed_split"),
        }
    } else {
        None
    };
    Ok(ChunkInner {
        tag,
        prev_block_hash,
        prev_state_root,
        prev_outcome_root,
        encoded_merkle_root,
        encoded_length,
        height_created,
        shard_id,
        prev_gas_used,
        gas_limit,
        prev_balance_burnt,
        prev_outgoing_receipts_root,
        tx_root,
        proposals,
        congestion,
        bw_requests,
        proposed_split,
    })
}

fn decode_chunk_inner(b: &[u8]) -> Result<ChunkInner, String> {
    let mut r = Reader::new(b);
    let ci = p_chunk_inner(&mut r)?;
    mapw(r.finish())?;
    Ok(ci)
}

/// `chunkHash inner emr = sha256(sha256 inner ++ emr)`.
pub fn chunk_hash(inner: &[u8], emr: &[u8]) -> Bytes {
    let mut v = sha256(inner).to_vec();
    v.extend_from_slice(emr);
    sha256(&v).to_vec()
}

pub(crate) fn p_signature(r: &mut Reader, what: &'static str) -> Result<(), String> {
    let t = mapw(r.u8("signature type"))?;
    match t {
        0 => {
            let d = mapw(r.take(64, what))?;
            if d[63] / 32 != 0 {
                return err("decode: ed25519 signature high bits");
            }
        }
        1 => {
            mapw(r.take(65, what))?;
        }
        2 => {
            mapw(r.take(3309, what))?;
        }
        _ => return err("decode: unknown signature tag"),
    }
    Ok(())
}

fn p_approval(r: &mut Reader) -> Result<(), String> {
    match mapw(r.u8("approval option"))? {
        0 => Ok(()),
        1 => p_signature(r, "approval"),
        _ => err("decode: invalid option tag for approval"),
    }
}

fn p_validator_stake(r: &mut Reader) -> Result<(), String> {
    if mapw(r.u8("ValidatorStake tag"))? != 0 {
        return err("decode: ValidatorStake tag");
    }
    let _ = p_account_id(r, "stake account")?;
    let _ = p_public_key(r, "stake key")?;
    mapw(r.u128("stake"))?;
    Ok(())
}

/// `decodeBlockV6`.
fn decode_block_v6(
    version: u64,
    prev_hash: &[u8],
    lite: &[u8],
    rest: &[u8],
) -> Result<BlockHdr, String> {
    if version != 5 {
        return err("out of domain (c.headers): block header is not V6");
    }
    let mut l = Reader::new(lite);
    let height = mapw(l.u64("height"))?;
    let epoch_id = mapw(l.hash("epoch_id"))?.to_vec();
    let next_epoch_id = mapw(l.hash("next_epoch_id"))?.to_vec();
    let _ = mapw(l.hash("prev_state_root"))?;
    let _ = mapw(l.hash("prev_outcome_root"))?;
    let timestamp = mapw(l.u64("timestamp"))?;
    let _ = mapw(l.hash("next_bp_hash"))?;
    let _ = mapw(l.hash("block_merkle_root"))?;
    mapw(l.finish())?;
    let mut r = Reader::new(rest);
    let _ = mapw(r.hash("block_body_hash"))?;
    let _ = mapw(r.hash("prev_chunk_outgoing_receipts_root"))?;
    let chr = mapw(r.hash("chunk_headers_root"))?.to_vec();
    let _ = mapw(r.hash("chunk_tx_root"))?;
    let random_value = mapw(r.hash("random_value"))?.to_vec();
    let nvp = mapw(r.u32("prev_validator_proposals length"))? as usize;
    for _ in 0..nvp {
        p_validator_stake(&mut r)?;
    }
    let ncm = mapw(r.u32("chunk_mask length"))? as usize;
    for _ in 0..ncm {
        if mapw(r.u8("chunk_mask"))? > 1 {
            return err("decode: invalid bool chunk_mask");
        }
    }
    let next_gas_price = mapw(r.u128("next_gas_price"))?;
    let _ = mapw(r.u128("total_supply"))?;
    let _ = mapw(r.hash("last_final_block"))?;
    let _ = mapw(r.hash("last_ds_final_block"))?;
    let _ = mapw(r.u64("block_ordinal"))?;
    let _ = mapw(r.u64("prev_height"))?;
    match mapw(r.u8("epoch_sync_data_hash option"))? {
        0 => {}
        1 => {
            mapw(r.hash("epoch_sync_data_hash"))?;
        }
        _ => return err("decode: invalid option tag for epoch_sync_data_hash"),
    }
    let nap = mapw(r.u32("approvals length"))? as usize;
    for _ in 0..nap {
        p_approval(&mut r)?;
    }
    let _ = mapw(r.u32("latest_protocol_version"))?;
    let nce = mapw(r.u32("chunk_endorsements length"))? as usize;
    for _ in 0..nce {
        mapw(r.bytes("chunk_endorsements row"))?;
    }
    match mapw(r.u8("shard_split option"))? {
        0 => {}
        1 => {
            let _ = mapw(r.u64("split shard"))?;
            let _ = p_account_id(&mut r, "split boundary")?;
        }
        _ => return err("decode: invalid option tag for shard_split"),
    }
    mapw(r.finish())?;
    let hash = block_hash(prev_hash, lite, rest);
    Ok(BlockHdr {
        version,
        prev_hash: prev_hash.to_vec(),
        height,
        epoch_id,
        next_epoch_id,
        timestamp,
        random_value,
        chunk_headers_root: chr,
        next_gas_price,
        hash,
    })
}

/// `blockHash prev lite rest = sha256(sha256(sha256 lite ++ sha256 rest) ++ prev)`.
pub fn block_hash(prev: &[u8], lite: &[u8], rest: &[u8]) -> Bytes {
    let mut inner = sha256(lite).to_vec();
    inner.extend_from_slice(&sha256(rest));
    let mut v = sha256(&inner).to_vec();
    v.extend_from_slice(prev);
    sha256(&v).to_vec()
}

/// `Blk`.
#[derive(Clone, Debug, Default)]
pub struct Blk {
    pub rec: BlockRec,
    pub hdr: BlockHdr,
    pub slots: Vec<(u64, ChunkInner)>,
    /// raw slot inner bytes (what `chunkHash` hashes), aligned with `slots`.
    pub slot_inner: Vec<Bytes>,
}

/// `merklizeBorsh` over byte items: `merkleRoot (map sha256 items)`.
fn merklize_borsh(items: &[Bytes]) -> Bytes {
    let leaves: Vec<Bytes> = items.iter().map(|it| sha256(it).to_vec()).collect();
    ns::merkle_root(&leaves)
}

/// `decodeBlk`.
fn decode_blk(rec: &BlockRec) -> Result<Blk, String> {
    let hdr = decode_block_v6(
        rec.header_version,
        &rec.prev_hash,
        &rec.inner_lite,
        &rec.inner_rest,
    )?;
    let mut slots = Vec::with_capacity(rec.slots.len());
    let mut slot_inner = Vec::with_capacity(rec.slots.len());
    for s in &rec.slots {
        let ci = decode_chunk_inner(&s.inner)?;
        slots.push((s.height_included, ci));
        slot_inner.push(s.inner.clone());
    }
    let leaves: Vec<Bytes> = slots
        .iter()
        .enumerate()
        .map(|(i, (h, ci))| {
            let mut v = chunk_hash(&slot_inner[i], &ci.encoded_merkle_root);
            v.extend(u64b(*h as u128));
            v
        })
        .collect();
    if merklize_borsh(&leaves) != hdr.chunk_headers_root {
        return err("invalid: chunk slots do not match chunk_headers_root");
    }
    Ok(Blk {
        rec: rec.clone(),
        hdr,
        slots,
        slot_inner,
    })
}

// ---------------------------------------------------------------------------
// Claim / Layout decoders (`NearSpecV3.ClaimV3`, `Layout`)
// ---------------------------------------------------------------------------

fn d_acct(r: &mut Reader) -> Result<(Bytes, u128), String> {
    let a = mapw(r.bytes("account"))?.to_vec();
    let s = mapw(r.u128("amount"))?;
    Ok((a, s))
}

fn d_slot(r: &mut Reader) -> Result<ChunkSlot, String> {
    let inner = mapw(r.bytes("slot inner"))?.to_vec();
    let height_included = mapw(r.u64("height_included"))?;
    Ok(ChunkSlot {
        inner,
        height_included,
    })
}

fn d_block(r: &mut Reader) -> Result<BlockRec, String> {
    let header_version = mapw(r.u8("header_version"))? as u64;
    let prev_hash = mapw(r.hash("prev_hash"))?.to_vec();
    let inner_lite = mapw(r.bytes("inner_lite"))?.to_vec();
    let inner_rest = mapw(r.bytes("inner_rest"))?.to_vec();
    let ns = mapw(r.u32("slots length"))? as usize;
    let mut slots = Vec::with_capacity(ns.min(1024));
    for _ in 0..ns {
        slots.push(d_slot(r)?);
    }
    Ok(BlockRec {
        header_version,
        prev_hash,
        inner_lite,
        inner_rest,
        slots,
    })
}

fn d_epoch(r: &mut Reader) -> Result<EpochRec, String> {
    let epoch_id = mapw(r.hash("epoch_id"))?.to_vec();
    let protocol_version = mapw(r.u32("protocol_version"))? as u64;
    let epoch_height = mapw(r.u64("epoch_height"))?;
    let shard_layout = mapw(r.bytes("shard_layout"))?.to_vec();
    let nv = mapw(r.u32("validators length"))? as usize;
    let mut validators = Vec::with_capacity(nv.min(4096));
    for _ in 0..nv {
        validators.push(d_acct(r)?);
    }
    Ok(EpochRec {
        epoch_id,
        protocol_version,
        epoch_height,
        shard_layout,
        validators,
    })
}

fn d_vupdate(r: &mut Reader) -> Result<(), String> {
    let a = mapw(r.u32("stake_info length"))? as usize;
    for _ in 0..a {
        d_acct(r)?;
    }
    let b = mapw(r.u32("validator_rewards length"))? as usize;
    for _ in 0..b {
        d_acct(r)?;
    }
    match mapw(r.u8("treasury option"))? {
        0 => {}
        1 => {
            mapw(r.bytes("treasury"))?;
        }
        _ => return err("decode: invalid option tag for treasury"),
    }
    Ok(())
}

fn d_gate(r: &mut Reader) -> Result<(), String> {
    let _ = mapw(r.u64("memory_usage_threshold"))?;
    let _ = mapw(r.u64("min_child_memory_usage"))?;
    let _ = mapw(r.u64("max_number_of_shards"))?;
    let f = mapw(r.u32("force_split_shards length"))? as usize;
    for _ in 0..f {
        mapw(r.u64("shard"))?;
    }
    let g = mapw(r.u32("block_split_shards length"))? as usize;
    for _ in 0..g {
        mapw(r.u64("shard"))?;
    }
    Ok(())
}

fn d_facts(r: &mut Reader) -> Result<ApplyFacts, String> {
    let has_validator_update = match mapw(r.u8("validator_update option"))? {
        0 => false,
        1 => {
            d_vupdate(r)?;
            true
        }
        _ => return err("decode: invalid option tag for validator_update"),
    };
    let minimum_stake = mapw(r.u128("minimum_stake"))?;
    let has_split_gate = match mapw(r.u8("split_gate option"))? {
        0 => false,
        1 => {
            d_gate(r)?;
            true
        }
        _ => return err("decode: invalid option tag for split_gate"),
    };
    Ok(ApplyFacts {
        has_validator_update,
        minimum_stake,
        has_split_gate,
    })
}

/// `decodeClaimE`.
pub fn decode_claim(b: &[u8]) -> Result<Claim, String> {
    let mut r = Reader::new(b);
    d_tag(&mut r, CLAIM_TAG, "claim format")?;
    d_tag(&mut r, STATEMENT_ID_V3, "statement id")?;
    let protocol_version = mapw(r.u32("protocol_version"))? as u64;
    let chain_id = mapw(r.bytes("chain_id"))?.to_vec();
    let epoch_id = mapw(r.hash("epoch_id"))?.to_vec();
    let chunk_inner = mapw(r.bytes("chunk_inner"))?.to_vec();
    let nb = mapw(r.u32("blocks length"))? as usize;
    let mut blocks = Vec::with_capacity(nb.min(64));
    for _ in 0..nb {
        blocks.push(d_block(&mut r)?);
    }
    let rs_data_parts = mapw(r.u16("rs_data_parts"))? as u64;
    let rs_total_parts = mapw(r.u16("rs_total_parts"))? as u64;
    let ne = mapw(r.u32("epochs length"))? as usize;
    let mut epochs = Vec::with_capacity(ne.min(64));
    for _ in 0..ne {
        epochs.push(d_epoch(&mut r)?);
    }
    let epoch_start_after = mapw(r.bytes("epoch_start_after"))?.to_vec();
    let nf = mapw(r.u32("apply_facts length"))? as usize;
    let mut apply_facts = Vec::with_capacity(nf.min(64));
    for _ in 0..nf {
        apply_facts.push(d_facts(&mut r)?);
    }
    let tx_valid = mapw(r.bytes("tx_valid"))?.to_vec();
    let genesis_chunk_extra = match mapw(r.u8("genesis_chunk_extra option"))? {
        0 => None,
        1 => Some(mapw(r.bytes("genesis_chunk_extra"))?.to_vec()),
        _ => return err("decode: invalid option tag for genesis_chunk_extra"),
    };
    mapw(r.finish())?;
    Ok(Claim {
        protocol_version,
        chain_id,
        epoch_id,
        chunk_inner,
        blocks,
        rs_data_parts,
        rs_total_parts,
        epochs,
        epoch_start_after,
        apply_facts,
        tx_valid,
        genesis_chunk_extra,
    })
}

/// `NearSpecV3.Layout`.
#[derive(Clone, Debug, Default)]
pub struct Layout {
    pub boundaries: Vec<Bytes>,
    pub shard_ids: Vec<u64>,
    pub id_to_index: Vec<(u64, u64)>,
}

fn p_pair_u64(r: &mut Reader) -> Result<(u64, u64), String> {
    let a = mapw(r.u64("map key"))?;
    let b = mapw(r.u64("map value"))?;
    Ok((a, b))
}
fn p_key_vec_u64(r: &mut Reader) -> Result<(), String> {
    let _ = mapw(r.u64("map key"))?;
    let n = mapw(r.u32("map value length"))? as usize;
    for _ in 0..n {
        mapw(r.u64("shard"))?;
    }
    Ok(())
}
fn p_account_vec(r: &mut Reader, what: &'static str) -> Result<Vec<Bytes>, String> {
    let n = mapw(r.u32("length"))? as usize;
    let mut out = Vec::with_capacity(n.min(4096));
    for _ in 0..n {
        out.push(p_account_id(r, what)?);
    }
    Ok(out)
}
fn p_u64_vec(r: &mut Reader) -> Result<Vec<u64>, String> {
    let n = mapw(r.u32("length"))? as usize;
    let mut out = Vec::with_capacity(n.min(4096));
    for _ in 0..n {
        out.push(mapw(r.u64("shard id"))?);
    }
    Ok(out)
}
fn p_pair_vec(r: &mut Reader) -> Result<Vec<(u64, u64)>, String> {
    let n = mapw(r.u32("length"))? as usize;
    let mut out = Vec::with_capacity(n.min(4096));
    for _ in 0..n {
        out.push(p_pair_u64(r)?);
    }
    Ok(out)
}

/// `decodeLayout`.
pub fn decode_layout(b: &[u8]) -> Result<Layout, String> {
    let mut r = Reader::new(b);
    let tag = mapw(r.u8("ShardLayout tag"))?;
    match tag {
        2 => {
            let boundaries = p_account_vec(&mut r, "boundary")?;
            let shard_ids = p_u64_vec(&mut r)?;
            let id_to_index = p_pair_vec(&mut r)?;
            let _ = p_pair_vec(&mut r)?; // index_to_id_map
            match mapw(r.u8("shards_split_map option"))? {
                0 => {}
                1 => {
                    let n = mapw(r.u32("split map length"))? as usize;
                    for _ in 0..n {
                        p_key_vec_u64(&mut r)?;
                    }
                }
                _ => return err("decode: invalid option tag for shards_split_map"),
            }
            match mapw(r.u8("shards_parent_map option"))? {
                0 => {}
                1 => {
                    let _ = p_pair_vec(&mut r)?;
                }
                _ => return err("decode: invalid option tag for shards_parent_map"),
            }
            let _ = mapw(r.u32("version"))?;
            mapw(r.finish())?;
            Ok(Layout {
                boundaries,
                shard_ids,
                id_to_index,
            })
        }
        3 => {
            let boundaries = p_account_vec(&mut r, "boundary")?;
            let shard_ids = p_u64_vec(&mut r)?;
            let id_to_index = p_pair_vec(&mut r)?;
            let n = mapw(r.u32("shards_split_map length"))? as usize;
            for _ in 0..n {
                p_key_vec_u64(&mut r)?;
            }
            let _ = mapw(r.u64("last_split"))?;
            let n2 = mapw(r.u32("shards_ancestor_map length"))? as usize;
            for _ in 0..n2 {
                p_key_vec_u64(&mut r)?;
            }
            mapw(r.finish())?;
            Ok(Layout {
                boundaries,
                shard_ids,
                id_to_index,
            })
        }
        _ => err("out of domain (c.layout): shard layout is not V2/V3"),
    }
}

impl Layout {
    pub fn num_shards(&self) -> usize {
        self.shard_ids.len()
    }
    /// `Layout.index` (first `id_to_index` entry with matching id).
    pub fn index(&self, s: u64) -> Option<u64> {
        self.id_to_index
            .iter()
            .find(|(k, _)| *k == s)
            .map(|(_, v)| *v)
    }
    /// `partitionPoint` of `account` over the (sorted) boundaries.
    fn partition_point(&self, acct: &[u8]) -> usize {
        let mut i = 0;
        while i < self.boundaries.len() && lex_le(&self.boundaries[i], acct) {
            i += 1;
        }
        i
    }
    /// `Layout.shardOf`.
    pub fn shard_of(&self, acct: &[u8]) -> u64 {
        let pp = self.partition_point(acct);
        self.shard_ids.get(pp).copied().unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// walkD0 (`ChunkValidationV0a.lean:70`)
// ---------------------------------------------------------------------------

/// `WalkD0`.
pub struct Walk {
    pub c: Claim,
    pub h_chunk: ChunkInner,
    pub layout: Layout,
    pub idx: usize,
    pub blks: Vec<Blk>,
    pub b2i: usize,
    pub stop: usize,
    pub slot_b2: ChunkInner,
    pub implicit_blks: Vec<Blk>,
    pub source_blks: Vec<Blk>,
}

fn rs_genesis_params_ok(d: u64, t: u64) -> bool {
    let want = if t <= 3 { 1 } else { (t - 1) / 3 };
    (2..=256).contains(&t) && d == want
}

/// `walkD0`.
pub fn walk_d0(cb: &[u8]) -> Result<Walk, String> {
    let c = decode_claim(cb)?;
    let h_chunk = decode_chunk_inner(&c.chunk_inner)?;
    let ep = c.epochs.first().cloned().unwrap_or_default();
    let layout = decode_layout(&ep.shard_layout)?;
    let mut blks = Vec::with_capacity(c.blocks.len());
    for b in &c.blocks {
        blks.push(decode_blk(b)?);
    }
    let idx = layout
        .index(h_chunk.shard_id)
        .ok_or_else(|| "layout".to_string())? as usize;
    let is_new = |b: &Blk| -> bool {
        match b.slots.get(idx) {
            Some((h, _)) => *h == b.hdr.height,
            None => false,
        }
    };
    let b2i = blks
        .iter()
        .position(&is_new)
        .ok_or_else(|| "walk".to_string())?;
    let stop_off = blks
        .iter()
        .skip(b2i + 1)
        .position(&is_new)
        .ok_or_else(|| "walk".to_string())?;
    let stop = b2i + 1 + stop_off;
    let slot_b2 = blks
        .get(b2i)
        .and_then(|b| b.slots.get(idx))
        .map(|(_, ci)| ci.clone())
        .ok_or_else(|| "slot".to_string())?;
    let mut implicit_blks: Vec<Blk> = blks[..b2i].to_vec();
    implicit_blks.reverse();
    let source_blks: Vec<Blk> = blks[b2i..b2i + (stop - b2i)].to_vec();
    Ok(Walk {
        c,
        h_chunk,
        layout,
        idx,
        blks,
        b2i,
        stop,
        slot_b2,
        implicit_blks,
        source_blks,
    })
}

// ---------------------------------------------------------------------------
// Bandwidth-scheduler public part (`Scheduler.pubOf`)
// ---------------------------------------------------------------------------

const CFG_MAX_SHARD_BANDWIDTH: u64 = 4_500_000;
const CFG_MAX_SINGLE_GRANT: u64 = 4_194_304;
const CFG_MAX_ALLOWANCE: u64 = 4_500_000;
const CFG_MAX_BASE_BANDWIDTH: u64 = 100_000;
const CFG_MAX_RECEIPT_SIZE: u64 = 4_194_304;

fn params_calculate(n: u64) -> Option<SchedParams> {
    if CFG_MAX_SINGLE_GRANT < CFG_MAX_RECEIPT_SIZE || CFG_MAX_SHARD_BANDWIDTH < CFG_MAX_SINGLE_GRANT
    {
        return None;
    }
    let denom = n.saturating_sub(1).max(1);
    let base = (CFG_MAX_SHARD_BANDWIDTH - CFG_MAX_SINGLE_GRANT) / denom;
    Some(SchedParams {
        base: base.min(CFG_MAX_BASE_BANDWIDTH),
        max_shard_bandwidth: CFG_MAX_SHARD_BANDWIDTH,
        max_single_grant: CFG_MAX_SINGLE_GRANT,
        max_receipt_size: CFG_MAX_RECEIPT_SIZE,
        max_allowance: CFG_MAX_ALLOWANCE,
    })
}

#[derive(Clone, Debug)]
struct ShardStatus {
    fully_congested: bool,
    last_chunk_missing: bool,
    allowed_sender_index: Option<u64>,
}

fn statuses(ids: &[u64], congestion: &[(u64, CongestionInfo, u64)]) -> Vec<Option<ShardStatus>> {
    let mut arr: Vec<Option<ShardStatus>> = vec![None; ids.len()];
    let entries: Vec<(u64, (CongestionInfo, u64))> = congestion
        .iter()
        .map(|(sid, info, missed)| (*sid, (info.clone(), *missed)))
        .collect();
    for (sid, (info, missed)) in to_btree_map(&entries) {
        if let Some(i) = index_of(ids, sid) {
            arr[i] = Some(ShardStatus {
                fully_congested: is_fully_congested(&info, missed),
                last_chunk_missing: missed > 0,
                allowed_sender_index: index_of(ids, info.allowed_shard).map(|x| x as u64),
            });
        }
    }
    arr
}

fn link_allowed(st: &[Option<ShardStatus>], s: usize, r: usize) -> bool {
    match st.get(r).and_then(|x| x.as_ref()) {
        None => false,
        Some(rs) => {
            let sender_missing = st
                .get(s)
                .and_then(|x| x.as_ref())
                .map(|ss| ss.last_chunk_missing)
                .unwrap_or(false);
            if rs.last_chunk_missing || sender_missing {
                false
            } else if rs.fully_congested {
                rs.allowed_sender_index == Some(s as u64)
            } else {
                true
            }
        }
    }
}

fn request_values(p: &SchedParams) -> Vec<u64> {
    (0..40u64)
        .map(|i| p.base + (p.max_single_grant - p.base) * (i + 1) / 40)
        .collect()
}

/// `schedPub ctx` = `Scheduler.pubOf`.
pub fn sched_pub(
    ids: &[u64],
    congestion: &[(u64, CongestionInfo, u64)],
    requests: &[(u64, Vec<BwRequest>)],
    prev_block_hash: &[u8],
) -> Option<SchedPub> {
    let n = ids.len();
    if n == 0 {
        return None;
    }
    let p = params_calculate(n as u64)?;
    let status = statuses(ids, congestion);
    let links = n * n;
    let mut allowed = Vec::with_capacity(links);
    for l in 0..links {
        allowed.push(link_allowed(&status, l / n, l % n));
    }
    let raw: Vec<(u64, Vec<prep::BandwidthRequest>)> = to_btree_map(requests)
        .into_iter()
        .map(|(sender, brs)| {
            let brs = brs
                .into_iter()
                .map(|b| prep::BandwidthRequest {
                    to_shard: b.to_shard,
                    bitmap: b.bitmap,
                })
                .collect();
            (sender, brs)
        })
        .collect();
    let values = request_values(&p);
    let mut all = u32b(n as u128);
    for s in ids {
        all.extend(u64b(*s as u128));
    }
    let all_shards_hash = sha256(&all).to_vec();
    Some(SchedPub {
        ids: ids.to_vec(),
        params: p,
        allowed,
        raw,
        values,
        seed: prev_block_hash.to_vec(),
        all_shards_hash,
    })
}

// ---------------------------------------------------------------------------
// Apply context and forwarding (`RuntimeD0.ApplyCtx`, `PrepD0`)
// ---------------------------------------------------------------------------

/// Per PV 86: `108_059_500_000 + 115_123_062_500` (`Params.G`).
const GAS_PER_RECEIPT: u128 = 223182562500;
const GASMAX: u128 = 18446744073709551615;
const MAX_RECEIPT_SIZE: u128 = 4_194_304;
const ALLOWED_SHARD_OUTGOING_GAS: u128 = 1_000_000_000_000_000;
const CREATE_ACCOUNT_EXEC: u128 = 7_200_000_000_000;
const ADD_FULL_ACCESS_KEY_EXEC: u128 = 101_765_125_000;
const MAX_GAS_LIMIT_D0: u64 = 1_000_000_000_000_000;
const FWD_DEMAND_MAX: u64 = 16_777_216;

/// `ApplyCtx` (claim-side fields).
#[derive(Clone, Debug)]
pub struct ApplyCtx {
    pub height: u64,
    pub prev_block_hash: Bytes,
    pub gas_price: u128,
    pub gas_limit: u64,
    pub layout: Layout,
    pub own: u64,
    pub statuses: Vec<(u64, CongestionInfo, u64)>,
    pub requests: Vec<(u64, Vec<BwRequest>)>,
}

/// `blockCtx l own gasLimit b gasPrice` (`ChunkValidationV0.blockCtx`).
pub(crate) fn block_ctx(
    layout: &Layout,
    own: u64,
    gas_limit: u64,
    b: &Blk,
    gas_price: u128,
) -> ApplyCtx {
    ApplyCtx {
        height: b.hdr.height,
        prev_block_hash: b.hdr.prev_hash.clone(),
        gas_price,
        gas_limit,
        layout: layout.clone(),
        own,
        statuses: b
            .slots
            .iter()
            .map(|(h, ci)| (ci.shard_id, ci.congestion.clone(), b.hdr.height - *h))
            .collect(),
        requests: b
            .slots
            .iter()
            .map(|(_, ci)| (ci.shard_id, ci.bw_requests.clone()))
            .collect(),
    }
}

fn is_hex(c: u8) -> bool {
    (b'a'..=b'f').contains(&c) || c.is_ascii_digit()
}
fn all_hex(b: &[u8]) -> bool {
    b.iter().all(|&c| is_hex(c))
}
/// `AccountId.isNearImplicit`.
fn is_near_implicit(s: &[u8]) -> bool {
    s.len() == 64 && all_hex(s)
}
/// `AccountId.isEthImplicit`.
fn is_eth_implicit(s: &[u8]) -> bool {
    s.len() == 42 && &s[..2] == b"0x" && all_hex(&s[2..])
}
/// `AccountId.isNearDeterministic`.
fn is_near_deterministic(s: &[u8]) -> bool {
    s.len() == 42 && &s[..2] == b"0s" && all_hex(&s[2..])
}

/// `refundCongestionGas receiver`.
fn refund_congestion_gas(receiver: &[u8]) -> u128 {
    let base = GAS_PER_RECEIPT;
    if is_near_implicit(receiver) {
        base + CREATE_ACCOUNT_EXEC + ADD_FULL_ACCESS_KEY_EXEC
    } else if is_eth_implicit(receiver) || is_near_deterministic(receiver) {
        base + CREATE_ACCOUNT_EXEC
    } else {
        base
    }
}

/// `statusShards ctx`: status shard ids in first-occurrence order.
fn status_shards(ctx: &ApplyCtx) -> Vec<u64> {
    let mut acc: Vec<u64> = Vec::new();
    for (s, _, _) in &ctx.statuses {
        if !acc.contains(s) {
            acc.push(*s);
        }
    }
    acc
}

/// `fwdGasOk ctx refunds`.
fn fwd_gas_ok(ctx: &ApplyCtx, refunds: &[Receipt]) -> bool {
    let gas0: Vec<(u64, u128)> = ctx
        .statuses
        .iter()
        .map(|(s, ci, missed)| {
            (
                *s,
                if *s == ctx.own {
                    GASMAX
                } else {
                    outgoing_gas_limit(ci, *missed, ctx.own)
                },
            )
        })
        .collect();
    let get = |ls: &[(u64, u128)], s: u64| -> u128 {
        ls.iter()
            .find(|(x, _)| *x == s)
            .map(|(_, y)| *y)
            .unwrap_or(GASMAX)
    };
    let mut st: Option<Vec<(u64, u128)>> = Some(gas0);
    for r in refunds {
        let Some(ls) = st.as_ref() else { break };
        let s = ctx.layout.shard_of(&r.receiver_id);
        let gas = refund_congestion_gas(&r.receiver_id);
        let g = get(ls, s);
        if g >= gas.min(ALLOWED_SHARD_OUTGOING_GAS) {
            st = Some(
                ls.iter()
                    .map(|(x, y)| if *x == s { (*x, g - gas) } else { (*x, *y) })
                    .collect(),
            );
        } else {
            st = None;
        }
    }
    st.is_some()
}

/// `fwdSizes ctx refunds`.
fn fwd_sizes(ctx: &ApplyCtx, refunds: &[Receipt]) -> Vec<(u64, u64)> {
    status_shards(ctx)
        .into_iter()
        .map(|s| {
            let tot: u64 = refunds
                .iter()
                .filter(|r| ctx.layout.shard_of(&r.receiver_id) == s)
                .map(|r| r.encode().len() as u64)
                .map(|l| l.min(MAX_RECEIPT_SIZE as u64))
                .sum();
            (s, tot)
        })
        .collect()
}

/// `fwdLinks ctx refunds`: `(own·n + idx(s), Σ size)` by scheduler link index.
fn fwd_links(ctx: &ApplyCtx, refunds: &[Receipt]) -> Vec<(u64, u64)> {
    let ids = &ctx.layout.shard_ids;
    let Some(o) = index_of(ids, ctx.own) else {
        return Vec::new();
    };
    fwd_sizes(ctx, refunds)
        .into_iter()
        .filter_map(|(s, tot)| index_of(ids, s).map(|r| ((o * ids.len() + r) as u64, tot)))
        .collect()
}

/// `outgoingReceiptsRoot l rs`.
fn outgoing_receipts_root(l: &Layout, rs: &[Receipt]) -> Bytes {
    let items: Vec<Bytes> = l
        .shard_ids
        .iter()
        .map(|s| {
            let filtered: Vec<Receipt> = rs
                .iter()
                .filter(|r| l.shard_of(&r.receiver_id) == *s)
                .cloned()
                .collect();
            let mut v = u64b(*s as u128);
            v.extend(encode_receipts(&filtered));
            sha256(&v).to_vec()
        })
        .collect();
    let leaves: Vec<Bytes> = items.iter().map(|it| sha256(it).to_vec()).collect();
    ns::merkle_root(&leaves)
}

/// `ownIntervals l own` (`PrepD0.ownIntervals`).
fn own_intervals(l: &Layout, own: u64) -> Vec<(Option<Bytes>, Option<Bytes>)> {
    (0..=(l.boundaries.len()))
        .filter_map(|k| {
            if l.shard_ids.get(k).copied().unwrap_or(0) == own {
                Some((
                    lex_max_opt(&l.boundaries[..k.min(l.boundaries.len())]),
                    l.boundaries.get(k).cloned(),
                ))
            } else {
                None
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// prepClaim / prepBody / prep
// ---------------------------------------------------------------------------

/// Claim-only part of the prepared statement (`PrepC`).
pub struct PrepC {
    pub hdr: PrepHdr,
    pub lists: Vec<SrcList>,
    pub bnds: Vec<(Option<Bytes>, Option<Bytes>)>,
    pub sched: Vec<SchedPub>,
    pub l: Layout,
    pub h: ChunkInner,
    pub ctx_b2: ApplyCtx,
    pub rs_data: u64,
    pub rs_total: u64,
    pub allowed: u64,
    pub own_congestion: CongestionInfo,
}

/// `prepClaim cb`.
pub fn prep_claim(cb: &[u8]) -> Result<PrepC, String> {
    let k = walk_d0(cb)?;
    let c = &k.c;
    if c.protocol_version != 86 {
        return err("out of domain (c.pv86)");
    }
    if c.epochs.len() != 1 {
        return err("out of domain (c.single_epoch): more than one epoch");
    }
    let ep = c.epochs.first().cloned().unwrap_or_default();
    if !(ep.epoch_id == c.epoch_id && ep.protocol_version == c.protocol_version) {
        return err("invalid: epoch table does not match epoch_id / protocol_version");
    }
    let l = &k.layout;
    if !(1 <= l.num_shards() && l.num_shards() <= 64) {
        return err("out of domain (c.layout)");
    }
    if !rs_genesis_params_ok(c.rs_data_parts, c.rs_total_parts) {
        return err("invalid: Reed-Solomon parameters");
    }
    if c.blocks.len() > 32 {
        return err("out of domain (c.segment)");
    }
    if !c.tx_valid.is_empty() {
        return err("out of domain (c.no_tx_flags)");
    }
    if c.epoch_start_after.len() != c.blocks.len() {
        return err("invalid: epoch_start_after length");
    }
    if !c.epoch_start_after.iter().all(|&x| x == 0) {
        return err("out of domain (c.single_epoch): epoch start");
    }
    if !c
        .apply_facts
        .iter()
        .all(|f| !f.has_validator_update && !f.has_split_gate)
    {
        return err("out of domain (c.no_split_gate)");
    }
    if k.blks.is_empty() {
        return err("invalid: empty chain segment");
    }
    if !k.blks.iter().all(|b| b.hdr.epoch_id == c.epoch_id) {
        return err("out of domain (c.single_epoch)");
    }
    let hashes: Vec<Bytes> = k.blks.iter().map(|b| b.hdr.hash.clone()).collect();
    if hashes.first().map(|h| h.as_slice()) != Some(k.h_chunk.prev_block_hash.as_slice()) {
        return err("invalid: segment does not start at prev_block_hash");
    }
    for (b, h) in k.blks.iter().zip(hashes.iter().skip(1)) {
        if &b.hdr.prev_hash != h {
            return err("invalid: segment is not hash-linked");
        }
    }
    if !k.blks.iter().all(|b| b.slots.len() == l.num_shards()) {
        return err("invalid: slot count");
    }
    // A8 (claim-only, `ChunkValidationV0a.a8`): distinct `to_shard`s per chunk's requests
    if !k.blks.iter().all(|b| {
        b.slots.iter().all(|(_, ci)| {
            let ts: Vec<u64> = ci.bw_requests.iter().map(|r| r.to_shard).collect();
            ts.iter().enumerate().all(|(i, t)| !ts[..i].contains(t))
        })
    }) {
        return err(
            "out of domain (c.bw_requests): a chunk's bandwidth requests repeat a to_shard",
        );
    }
    if !k
        .blks
        .iter()
        .all(|b| b.slots.iter().all(|(hi, _)| *hi <= b.hdr.height))
    {
        return err("invalid: height_included above block height (block_congestion_info panics)");
    }
    let b2 = &k.blks[k.b2i];
    if b2.hdr.prev_hash == zero32() {
        return err("out of domain (c.not_genesis)");
    }
    if c.genesis_chunk_extra.is_some() {
        return err("invalid: genesis_chunk_extra for a non-genesis main block");
    }
    if k.stop + 1 != k.blks.len() {
        return err("invalid: segment is not exactly the blocks the validator reads");
    }
    if c.apply_facts.len() != 1 + k.implicit_blks.len() {
        return err("invalid: apply_facts length");
    }
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("invalid: walk")?;
    let slot_b2 = k.slot_b2.clone();
    // A1
    if slot_b2.gas_limit > MAX_GAS_LIMIT_D0 {
        return err("out of domain (c.gas_limit): chunk gas_limit above 10^15");
    }
    // 3.3 / 3.4: source lists in applied order
    let mut lists: Vec<SrcList> = Vec::new();
    for s_blk in &k.source_blks {
        let mut srcs: Vec<SrcList> = Vec::new();
        for (i, (hi, ci)) in s_blk.slots.iter().enumerate() {
            if *hi == s_blk.hdr.height {
                srcs.push(SrcList {
                    key: chunk_hash(&s_blk.slot_inner[i], &ci.encoded_merkle_root),
                    from_shard: ci.shard_id,
                    root: ci.prev_outgoing_receipts_root.clone(),
                });
            }
        }
        if !shuffle_with_seed(&mut srcs, &s_blk.hdr.prev_hash) {
            return err("invalid: shuffle fuel exhausted (probability < 2^-1024)");
        }
        lists.extend(srcs);
    }
    if slot_b2.tx_root != zero32() {
        return err("invalid: transaction root of the last chunk");
    }
    let own = slot_b2.congestion.clone();
    if !(own.delayed_gas == 0 && own.buffered_gas == 0 && own.receipt_bytes == 0) {
        return err("out of domain (c.own_congestion_zero)");
    }
    // scheduler public data per applied block (B2, then implicit oldest first)
    let ctx_b2 = block_ctx(
        l,
        k.h_chunk.shard_id,
        slot_b2.gas_limit,
        b2,
        prev_b2.hdr.next_gas_price,
    );
    let mut ctxs = vec![ctx_b2.clone()];
    for m in &k.implicit_blks {
        ctxs.push(block_ctx(
            l,
            k.h_chunk.shard_id,
            slot_b2.gas_limit,
            m,
            m.hdr.next_gas_price,
        ));
    }
    let mut sched = Vec::with_capacity(ctxs.len());
    for ctx in &ctxs {
        match sched_pub(
            &ctx.layout.shard_ids,
            &ctx.statuses,
            &ctx.requests,
            &ctx.prev_block_hash,
        ) {
            Some(p) => sched.push(p),
            None => return err("invalid: bandwidth scheduler aborted (StorageInconsistentState)"),
        }
    }
    let allowed = l
        .shard_ids
        .get(((b2.hdr.height as u128 + k.idx as u128) % l.num_shards() as u128) as usize)
        .copied()
        .unwrap_or(k.h_chunk.shard_id);
    // A12 (claim-only, `ChunkValidationV0a.a12`): one boundary account fewer than shard ids
    if l.num_shards() != l.boundaries.len() + 1 {
        return err(
            "out of domain (c.layout_wf): the shard layout does not have one boundary fewer than shard ids",
        );
    }
    let hdr = PrepHdr {
        k: k.implicit_blks.len() as u64,
        n: 0,
        own: k.h_chunk.shard_id,
        own_idx: k.idx as u64,
        num_shards: l.num_shards() as u64,
        height: b2.hdr.height,
        gas_price: prev_b2.hdr.next_gas_price,
        gas_limit: slot_b2.gas_limit,
        prev_state_root: slot_b2.prev_state_root.clone(),
        post_state_root: k.h_chunk.prev_state_root.clone(),
        outcome_root: k.h_chunk.prev_outcome_root.clone(),
        balance_burnt: k.h_chunk.prev_balance_burnt,
    };
    Ok(PrepC {
        hdr,
        lists,
        bnds: own_intervals(l, k.h_chunk.shard_id),
        sched,
        l: l.clone(),
        h: k.h_chunk.clone(),
        ctx_b2,
        rs_data: c.rs_data_parts,
        rs_total: c.rs_total_parts,
        allowed,
        own_congestion: own,
    })
}

/// `prepBody pc h`.
pub fn prep_body(pc: &PrepC, h: &Hint) -> Result<Prep, String> {
    let ctx = &pc.ctx_b2;
    let refunds = prep::decode_body(&h.body)?;
    if !refunds
        .iter()
        .all(|r| status_shards(ctx).contains(&ctx.layout.shard_of(&r.receiver_id)))
    {
        return err("out of domain (e.forwarded): generated receipt buffered");
    }
    if !fwd_gas_ok(ctx, &refunds) {
        return err("out of domain (e.forwarded): generated receipt buffered");
    }
    let fwd = fwd_links(ctx, &refunds);
    if !fwd.iter().all(|(_, d)| *d < FWD_DEMAND_MAX) {
        return err("out of domain (e.forwarded): forwarding demand above 2^24");
    }
    // `Nat` arithmetic: `n < 2^32` and `G < 2^38`, so the products fit in `u128`.
    if !(h.n == 0 || (h.n as u128 - 1) * GAS_PER_RECEIPT < ctx.gas_limit as u128) {
        return err("out of domain (e.compute): receipt delayed by the compute limit");
    }
    // 3.7 header comparison (claim/hint part)
    let hc = &pc.h;
    if !hc.proposals.is_empty() {
        return err("invalid: InvalidValidatorProposals");
    }
    if hc.gas_limit != pc.hdr.gas_limit {
        return err("invalid: InvalidGasLimit");
    }
    if hc.prev_gas_used as u128 != h.n as u128 * GAS_PER_RECEIPT {
        return err("invalid: InvalidGasUsed");
    }
    if hc.prev_outgoing_receipts_root != outgoing_receipts_root(&pc.l, &refunds) {
        return err("invalid: InvalidReceiptsProof");
    }
    let want_congestion = CongestionInfo {
        allowed_shard: pc.allowed,
        ..pc.own_congestion.clone()
    };
    if hc.congestion != want_congestion {
        return err("invalid: InvalidCongestionInfo");
    }
    if !hc.bw_requests.is_empty() {
        return err("invalid: InvalidBandwidthRequests");
    }
    if hc.proposed_split.is_some() {
        return err("invalid: InvalidChunkHeaderShardSplit");
    }
    if hc.tx_root != zero32() {
        return err("invalid: InvalidTxRoot");
    }
    match encoded_merkle_root(pc.rs_data, pc.rs_total, &h.body) {
        None => return err("invalid: Reed-Solomon parameters"),
        Some((emr, len)) => {
            if hc.encoded_merkle_root != emr {
                return err("invalid: InvalidChunkEncodedMerkleRoot");
            }
            if hc.encoded_length != len {
                return err("invalid: InvalidChunkEncodedLength");
            }
        }
    }
    Ok(Prep {
        hdr: PrepHdr {
            n: h.n,
            ..pc.hdr.clone()
        },
        lists: pc.lists.clone(),
        bnds: pc.bnds.clone(),
        sched: pc.sched.clone(),
        body: h.body.clone(),
        fwd,
    })
}

/// `prepD0 cb h = prepClaim cb >>= prepBody · h`.
pub fn prep(cb: &[u8], h: &Hint) -> Result<Prep, String> {
    let pc = prep_claim(cb)?;
    prep_body(&pc, h)
}

/// The `Hint` read off the relation's own execution: not the D0 execution,
/// but the `Hint` bytes/decode.  Crate-internal use only.
pub fn hint_from(n: u64, body: Bytes) -> Hint {
    Hint { n, body }
}

// Keep `borsh_bytes`, `u16b`, `u128b` referenced for the header codec parity
// (the `prep.rs` codec uses them; this module's `F64`/wire paths do not).
#[allow(dead_code)]
fn _enc_helpers() {
    let _ = borsh_bytes(&[]);
    let _ = u16b(0);
    let _ = u128b(0);
}

// ---------------------------------------------------------------------------
// `prep_json`: the Lean field-name JSON of a `Prep` (`PrepV3.jsonPrep`),
// consumed by `npudr prep-encode`.
// ---------------------------------------------------------------------------

fn jbytes(b: &[u8]) -> serde_json::Value {
    serde_json::Value::Array(b.iter().map(|&x| serde_json::json!(x)).collect())
}
fn jopt_bytes(b: &Option<Bytes>) -> serde_json::Value {
    match b {
        None => serde_json::Value::Null,
        Some(v) => jbytes(v),
    }
}

/// Serialize a `Prep` with the exact Lean `prep_json` field names.
pub fn to_json(p: &Prep) -> serde_json::Value {
    let hdr = &p.hdr;
    let hdr_j = serde_json::json!({
        "K": hdr.k, "n": hdr.n, "own": hdr.own, "ownIdx": hdr.own_idx,
        "numShards": hdr.num_shards, "height": hdr.height, "gasPrice": hdr.gas_price,
        "gasLimit": hdr.gas_limit, "prevStateRoot": jbytes(&hdr.prev_state_root),
        "postStateRoot": jbytes(&hdr.post_state_root), "outcomeRoot": jbytes(&hdr.outcome_root),
        "balanceBurnt": hdr.balance_burnt
    });
    let lists: Vec<serde_json::Value> = p
        .lists
        .iter()
        .map(|s| {
            serde_json::json!({
                "key": jbytes(&s.key), "fromShard": s.from_shard, "root": jbytes(&s.root)
            })
        })
        .collect();
    let bnds: Vec<serde_json::Value> = p
        .bnds
        .iter()
        .map(|(lo, hi)| serde_json::json!([jopt_bytes(lo), jopt_bytes(hi)]))
        .collect();
    let sched: Vec<serde_json::Value> = p.sched.iter().map(sched_pub_json).collect();
    serde_json::json!({
        "hdr": hdr_j,
        "lists": lists,
        "bnds": bnds,
        "sched": sched,
        "body": jbytes(&p.body),
        "fwd": p.fwd.iter().map(|(s, t)| serde_json::json!([s, t])).collect::<Vec<_>>()
    })
}

fn sched_pub_json(sp: &SchedPub) -> serde_json::Value {
    let params = serde_json::json!({
        "base": sp.params.base,
        "maxShardBandwidth": sp.params.max_shard_bandwidth,
        "maxSingleGrant": sp.params.max_single_grant,
        "maxReceiptSize": sp.params.max_receipt_size,
        "maxAllowance": sp.params.max_allowance
    });
    let raw: Vec<serde_json::Value> = sp
        .raw
        .iter()
        .map(|(sender, brs)| {
            let bs: Vec<serde_json::Value> = brs
                .iter()
                .map(|b| serde_json::json!({ "toShard": b.to_shard, "bitmap": jbytes(&b.bitmap) }))
                .collect();
            serde_json::json!([sender, bs])
        })
        .collect();
    serde_json::json!({
        "ids": sp.ids,
        "params": params,
        "allowed": sp.allowed,
        "raw": raw,
        "values": sp.values,
        "seed": jbytes(&sp.seed),
        "allShardsHash": jbytes(&sp.all_shards_hash)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn f64_one_roundtrips() {
        assert_eq!(F64::of_nat(1), F64::one());
        assert_eq!(F64::div(F64::of_nat(1), F64::of_nat(2)).round_nat(), 1);
        assert_eq!(F64::of_nat(3).round_nat(), 3);
        assert_eq!(F64::fmax(F64::one(), F64::zero()), F64::one());
    }

    #[test]
    fn gf_mul_matches_known() {
        assert_eq!(gf_mul(0, 5), 0);
        assert_eq!(gf_mul(1, 5), 5);
        assert_eq!(gf_mul(2, 0x80), 0x1d);
        let mut a = 1u32;
        for _ in 0..255 {
            assert_ne!(a, 0);
            a = gf_mul(a, 2);
        }
        assert_eq!(a, 1);
        for b in 1..256u32 {
            assert_eq!(gf_mul(b, gf_inv(b)), 1, "inverse of {b}");
        }
    }

    #[test]
    fn rs_vectors_match_lean() {
        // `ReedSolomon.lean` kernel vectors.
        let (r1, l1) = encoded_merkle_root(1, 3, &[0x02, 0x00, 0x00, 0x00, 0xb3, 0x61]).unwrap();
        assert_eq!(l1, 6);
        assert_eq!(
            r1,
            vec![
                0x0c, 0xbe, 0x69, 0x31, 0x07, 0x2d, 0x1d, 0x5d, 0x2c, 0xdf, 0xcd, 0x48, 0x57, 0x9c,
                0xdf, 0x91, 0xd1, 0xa2, 0x7c, 0x8f, 0x84, 0x7f, 0x87, 0x3e, 0x7f, 0xa0, 0x29, 0x31,
                0xcb, 0x40, 0x9f, 0xc1
            ]
        );
        let (r2, l2) = encoded_merkle_root(2, 8, &[0x02, 0x00, 0x00, 0x00, 0x93, 0xe4]).unwrap();
        assert_eq!(l2, 6);
        assert_eq!(
            r2,
            vec![
                0x97, 0x5f, 0x53, 0x4f, 0x99, 0xf8, 0x24, 0xf3, 0x2f, 0x7d, 0xb7, 0x46, 0x17, 0x3c,
                0x7f, 0xc7, 0x55, 0xf2, 0xbc, 0x83, 0x01, 0x5b, 0xa8, 0x7b, 0xd6, 0xf6, 0x82, 0x4a,
                0xb7, 0x28, 0xf9, 0x38
            ]
        );
    }

    #[test]
    fn shuffle_permutes() {
        let mut v: Vec<u64> = (0..12).collect();
        assert!(shuffle_with_seed(&mut v, &[1, 2, 3, 4, 5, 6, 7, 8]));
        let mut sorted = v.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..12).collect::<Vec<_>>());
    }
}
