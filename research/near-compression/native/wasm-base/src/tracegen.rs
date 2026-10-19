//! Trace generation for `wasm-base-v1`: executes the code records (the verifier-side output of
//! `wasmbase-tool prep`) and fills every chip row by column name.  It is an independent
//! implementation of family F1 over the records; its results are compared with the Lean spec run
//! (`prep.json`) and with the Python reference interpreter.
use crate::air::{AirSpec, TableSpec};
use p3_baby_bear::BabyBear as F;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use serde_json::Value;
use std::collections::HashMap;

pub const OP_NEXT: u64 = 0x101;
pub const OP_JUMP: u64 = 0x102;
pub const OP_JIF: u64 = 0x103;
pub const OP_HALT: u64 = 0x104;
pub const OP_HIF: u64 = 0x105;

#[derive(Clone, Debug)]
pub struct Prep {
    pub records: Vec<[u64; 8]>,
    pub local_tags: Vec<u64>,
    pub arity: u64,
    pub res_tag: u64,
    pub g0: u128,
    pub g_final: u128,
    pub regular: u128,
    pub steps: u64,
    pub status: String,
    pub stack: Vec<(u64, [u64; 4])>,
    pub max_fee: u64,
}

impl Prep {
    pub fn parse(text: &str) -> Prep {
        let v: Value = serde_json::from_str(text).expect("prep json");
        assert!(v["eligible"].as_bool().unwrap(), "program not eligible: {text}");
        let nums = |x: &Value| -> Vec<u64> { x.as_array().unwrap().iter().map(|n| n.as_u64().unwrap()).collect() };
        Prep {
            records: v["records"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| nums(r).try_into().unwrap())
                .collect(),
            local_tags: nums(&v["localTags"]),
            arity: v["arity"].as_u64().unwrap(),
            res_tag: v["resTag"].as_u64().unwrap(),
            g0: v["g0"].as_u64().unwrap() as u128,
            g_final: v["gFinal"].as_u64().unwrap() as u128,
            regular: v["regularOpCost"].as_u64().unwrap() as u128,
            steps: v["steps"].as_u64().unwrap(),
            status: v["status"].as_str().unwrap().to_string(),
            stack: v["stack"]
                .as_array()
                .unwrap()
                .iter()
                .map(|e| (e["tag"].as_u64().unwrap(), nums(&e["limbs"]).try_into().unwrap()))
                .collect(),
            max_fee: v["maxFee"].as_u64().unwrap(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Ent {
    tag: u64,
    val: u64,
    tp: u64,
}

pub fn limbs(x: u64) -> [u64; 4] {
    [x & 0xffff, (x >> 16) & 0xffff, (x >> 32) & 0xffff, x >> 48]
}
pub fn bytes(x: u64) -> [u64; 8] {
    std::array::from_fn(|i| (x >> (8 * i)) & 0xff)
}
fn from_limbs(l: &[u64; 4]) -> u64 {
    l[0] | (l[1] << 16) | (l[2] << 32) | (l[3] << 48)
}
fn fe(x: u64) -> F {
    F::from_u64(x)
}
fn fi(x: i64) -> F {
    if x >= 0 { F::from_u64(x as u64) } else { -F::from_u64((-x) as u64) }
}
fn sg(v: u64, w: u32) -> i128 {
    let v = v as i128;
    if (v >> (w - 1)) & 1 == 1 { v - (1i128 << w) } else { v }
}

struct Tab<'a> {
    spec: &'a TableSpec,
    idx: HashMap<String, usize>,
    rows: Vec<Vec<F>>,
}
impl<'a> Tab<'a> {
    fn new(spec: &'a TableSpec) -> Self {
        let idx = spec.cols.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
        Tab { spec, idx, rows: vec![] }
    }
    fn row(&mut self) -> Row<'_, 'a> {
        self.rows.push(vec![F::ZERO; self.spec.cols.len()]);
        Row { t: self }
    }
}
struct Row<'b, 'a> {
    t: &'b mut Tab<'a>,
}
impl Row<'_, '_> {
    fn s(&mut self, name: &str, v: F) -> &mut Self {
        let i = *self.t.idx.get(name).unwrap_or_else(|| panic!("{}: no col {name}", self.t.spec.name));
        *self.t.rows.last_mut().unwrap().get_mut(i).unwrap() = v;
        self
    }
    fn u(&mut self, name: &str, v: u64) -> &mut Self {
        self.s(name, fe(v))
    }
    fn limbs(&mut self, p: &str, l: [u64; 4]) -> &mut Self {
        for (i, x) in l.iter().enumerate() {
            self.u(&format!("{p}{i}"), *x);
        }
        self
    }
    fn bytes(&mut self, p: &str, b: [u64; 8]) -> &mut Self {
        for (i, x) in b.iter().enumerate() {
            self.u(&format!("{p}{i}"), *x);
        }
        self
    }
}

pub struct Gen {
    pub mats: Vec<RowMajorMatrix<F>>,
    pub pubs: Vec<F>,
    pub rows_per_table: Vec<(String, usize)>,
    pub result: Option<(u64, u64)>,
    pub steps: u64,
    pub s_units: u64,
}

struct St {
    r16: Vec<u32>,
    byte: Vec<Vec<u32>>,
}
impl St {
    fn r16(&mut self, v: u64) {
        assert!(v < 65536, "range check out of range: {v}");
        self.r16[v as usize] += 1;
    }
    fn byte(&mut self, kind: usize, x: u64, y: u64) -> u64 {
        assert!(x < 256 && y < 256);
        self.byte[kind][(x + 256 * y) as usize] += 1;
        match kind {
            0 => 0,
            1 => x & y,
            2 => x | y,
            _ => x ^ y,
        }
    }
    /// `tp < ts`: returns `hi` and records the two lookups.
    fn tchk(&mut self, ts: u64, tp: u64) -> u64 {
        assert!(tp < ts, "channel time order violated: tp {tp} ts {ts}");
        let d = ts - tp - 1;
        let hi = d >> 16;
        assert!(hi < (1 << 14));
        self.r16(d & 0xffff);
        self.r16(4 * hi);
        hi
    }
}

fn binop(op: u64, a: u64, b: u64) -> u64 {
    let w: u32 = if (0x7C..=0x8A).contains(&op) { 64 } else { 32 };
    let m: u64 = if w == 64 { u64::MAX } else { 0xffff_ffff };
    let base = if w == 64 { 0x7C } else { 0x6A };
    let k = (b % w as u64) as u32;
    match op - base {
        0 => a.wrapping_add(b) & m,
        1 => a.wrapping_sub(b) & m,
        2 => a.wrapping_mul(b) & m,
        7 => a & b,
        8 => a | b,
        9 => a ^ b,
        10 => (a << k) & m,
        11 => ((sg(a, w) >> k) as u64) & m,
        12 => a >> k,
        13 => if k == 0 { a } else { ((a << k) | (a >> (w - k))) & m },
        14 => if k == 0 { a } else { ((a >> k) | (a << (w - k))) & m },
        _ => panic!("binop {op:#x}"),
    }
}

fn relop(op: u64, a: u64, b: u64) -> u64 {
    let w: u32 = if op >= 0x50 { 64 } else { 32 };
    let k = op - if w == 64 { 0x51 } else { 0x46 };
    (match k {
        0 => a == b,
        1 => a != b,
        2 => sg(a, w) < sg(b, w),
        3 => a < b,
        4 => sg(a, w) > sg(b, w),
        5 => a > b,
        6 => sg(a, w) <= sg(b, w),
        7 => a <= b,
        8 => sg(a, w) >= sg(b, w),
        _ => a >= b,
    }) as u64
}

const CMP_FLAGS: [&str; 11] = [
    "f_eqz", "f_eq", "f_ne", "f_lts", "f_ltu", "f_gts", "f_gtu", "f_les", "f_leu", "f_ges", "f_geu",
];

pub fn generate(air: &AirSpec, prep: &Prep) -> Gen {
    let t = |n: &str| &air.tables[air.index(n)];
    let mut add = Tab::new(t("ADD"));
    let mut bit = Tab::new(t("BIT"));
    let mut mul = Tab::new(t("MUL"));
    let mut shift = Tab::new(t("SHIFT"));
    let mut cmp = Tab::new(t("CMP"));
    let mut cnst = Tab::new(t("CONST"));
    let mut stk = Tab::new(t("STACK"));
    let mut ctrl = Tab::new(t("CTRL"));
    let mut loc = Tab::new(t("LOCAL"));
    let mut st = St { r16: vec![0; 65536], byte: vec![vec![0; 65536]; 4] };
    let mut fetch = vec![0u64; prep.records.len()];

    let mut stack: Vec<Ent> = vec![];
    let mut locals: Vec<Ent> = prep.local_tags.iter().map(|&tag| Ent { tag, val: 0, tp: 0 }).collect();
    let (mut pc, mut ts, mut s) = (0u64, 1u64, 0u64);
    let halt_pc;
    loop {
        let rec = prep.records[pc as usize];
        assert_eq!(rec[0], pc);
        let (op, h, fee) = (rec[1], rec[2], rec[3]);
        assert_eq!(h as usize, stack.len(), "static height mismatch at pc {pc}");
        fetch[pc as usize] += 1;
        let hdr = |r: &mut Row| {
            r.u("pc", pc).u("ts", ts).u("S", s).u("h", h).u("fee", fee);
        };
        let mut next = pc + 1;
        let mut halted = false;
        match op {
            0x41 | 0x42 => {
                let is64 = op - 0x41;
                let v = from_limbs(&[rec[4], rec[5], rec[6], rec[7]]);
                let mut r = cnst.row();
                hdr(&mut r);
                r.u("act", 1).u("is64", is64).limbs("imm", limbs(v));
                stack.push(Ent { tag: is64, val: v, tp: ts });
            }
            0x6A | 0x6B | 0x7C | 0x7D => {
                let is64 = (op >= 0x7C) as u64;
                let sub = (op & 1 == 1) as u64; // 0x6B, 0x7D
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (x, z) = if sub == 1 { (rv, a.val) } else { (a.val, rv) };
                let (xl, bl, zl) = (limbs(x), limbs(b.val), limbs(z));
                let nl = if is64 == 1 { 4 } else { 2 };
                let mut c = [0u64; 4];
                let mut carry = 0;
                for i in 0..nl {
                    let tot = xl[i] + bl[i] + carry;
                    assert_eq!(tot & 0xffff, zl[i]);
                    carry = tot >> 16;
                    c[i] = carry;
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                for l in limbs(rv) {
                    st.r16(l);
                }
                let mut r = add.row();
                hdr(&mut r);
                r.u("f_add", 1 - sub).u("f_sub", sub).u("is64", is64);
                r.limbs("a", limbs(a.val)).u("ta", a.tp).u("ha", ha);
                r.limbs("b", limbs(b.val)).u("tb", b.tp).u("hb", hb);
                r.limbs("r", limbs(rv)).limbs("c", c);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x71..=0x73 | 0x83..=0x85 => {
                let is64 = (op >= 0x83) as u64;
                let k = op - if is64 == 1 { 0x83 } else { 0x71 };
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (ab, bb, rb) = (bytes(a.val), bytes(b.val), bytes(rv));
                for j in 0..8 {
                    assert_eq!(st.byte(k as usize + 1, ab[j], bb[j]), rb[j]);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = bit.row();
                hdr(&mut r);
                r.u("f_and", (k == 0) as u64).u("f_or", (k == 1) as u64).u("f_xor", (k == 2) as u64);
                r.u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.bytes("bb", bb).u("tb", b.tp).u("hb", hb).bytes("rb", rb);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x6C | 0x7E => {
                let is64 = (op == 0x7E) as u64;
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (ab, bb, rb) = (bytes(a.val), bytes(b.val), bytes(rv));
                let nb = if is64 == 1 { 8 } else { 4 };
                let mut cy = [0u64; 8];
                let mut carry = 0u64;
                for k in 0..nb {
                    let mut tot = carry;
                    for i in 0..=k {
                        tot += ab[i] * bb[k - i];
                    }
                    assert_eq!(tot & 0xff, rb[k]);
                    carry = tot >> 8;
                    cy[k] = carry;
                }
                for i in 0..4 {
                    st.byte(0, ab[2 * i], ab[2 * i + 1]);
                    st.byte(0, bb[2 * i], bb[2 * i + 1]);
                    st.byte(0, rb[2 * i], rb[2 * i + 1]);
                }
                for c in cy {
                    st.r16(c);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = mul.row();
                hdr(&mut r);
                r.u("act", 1).u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.bytes("bb", bb).u("tb", b.tp).u("hb", hb).bytes("rb", rb).bytes("cy", cy);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x74..=0x78 | 0x86..=0x8A => {
                let is64 = (op >= 0x86) as u64;
                let kind = op - if is64 == 1 { 0x86 } else { 0x74 }; // shl, shr_s, shr_u, rotl, rotr
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let w: u64 = if is64 == 1 { 64 } else { 32 };
                let b0 = b.val & 0xffff;
                let k = b0 % w;
                let q = b0 / w;
                let left = kind == 0 || kind == 3;
                let e = if left { k } else { w - k };
                let (ebv, t) = (e % 8, e / 8);
                let pow = 1u64 << ebv;
                let ab = bytes(a.val);
                let top = if is64 == 1 { ab[7] } else { ab[3] };
                let sgn = top >> 7;
                let rest = top & 0x7f;
                let fill = if kind == 1 { 255 * sgn } else { 0 };
                let aext: Vec<u64> = (0..16)
                    .map(|i| {
                        if i < 4 { ab[i] }
                        else if i < 8 { if is64 == 1 { ab[i] } else { fill } }
                        else if is64 == 1 { fill } else { 0 }
                    })
                    .collect();
                let nb = if is64 == 1 { 16 } else { 8 };
                let (mut pb, mut cy) = ([0u64; 16], [0u64; 16]);
                let mut carry = 0u64;
                for j in 0..nb {
                    let m = if j as u64 >= t { aext[j - t as usize] } else { 0 };
                    let tot = pow * m + carry;
                    pb[j] = tot & 0xff;
                    carry = tot >> 8;
                    cy[j] = carry;
                }
                let flo = matches!(kind, 0 | 3 | 4) as u64;
                let fhi = matches!(kind, 1 | 2 | 3 | 4) as u64;
                let rbytes: Vec<u64> = (0..8)
                    .map(|j| {
                        if j < 4 {
                            flo * pb[j] + fhi * if is64 == 1 { pb[j + 8] } else { pb[j + 4] }
                        } else if is64 == 1 {
                            flo * pb[j] + fhi * pb[j + 8]
                        } else {
                            0
                        }
                    })
                    .collect();
                let rcalc: u64 = rbytes.iter().enumerate().map(|(j, &x)| x << (8 * j)).sum();
                assert_eq!(rcalc, rv, "shift construction op {op:#x} a {:#x} b {:#x}", a.val, b.val);
                st.r16(q);
                st.byte(0, 2 * rest, 0);
                for i in 0..4 {
                    st.byte(0, ab[2 * i], ab[2 * i + 1]);
                }
                for i in 0..8 {
                    st.byte(0, pb[2 * i], pb[2 * i + 1]);
                    st.byte(0, cy[2 * i], cy[2 * i + 1]);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = shift.row();
                hdr(&mut r);
                for (i, f) in ["f_shl", "f_shrs", "f_shru", "f_rotl", "f_rotr"].iter().enumerate() {
                    r.u(f, (kind == i as u64) as u64);
                }
                r.u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.limbs("b", limbs(b.val)).u("tb", b.tp).u("hb", hb);
                for j in 0..6 {
                    r.u(&format!("kb{j}"), (k >> j) & 1);
                }
                r.u("q", q);
                for j in 0..3 {
                    r.u(&format!("eb{j}"), (ebv >> j) & 1);
                }
                for j in 0..9 {
                    r.u(&format!("el{j}"), (t == j) as u64);
                }
                r.u("sgn", sgn).u("rest", rest);
                for j in 0..16 {
                    r.u(&format!("P{j}"), pb[j]).u(&format!("cy{j}"), cy[j]);
                }
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x45..=0x5A => {
                let is64 = (op >= 0x50) as u64;
                let idx = (op - if is64 == 1 { 0x50 } else { 0x45 }) as usize;
                let eqz = idx == 0;
                let b = if eqz { Ent { tag: is64, val: 0, tp: 0 } } else { stack.pop().unwrap() };
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let res = if eqz { (a.val == 0) as u64 } else { relop(op, a.val, b.val) };
                let swap = matches!(idx, 5 | 6 | 7 | 8);
                let signed = matches!(idx, 3 | 5 | 7 | 9);
                let w: u32 = if is64 == 1 { 64 } else { 32 };
                let (x, y) = if swap { (b.val, a.val) } else { (a.val, b.val) };
                let flip = |v: u64| if signed { v ^ (1u64 << (w - 1)) } else { v };
                let (xl, yl) = (limbs(flip(x)), limbs(flip(y)));
                let nl = if is64 == 1 { 4 } else { 2 };
                let (mut d, mut br) = ([0u64; 4], [0u64; 4]);
                let mut borrow = 0i64;
                for i in 0..nl {
                    let v = xl[i] as i64 - yl[i] as i64 - borrow;
                    let (dv, bo) = if v < 0 { (v + 65536, 1) } else { (v, 0) };
                    d[i] = dv as u64;
                    br[i] = bo as u64;
                    borrow = bo;
                }
                let lt = borrow as u64;
                let zsum: u64 = d.iter().sum();
                let eqf = (zsum == 0) as u64;
                let calc = match idx {
                    0 | 1 => eqf,
                    2 => 1 - eqf,
                    3 | 4 | 5 | 6 => lt,
                    _ => 1 - lt,
                };
                assert_eq!(calc, res, "cmp construction op {op:#x}");
                let (al, bl) = (limbs(a.val), limbs(b.val));
                let (ta_, tb_) = (if is64 == 1 { al[3] } else { al[1] }, if is64 == 1 { bl[3] } else { bl[1] });
                let (sa, ra, sb, rb) = (ta_ >> 15, ta_ & 0x7fff, tb_ >> 15, tb_ & 0x7fff);
                for v in d {
                    st.r16(v);
                }
                st.r16(2 * ra);
                st.r16(2 * rb);
                let ha = st.tchk(ts, a.tp);
                let hb = if eqz { 0 } else { st.tchk(ts, b.tp) };
                let mut r = cmp.row();
                hdr(&mut r);
                for (i, f) in CMP_FLAGS.iter().enumerate() {
                    r.u(f, (i == idx) as u64);
                }
                r.u("is64", is64).limbs("a", al).u("ta", a.tp).u("ha", ha);
                r.limbs("b", bl).u("tb", b.tp).u("hb", hb);
                r.u("sa", sa).u("ra", ra).u("sb", sb).u("rb", rb).limbs("d", d).limbs("br", br);
                let inv = if zsum == 0 { F::ZERO } else { fe(zsum).inverse() };
                r.s("inv", inv);
                stack.push(Ent { tag: 0, val: res, tp: ts });
            }
            0x1A => {
                let a = stack.pop().unwrap();
                let ha = st.tchk(ts, a.tp);
                let al = limbs(a.val);
                let cz = al[0] + al[1];
                let mut r = stk.row();
                hdr(&mut r);
                r.u("f_drop", 1).u("tagA", a.tag).limbs("A", al).u("tA", a.tp).u("hA", ha);
                r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
            }
            0x1B => {
                let c = stack.pop().unwrap();
                let v2 = stack.pop().unwrap();
                let v1 = stack.pop().unwrap();
                assert!(c.tag == 0 && v1.tag == v2.tag);
                let (hc, h2, h1) = (st.tchk(ts, c.tp), st.tchk(ts, v2.tp), st.tchk(ts, v1.tp));
                let cl = limbs(c.val);
                let cz = cl[0] + cl[1];
                let out = if c.val != 0 { v1 } else { v2 };
                let mut r = stk.row();
                hdr(&mut r);
                r.u("f_sel", 1).u("tagA", 0).limbs("A", cl).u("tA", c.tp).u("hA", hc);
                r.u("tagV", v1.tag);
                let l2 = limbs(v2.val);
                let l1 = limbs(v1.val);
                for i in 0..4 {
                    r.u(&format!("V2_{i}"), l2[i]).u(&format!("V1_{i}"), l1[i]);
                }
                r.u("t2", v2.tp).u("h2", h2).u("t1", v1.tp).u("h1", h1);
                r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                stack.push(Ent { tag: out.tag, val: out.val, tp: ts });
            }
            0x20..=0x22 => {
                let x = rec[4] as usize;
                let old = locals[x];
                let hl = st.tchk(ts, old.tp);
                let mut r = loc.row();
                hdr(&mut r);
                r.u("f_get", (op == 0x20) as u64).u("f_set", (op == 0x21) as u64).u("f_tee", (op == 0x22) as u64);
                r.u("idx", x as u64).u("tagL", old.tag).limbs("L", limbs(old.val)).u("tL", old.tp).u("hL", hl);
                if op == 0x20 {
                    locals[x] = Ent { tag: old.tag, val: old.val, tp: ts };
                    stack.push(Ent { tag: old.tag, val: old.val, tp: ts });
                } else {
                    let v = stack.pop().unwrap();
                    let hv = st.tchk(ts, v.tp);
                    r.u("tagV", v.tag).limbs("V", limbs(v.val)).u("tV", v.tp).u("hV", hv);
                    locals[x] = Ent { tag: v.tag, val: v.val, tp: ts };
                    if op == 0x22 {
                        stack.push(Ent { tag: v.tag, val: v.val, tp: ts });
                    }
                }
            }
            OP_NEXT | OP_JUMP | OP_JIF | OP_HALT | OP_HIF => {
                let tgt = rec[4];
                let mut r = ctrl.row();
                hdr(&mut r);
                let names = ["f_next", "f_jump", "f_jif", "f_halt", "f_hif"];
                r.u(names[(op - OP_NEXT) as usize], 1).u("tgt", tgt);
                let mut taken = false;
                if op == OP_JIF || op == OP_HIF {
                    let c = stack.pop().unwrap();
                    assert_eq!(c.tag, 0);
                    let hc = st.tchk(ts, c.tp);
                    let cl = limbs(c.val);
                    let cz = cl[0] + cl[1];
                    r.u("c0", cl[0]).u("c1", cl[1]).u("tc", c.tp).u("hc", hc);
                    r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                    taken = c.val != 0;
                }
                match op {
                    OP_JUMP => next = tgt,
                    OP_JIF if taken => next = tgt,
                    OP_HALT => halted = true,
                    OP_HIF if taken => halted = true,
                    _ => {}
                }
            }
            _ => panic!("unknown op {op:#x}"),
        }
        s += fee;
        ts += 1;
        if halted {
            halt_pc = pc;
            break;
        }
        pc = next;
    }
    let steps = ts - 1;
    assert_eq!(stack.len() as u64, prep.arity, "final stack size");
    let result = stack.last().map(|e| (e.tag, e.val));

    // BOUNDARY
    let nloc = prep.local_tags.len();
    let bspec = t("BOUNDARY");
    let mut bnd = Tab::new(bspec);
    {
        let mut r = bnd.row();
        r.u("pcf", halt_pc).u("tpr", stack.last().map(|e| e.tp).unwrap_or(0));
        for (j, e) in locals.iter().enumerate() {
            r.u(&format!("ftag{j}"), e.tag).limbs(&format!("fv{j}_"), limbs(e.val)).u(&format!("ftp{j}"), e.tp);
        }
        for (j, m) in fetch.iter().enumerate() {
            r.u(&format!("m{j}"), *m);
        }
    }
    // public values
    let mut pubs = vec![fe(ts), fe(s), fe(prep.arity)];
    let (rtag, rval) = result.unwrap_or((0, 0));
    pubs.push(fe(rtag));
    pubs.extend(limbs(rval).map(fe));
    pubs.extend(prep.local_tags.iter().map(|&x| fe(x)));
    for rec in &prep.records {
        pubs.extend(rec.iter().map(|&x| fe(x)));
    }
    assert_eq!(pubs.len(), air.num_pub);

    // RANGE16 / BYTE
    let mut rng = Tab::new(t("RANGE16"));
    for v in 0..65536u64 {
        rng.row().u("v", v).u("m", st.r16[v as usize] as u64);
    }
    let mut byt = Tab::new(t("BYTE"));
    for key in 0..65536u64 {
        let (x, y) = (key & 0xff, key >> 8);
        let mut r = byt.row();
        for i in 0..8 {
            r.u(&format!("x{i}"), (x >> i) & 1).u(&format!("y{i}"), (y >> i) & 1);
        }
        for k in 0..4 {
            r.u(&format!("m{k}"), st.byte[k][key as usize] as u64);
        }
    }

    let mut tabs: HashMap<String, Tab> = HashMap::new();
    for tb in [bnd, add, bit, mul, shift, cmp, cnst, stk, ctrl, loc, rng, byt] {
        tabs.insert(tb.spec.name.clone(), tb);
    }
    let mut mats = vec![];
    let mut rows_per_table = vec![];
    for spec in &air.tables {
        let tb = tabs.remove(&spec.name).unwrap();
        let w = spec.cols.len();
        let n = tb.rows.len();
        let h = n.max(4).next_power_of_two();
        let mut data: Vec<F> = tb.rows.into_iter().flatten().collect();
        data.resize(h * w, F::ZERO);
        rows_per_table.push((spec.name.clone(), n));
        mats.push(RowMajorMatrix::new(data, w));
    }
    Gen { mats, pubs, rows_per_table, result, steps, s_units: s }
}

/// Check every constraint of every table on every row with the interpreter (cheap pre-check).
pub fn check_constraints(air: &AirSpec, g: &Gen) -> Result<(), String> {
    for (ti, spec) in air.tables.iter().enumerate() {
        let m = &g.mats[ti];
        let w = spec.cols.len();
        let h = m.values.len() / w;
        let pubs: &[F] = if crate::air::JsonAir::reads_pub(spec) { &g.pubs } else { &[] };
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nr = (r + 1) % h;
            let nxt = &m.values[nr * w..(nr + 1) * w];
            let sel = [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)];
            for (ci, c) in spec.constraints.iter().enumerate() {
                let v = c.eval_f(cur, nxt, pubs, sel);
                if v != F::ZERO {
                    return Err(format!("{} row {r} constraint {ci} = {}", spec.name, v.as_canonical_u32()));
                }
            }
        }
    }
    Ok(())
}

/// Bus balance (exact multisets over the trace, all buses) with the interpreter.
pub fn check_buses(air: &AirSpec, g: &Gen) -> Result<(), String> {
    let mut bal: HashMap<(u16, Vec<u32>), i128> = HashMap::new();
    for (ti, spec) in air.tables.iter().enumerate() {
        let m = &g.mats[ti];
        let w = spec.cols.len();
        let h = m.values.len() / w;
        let pubs: &[F] = if crate::air::JsonAir::reads_pub(spec) { &g.pubs } else { &[] };
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nr = (r + 1) % h;
            let nxt = &m.values[nr * w..(nr + 1) * w];
            let sel = [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)];
            for it in &spec.inters {
                let c = it.count.eval_f(cur, nxt, pubs, sel).as_canonical_u32();
                if c == 0 {
                    continue;
                }
                let msg: Vec<u32> = it.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, sel).as_canonical_u32()).collect();
                let e = bal.entry((it.bus, msg)).or_insert(0);
                *e += if it.send { c as i128 } else { -(c as i128) };
            }
        }
    }
    let bad: Vec<_> = bal.iter().filter(|(_, v)| **v != 0).take(5).collect();
    if bad.is_empty() { Ok(()) } else { Err(format!("unbalanced: {bad:?}")) }
}

#[allow(dead_code)]
pub fn felt(x: i64) -> F {
    fi(x)
}
