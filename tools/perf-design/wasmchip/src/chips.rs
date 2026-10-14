//! Opcode-class chips (V3-PERF-DESIGN §2.3) as `npudr` tables, and their trace builders.
//!
//! Buses: 0 = execution state `(pc, ts, fp, u)`; 1 = instruction fetch (13 fields);
//! 2 = memory `(space, addr, l0, l1, l2, l3, t)` (offline memory checking with timestamps,
//! sub-slot `4·ts + k` per access); 3 = 16-bit range; 4 = byte pair `(b0, b1)`.
//! Values are 16-bit limbs (i64 = 4 limbs); `i64.mul` uses bytes (BabyBear: a 16×16-bit
//! product overflows p).
use std::collections::HashMap;
use std::ops::{Add, Mul, Sub};

use npudr::air::{Air, Expr as E, Interaction, Table};
use npudr::field::F;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;

use crate::wasm::{Acc, Cls, RProg, Run, limbs};

pub const STATE: usize = 0;
pub const CODE: usize = 1;
pub const MEM: usize = 2;
pub const RANGE: usize = 3;
pub const PAIR: usize = 4;
pub const NBUS: usize = 5;

// ----- expression sugar -----
#[derive(Clone)]
pub struct X(pub E);
pub fn x(c: usize) -> X {
    X(E::col(c))
}
pub fn nx(c: usize) -> X {
    X(E::nxt(c))
}
pub fn k(v: u64) -> X {
    X(E::c(v))
}
impl Add for X {
    type Output = X;
    fn add(self, o: X) -> X {
        X(E::add(self.0, o.0))
    }
}
impl Sub for X {
    type Output = X;
    fn sub(self, o: X) -> X {
        X(E::sub(self.0, o.0))
    }
}
impl Mul for X {
    type Output = X;
    fn mul(self, o: X) -> X {
        X(E::mul(self.0, o.0))
    }
}
fn sum(v: Vec<X>) -> X {
    v.into_iter().reduce(|a, b| a + b).unwrap_or(k(0))
}

/// Table builder with named columns.
pub struct TB {
    pub name: String,
    pub names: Vec<String>,
    pub cons: Vec<E>,
    pub ints: Vec<Interaction>,
}
impl TB {
    fn new(n: &str) -> TB {
        TB { name: n.into(), names: vec![], cons: vec![], ints: vec![] }
    }
    fn c(&mut self, n: &str) -> usize {
        self.names.push(n.into());
        self.names.len() - 1
    }
    fn cs<const N: usize>(&mut self, n: &str) -> [usize; N] {
        std::array::from_fn(|i| self.c(&format!("{n}{i}")))
    }
    fn con(&mut self, e: X) {
        self.cons.push(e.0)
    }
    fn int(&mut self, bus: usize, send: bool, mult: Vec<X>, msg: Vec<X>) {
        self.ints.push(Interaction {
            bus,
            mult: mult.into_iter().map(|m| m.0).collect(),
            msg: msg.into_iter().map(|m| m.0).collect(),
            send,
        })
    }
    fn table(self) -> Table {
        let mut t = Table {
            name: self.name,
            width: self.names.len(),
            constraints: self.cons,
            interactions: self.ints,
            max_log: 22,
        };
        let b = npudr::aux::bit_constraints(&t);
        t.constraints.extend(b);
        t
    }
}

/// Columns of one memory access.
#[derive(Clone, Copy)]
pub struct AccCols {
    pub t: usize,
    pub lo: usize,
    pub hi: usize,
}

/// Lookup / fetch multiplicity counters filled while building rows.
#[derive(Default)]
pub struct Counts {
    pub range: Vec<u32>,
    pub pair: Vec<u32>,
    pub code: Vec<u32>,
}
impl Counts {
    fn r(&mut self, v: u32) {
        assert!(v < 65536, "range lookup out of range: {v}");
        self.range[v as usize] += 1
    }
}

fn access(tb: &mut TB, act: usize, ts: usize, sub: u64, space: X, addr: X, prev: [X; 4], new: [X; 4], name: &str) -> AccCols {
    let t = tb.c(&format!("{name}_t"));
    let lo = tb.c(&format!("{name}_lo"));
    let hi = tb.c(&format!("{name}_hi"));
    let mut m1 = vec![space.clone(), addr.clone()];
    m1.extend(prev);
    m1.push(x(t));
    tb.int(MEM, false, vec![x(act)], m1);
    let mut m2 = vec![space, addr];
    m2.extend(new);
    m2.push(k(4) * x(ts) + k(sub));
    tb.int(MEM, true, vec![x(act)], m2);
    tb.con(x(act) * (k(4) * x(ts) + k(sub) - x(t) - k(1) - x(lo) - k(65536) * x(hi)));
    tb.int(RANGE, true, vec![x(act)], vec![x(lo)]);
    tb.int(RANGE, true, vec![x(act)], vec![x(hi)]);
    AccCols { t, lo, hi }
}

fn fill_acc(row: &mut [F], c: &AccCols, a: &Acc, cnt: &mut Counts) {
    let d = a.t - a.t_prev - 1;
    row[c.t] = F::from_u32(a.t_prev);
    row[c.lo] = F::from_u32(d & 0xffff);
    row[c.hi] = F::from_u32(d >> 16);
    cnt.r(d & 0xffff);
    cnt.r(d >> 16);
}

fn lim(cols: &[usize]) -> [X; 4] {
    std::array::from_fn(|i| if i < cols.len() { x(cols[i]) } else { k(0) })
}
fn set_limbs(row: &mut [F], cols: &[usize], l: &[u16; 4]) {
    for (i, c) in cols.iter().enumerate() {
        row[*c] = F::from_u32(l[i] as u32);
    }
}

/// Common prefix of every chip row.
#[derive(Clone, Copy)]
pub struct Pre {
    pub act: usize,
    pub pc: usize,
    pub ts: usize,
    pub fp: usize,
    pub u: usize,
    pub fee: usize,
    pub nxt: usize,
}
fn prefix(tb: &mut TB) -> Pre {
    Pre {
        act: tb.c("act"),
        pc: tb.c("pc"),
        ts: tb.c("ts"),
        fp: tb.c("fp"),
        u: tb.c("u"),
        fee: tb.c("fee"),
        nxt: tb.c("nxt"),
    }
}
/// State in/out and fetch. `npc` = next-pc expression; fetch fields after (pc, cls).
fn control(tb: &mut TB, p: &Pre, cls: Cls, npc: X, f: [X; 11]) {
    tb.int(STATE, false, vec![x(p.act)], vec![x(p.pc), x(p.ts), x(p.fp), x(p.u)]);
    tb.int(STATE, true, vec![x(p.act)], vec![npc, x(p.ts) + k(1), x(p.fp), x(p.u) + x(p.fee)]);
    let mut m = vec![x(p.pc), k(cls as u64)];
    m.extend(f);
    tb.int(CODE, true, vec![x(p.act)], m);
}
fn fill_pre(row: &mut [F], p: &Pre, rp: &RProg, s: &crate::wasm::Step, cnt: &mut Counts) {
    let r = &rp.rows[s.rpc];
    row[p.act] = F::ONE;
    row[p.pc] = F::from_usize(s.rpc);
    row[p.ts] = F::from_u32(s.ts);
    row[p.u] = F::from_u32(s.u);
    row[p.fee] = F::from_u32(r.fee);
    row[p.nxt] = F::from_usize(r.next);
    cnt.code[s.rpc] += 1;
}

/// A chip: its table and a row filler.
pub struct Chip {
    pub cls: Cls,
    pub tb: TB,
    pub fill: Box<dyn Fn(&mut [F], &RProg, &crate::wasm::Step, &mut Counts)>,
}

fn alu(rr: bool) -> Chip {
    let cls = if rr { Cls::AluRR } else { Cls::AluRI };
    let mut tb = TB::new(if rr { "alu_rr" } else { "alu_ri" });
    let p = prefix(&mut tb);
    let sub = tb.c("sub");
    let aoff = tb.c("aoff");
    let boff = if rr { Some(tb.c("boff")) } else { None };
    let doff = tb.c("doff");
    let a: [usize; 4] = tb.cs("A");
    let b: [usize; 4] = tb.cs(if rr { "B" } else { "I" });
    let c: [usize; 4] = tb.cs("C");
    let pv: [usize; 4] = tb.cs("P");
    let kk: [usize; 4] = tb.cs("k");
    let za = access(&mut tb, p.act, p.ts, 0, k(0), x(p.fp) + x(aoff), lim(&a), lim(&a), "a");
    let zb = boff.map(|bo| access(&mut tb, p.act, p.ts, 1, k(0), x(p.fp) + x(bo), lim(&b), lim(&b), "b"));
    let zc = access(&mut tb, p.act, p.ts, 2, k(0), x(p.fp) + x(doff), lim(&pv), lim(&c), "c");
    for i in 0..4 {
        let cin = if i == 0 { k(0) } else { x(kk[i - 1]) };
        let add = x(a[i]) + x(b[i]) + cin.clone() - x(c[i]) - k(65536) * x(kk[i]);
        let subr = x(c[i]) + x(b[i]) + cin - x(a[i]) - k(65536) * x(kk[i]);
        tb.con((k(1) - x(sub)) * add + x(sub) * subr);
        tb.con(x(kk[i]) * (x(kk[i]) - k(1)));
        tb.int(RANGE, true, vec![x(p.act)], vec![x(c[i])]);
    }
    tb.con(x(sub) * (x(sub) - k(1)));
    let imm: [X; 4] = if rr { std::array::from_fn(|_| k(0)) } else { lim(&b) };
    let bf = boff.map(x).unwrap_or(k(0));
    let [i0, i1, i2, i3] = imm;
    control(&mut tb, &p, cls, x(p.nxt), [x(doff), x(aoff), bf, i0, i1, i2, i3, x(p.fee), x(p.nxt), k(0), x(sub)]);
    let fill = Box::new(move |row: &mut [F], rp: &RProg, s: &crate::wasm::Step, cnt: &mut Counts| {
        fill_pre(row, &p, rp, s, cnt);
        let r = &rp.rows[s.rpc];
        row[sub] = F::from_bool(r.pol);
        row[aoff] = F::from_u32(r.a);
        row[doff] = F::from_u32(r.dst);
        let av = s.acc[0].new;
        let (bv, ci) = if let Some(bo) = boff {
            row[bo] = F::from_u32(r.b);
            fill_acc(row, zb.as_ref().unwrap(), &s.acc[1], cnt);
            (s.acc[1].new, 2)
        } else {
            (limbs(r.imm), 1)
        };
        let cacc = &s.acc[ci];
        set_limbs(row, &a, &av);
        set_limbs(row, &b, &bv);
        set_limbs(row, &c, &cacc.new);
        set_limbs(row, &pv, &cacc.prev);
        fill_acc(row, &za, &s.acc[0], cnt);
        fill_acc(row, &zc, cacc, cnt);
        // carries: add: a + b = c; sub: c + b = a
        let (x0, y0) = if r.pol { (cacc.new, bv) } else { (av, bv) };
        let mut carry = 0u32;
        for i in 0..4 {
            let t = x0[i] as u32 + y0[i] as u32 + carry;
            carry = t >> 16;
            row[kk[i]] = F::from_u32(carry);
            cnt.r(cacc.new[i] as u32);
        }
    });
    Chip { cls, tb, fill }
}

fn mul() -> Chip {
    let mut tb = TB::new("mul");
    let p = prefix(&mut tb);
    let aoff = tb.c("aoff");
    let boff = tb.c("boff");
    let doff = tb.c("doff");
    let a: [usize; 8] = tb.cs("a");
    let b: [usize; 8] = tb.cs("b");
    let c: [usize; 8] = tb.cs("c");
    let pv: [usize; 4] = tb.cs("P");
    let kk: [usize; 8] = tb.cs("k");
    let l = |v: &[usize; 8]| -> [X; 4] { std::array::from_fn(|i| x(v[2 * i]) + k(256) * x(v[2 * i + 1])) };
    let za = access(&mut tb, p.act, p.ts, 0, k(0), x(p.fp) + x(aoff), l(&a), l(&a), "a");
    let zb = access(&mut tb, p.act, p.ts, 1, k(0), x(p.fp) + x(boff), l(&b), l(&b), "b");
    let zc = access(&mut tb, p.act, p.ts, 2, k(0), x(p.fp) + x(doff), lim(&pv), l(&c), "c");
    for kx in 0..8 {
        let mut terms = vec![];
        for i in 0..=kx {
            terms.push(x(a[i]) * x(b[kx - i]));
        }
        let cin = if kx == 0 { k(0) } else { x(kk[kx - 1]) };
        tb.con(sum(terms) + cin - x(c[kx]) - k(256) * x(kk[kx]));
        tb.int(RANGE, true, vec![x(p.act)], vec![x(kk[kx])]);
    }
    for v in [&a, &b, &c] {
        for i in 0..4 {
            tb.int(PAIR, true, vec![x(p.act)], vec![x(v[2 * i]), x(v[2 * i + 1])]);
        }
    }
    control(&mut tb, &p, Cls::Mul, x(p.nxt), [x(doff), x(aoff), x(boff), k(0), k(0), k(0), k(0), x(p.fee), x(p.nxt), k(0), k(0)]);
    let fill = Box::new(move |row: &mut [F], rp: &RProg, s: &crate::wasm::Step, cnt: &mut Counts| {
        fill_pre(row, &p, rp, s, cnt);
        let r = &rp.rows[s.rpc];
        row[aoff] = F::from_u32(r.a);
        row[boff] = F::from_u32(r.b);
        row[doff] = F::from_u32(r.dst);
        let by = |l: &[u16; 4]| -> [u32; 8] { std::array::from_fn(|i| ((l[i / 2] >> (8 * (i % 2))) & 255) as u32) };
        let (ab, bb, cb) = (by(&s.acc[0].new), by(&s.acc[1].new), by(&s.acc[2].new));
        for i in 0..8 {
            row[a[i]] = F::from_u32(ab[i]);
            row[b[i]] = F::from_u32(bb[i]);
            row[c[i]] = F::from_u32(cb[i]);
        }
        for i in 0..4 {
            for v in [&ab, &bb, &cb] {
                cnt.pair[(v[2 * i] | v[2 * i + 1] << 8) as usize] += 1;
            }
        }
        set_limbs(row, &pv, &s.acc[2].prev);
        fill_acc(row, &za, &s.acc[0], cnt);
        fill_acc(row, &zb, &s.acc[1], cnt);
        fill_acc(row, &zc, &s.acc[2], cnt);
        let mut carry = 0u64;
        for kx in 0..8 {
            let mut t = carry;
            for i in 0..=kx {
                t += ab[i] as u64 * bb[kx - i] as u64;
            }
            assert_eq!(t & 255, cb[kx] as u64);
            carry = t >> 8;
            row[kk[kx]] = F::from_u64(carry);
            cnt.r(carry as u32);
        }
    });
    Chip { cls: Cls::Mul, tb, fill }
}

fn brz() -> Chip {
    let mut tb = TB::new("brz");
    let p = prefix(&mut tb);
    let aoff = tb.c("aoff");
    let tgt = tb.c("tgt");
    let pol = tb.c("pol");
    let a: [usize; 4] = tb.cs("A");
    let inv = tb.c("inv");
    let z = tb.c("z");
    let taken = tb.c("taken");
    let npc = tb.c("npc");
    let za = access(&mut tb, p.act, p.ts, 0, k(0), x(p.fp) + x(aoff), lim(&a), lim(&a), "a");
    let s = sum(a.iter().map(|c| x(*c)).collect());
    tb.con(x(p.act) * (x(z) - k(1) + s.clone() * x(inv)));
    tb.con(x(z) * s);
    tb.con(x(pol) * (x(pol) - k(1)));
    tb.con(x(p.act) * (x(taken) - x(pol) * x(z) - (k(1) - x(pol)) * (k(1) - x(z))));
    tb.con(x(npc) - x(taken) * x(tgt) - (k(1) - x(taken)) * x(p.nxt));
    control(&mut tb, &p, Cls::Brz, x(npc), [k(0), x(aoff), k(0), k(0), k(0), k(0), k(0), x(p.fee), x(p.nxt), x(tgt), x(pol)]);
    let fill = Box::new(move |row: &mut [F], rp: &RProg, st: &crate::wasm::Step, cnt: &mut Counts| {
        fill_pre(row, &p, rp, st, cnt);
        let r = &rp.rows[st.rpc];
        row[aoff] = F::from_u32(r.a);
        row[tgt] = F::from_usize(r.tgt);
        row[pol] = F::from_bool(r.pol);
        let av = st.acc[0].new;
        set_limbs(row, &a, &av);
        let sm: u32 = av.iter().map(|v| *v as u32).sum();
        let zz = sm == 0;
        row[inv] = if zz { F::ZERO } else { F::from_u32(sm).inverse() };
        row[z] = F::from_bool(zz);
        row[taken] = F::from_bool(zz == r.pol);
        row[npc] = F::from_usize(st.npc);
        fill_acc(row, &za, &st.acc[0], cnt);
    });
    Chip { cls: Cls::Brz, tb, fill }
}

/// i32.load / i32.store, aligned, effective address < 64 MiB (1,024 pages).
fn ldst(store: bool) -> Chip {
    let cls = if store { Cls::St } else { Cls::Ld };
    let mut tb = TB::new(if store { "st" } else { "ld" });
    let p = prefix(&mut tb);
    let aoff = tb.c("aoff");
    let o2 = tb.c(if store { "voff" } else { "doff" });
    let off = tb.c("off");
    let a: [usize; 2] = tb.cs("A");
    let c0 = tb.c("c0");
    let l0 = tb.c("L0");
    let l1 = tb.c("L1");
    let q0 = tb.c("q0");
    let v: [usize; 2] = tb.cs("V");
    let pv: Vec<usize> = if store { tb.cs::<2>("W").to_vec() } else { tb.cs::<4>("P").to_vec() };
    tb.con(x(a[0]) + x(off) - x(l0) - k(65536) * x(c0));
    tb.con(x(a[1]) + x(c0) - x(l1));
    tb.con(x(l0) - k(4) * x(q0));
    tb.con(x(c0) * (x(c0) - k(1)));
    for e in [x(l0), x(q0), k(64) * x(l1)] {
        tb.int(RANGE, true, vec![x(p.act)], vec![e]);
    }
    let key = x(q0) + k(16384) * x(l1);
    let za = access(&mut tb, p.act, p.ts, 0, k(0), x(p.fp) + x(aoff), lim(&a), lim(&a), "a");
    let (z1, z2) = if store {
        let zv = access(&mut tb, p.act, p.ts, 1, k(0), x(p.fp) + x(o2), lim(&v), lim(&v), "v");
        let zw = access(&mut tb, p.act, p.ts, 2, k(1), key, lim(&pv), lim(&v), "w");
        (zv, zw)
    } else {
        let zw = access(&mut tb, p.act, p.ts, 1, k(1), key, lim(&v), lim(&v), "w");
        let zd = access(&mut tb, p.act, p.ts, 2, k(0), x(p.fp) + x(o2), lim(&pv), lim(&v), "d");
        (zw, zd)
    };
    let (d, b) = if store { (k(0), x(o2)) } else { (x(o2), k(0)) };
    control(&mut tb, &p, cls, x(p.nxt), [d, x(aoff), b, x(off), k(0), k(0), k(0), x(p.fee), x(p.nxt), k(0), k(0)]);
    let fill = Box::new(move |row: &mut [F], rp: &RProg, s: &crate::wasm::Step, cnt: &mut Counts| {
        fill_pre(row, &p, rp, s, cnt);
        let r = &rp.rows[s.rpc];
        assert!(r.imm < 65536);
        row[aoff] = F::from_u32(r.a);
        row[o2] = F::from_u32(if store { r.b } else { r.dst });
        row[off] = F::from_u64(r.imm);
        let av = s.acc[0].new;
        assert!(av[2] == 0 && av[3] == 0);
        set_limbs(row, &a, &av);
        let lo = av[0] as u64 + r.imm;
        let cc = lo >> 16;
        let (ll0, ll1) = (lo & 0xffff, av[1] as u64 + cc);
        assert!(ll0 % 4 == 0 && ll1 < 1024);
        row[c0] = F::from_u64(cc);
        row[l0] = F::from_u64(ll0);
        row[l1] = F::from_u64(ll1);
        row[q0] = F::from_u64(ll0 / 4);
        cnt.r(ll0 as u32);
        cnt.r((ll0 / 4) as u32);
        cnt.r((64 * ll1) as u32);
        fill_acc(row, &za, &s.acc[0], cnt);
        fill_acc(row, &z1, &s.acc[1], cnt);
        fill_acc(row, &z2, &s.acc[2], cnt);
        if store {
            set_limbs(row, &v, &s.acc[1].new);
            set_limbs(row, &pv, &s.acc[2].prev);
        } else {
            set_limbs(row, &v, &s.acc[1].new);
            set_limbs(row, &pv, &s.acc[2].prev);
        }
    });
    Chip { cls, tb, fill }
}

pub fn all_chips() -> Vec<Chip> {
    vec![alu(false), alu(true), mul(), brz(), ldst(false), ldst(true)]
}

fn bits_for(m: u32) -> usize {
    (32 - m.leading_zeros()).max(1) as usize
}
fn mult_cols(tb: &mut TB, nb: usize) -> Vec<usize> {
    (0..nb).map(|i| tb.c(&format!("m{i}"))).collect()
}
fn set_bits(row: &mut [F], cols: &[usize], m: u32) {
    for (i, c) in cols.iter().enumerate() {
        row[*c] = F::from_u32((m >> i) & 1);
    }
}

pub struct Built {
    pub air: Air,
    pub traces: Vec<RowMajorMatrix<F>>,
    /// active (non-padding) rows per table
    pub active: Vec<usize>,
    /// table kind: "chip" (per-instruction), "mem" (per touched address), "fixed" (lookup/code/io)
    pub kind: Vec<&'static str>,
}

fn pad_pow2(n: usize) -> usize {
    n.max(4).next_power_of_two()
}

pub fn build(rp: &RProg, run: &Run) -> Built {
    let mut cnt = Counts { range: vec![0; 65536], pair: vec![0; 65536], code: vec![0; rp.rows.len()] };
    let mut tables = vec![];
    let mut traces = vec![];
    let mut active = vec![];
    let mut kind = vec![];
    // chips
    let mut by: HashMap<Cls, Vec<usize>> = HashMap::new();
    for (i, s) in run.steps.iter().enumerate() {
        by.entry(rp.rows[s.rpc].cls).or_default().push(i);
    }
    for ch in all_chips() {
        let Some(ix) = by.get(&ch.cls) else { continue };
        let w = ch.tb.names.len();
        let h = pad_pow2(ix.len());
        let mut v = vec![F::ZERO; w * h];
        for (r, si) in ix.iter().enumerate() {
            (ch.fill)(&mut v[r * w..(r + 1) * w], rp, &run.steps[*si], &mut cnt);
        }
        tables.push(ch.tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(ix.len());
        kind.push("chip");
    }
    // memory boundary: one row per touched (space, addr), sorted by key
    {
        let mut tb = TB::new("mbound");
        let act = tb.c("act");
        let nact = tb.c("nact");
        let sp = tb.c("space");
        let ad = tb.c("addr");
        let iv: [usize; 4] = tb.cs("I");
        let fv: [usize; 4] = tb.cs("F");
        let tf = tb.c("tf");
        let lo = tb.c("lo");
        let hi = tb.c("hi");
        let mut m = vec![x(sp), x(ad)];
        m.extend(lim(&iv));
        m.push(k(0));
        tb.int(MEM, true, vec![x(act)], m);
        let mut m = vec![x(sp), x(ad)];
        m.extend(lim(&fv));
        m.push(x(tf));
        tb.int(MEM, false, vec![x(act)], m);
        let key = |s: X, a: X| s * k(1 << 24) + a;
        tb.con(X(E::IsTransition) * (x(nact) - nx(act)));
        tb.con(X(E::IsLast) * x(nact));
        tb.con(X(E::IsTransition) * (k(1) - x(act)) * nx(act));
        tb.con(X(E::IsTransition) * x(nact) * (key(nx(sp), nx(ad)) - key(x(sp), x(ad)) - k(1) - x(lo) - k(65536) * x(hi)));
        tb.int(RANGE, true, vec![x(act)], vec![x(lo)]);
        tb.int(RANGE, true, vec![x(act)], vec![x(hi)]);
        let mut keys: Vec<(u32, u32)> = run.mem.cur.keys().copied().collect();
        keys.sort();
        let w = tb.names.len();
        let h = pad_pow2(keys.len());
        let mut v = vec![F::ZERO; w * h];
        for (r, kk) in keys.iter().enumerate() {
            let row = &mut v[r * w..(r + 1) * w];
            let (fin, t) = run.mem.cur[kk];
            row[act] = F::ONE;
            row[nact] = F::from_bool(r + 1 < keys.len());
            row[sp] = F::from_u32(kk.0);
            row[ad] = F::from_u32(kk.1);
            set_limbs(row, &iv, &run.mem.init[kk]);
            set_limbs(row, &fv, &fin);
            row[tf] = F::from_u32(t);
            let d = if r + 1 < keys.len() {
                let kn = keys[r + 1];
                ((kn.0 << 24) | kn.1) - ((kk.0 << 24) | kk.1) - 1
            } else {
                0
            };
            row[lo] = F::from_u32(d & 0xffff);
            row[hi] = F::from_u32(d >> 16);
            cnt.r(d & 0xffff);
            cnt.r(d >> 16);
        }
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(keys.len());
        kind.push("mem");
    }
    // code table (per contract: preprocessed in the design; committed here)
    {
        let mut tb = TB::new("code");
        let f: [usize; 13] = tb.cs("f");
        let nb = bits_for(*cnt.code.iter().max().unwrap());
        let mb = mult_cols(&mut tb, nb);
        tb.int(CODE, false, mb.iter().map(|c| x(*c)).collect(), f.iter().map(|c| x(*c)).collect());
        let w = tb.names.len();
        let h = pad_pow2(rp.rows.len());
        let mut v = vec![F::ZERO; w * h];
        for (i, r) in rp.rows.iter().enumerate() {
            let row = &mut v[i * w..(i + 1) * w];
            let imm = match r.cls {
                Cls::AluRI => limbs(r.imm),
                Cls::Ld | Cls::St => [r.imm as u16, 0, 0, 0],
                _ => [0; 4],
            };
            let (dst, b) = match r.cls {
                Cls::Brz | Cls::St => (0, r.b),
                Cls::AluRI | Cls::Ld => (r.dst, 0),
                _ => (r.dst, r.b),
            };
            let a = r.a;
            let vals: [u64; 13] = [
                i as u64,
                r.cls as u64,
                dst as u64,
                a as u64,
                if r.cls == Cls::Brz { 0 } else { b as u64 },
                imm[0] as u64,
                imm[1] as u64,
                imm[2] as u64,
                imm[3] as u64,
                r.fee as u64,
                r.next as u64,
                if r.cls == Cls::Brz { r.tgt as u64 } else { 0 },
                if matches!(r.cls, Cls::AluRI | Cls::AluRR | Cls::Brz) { r.pol as u64 } else { 0 },
            ];
            for (j, c) in f.iter().enumerate() {
                row[*c] = F::from_u64(vals[j]);
            }
            set_bits(row, &mb, cnt.code[i]);
        }
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(rp.rows.len());
        kind.push("fixed");
    }
    // io: initial / final state
    {
        let mut tb = TB::new("io");
        let s = tb.c("s");
        let r = tb.c("r");
        let st: [usize; 4] = tb.cs("st");
        tb.int(STATE, true, vec![x(s)], st.iter().map(|c| x(*c)).collect());
        tb.int(STATE, false, vec![x(r)], st.iter().map(|c| x(*c)).collect());
        let w = tb.names.len();
        let mut v = vec![F::ZERO; w * 4];
        v[s] = F::ONE;
        v[st[1]] = F::ONE;
        let (pc, ts, u) = run.final_state;
        v[w + r] = F::ONE;
        v[w + st[0]] = F::from_usize(pc);
        v[w + st[1]] = F::from_u32(ts);
        v[w + st[3]] = F::from_u32(u);
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(2);
        kind.push("fixed");
    }
    // byte-pair table (only if used)
    if cnt.pair.iter().any(|c| *c > 0) {
        let mut tb = TB::new("pair");
        let b0 = tb.c("b0");
        let b1 = tb.c("b1");
        let fl = tb.c("fl");
        let inv = tb.c("inv");
        let nb = bits_for(*cnt.pair.iter().max().unwrap());
        let mb = mult_cols(&mut tb, nb);
        tb.con(X(E::IsFirst) * x(b0));
        tb.con(X(E::IsFirst) * x(b1));
        tb.con(x(fl) * (x(fl) - k(1)));
        tb.con(x(fl) * (x(b0) - k(255)));
        tb.con((x(b0) - k(255)) * x(inv) - (k(1) - x(fl)));
        tb.con(X(E::IsTransition) * (nx(b0) - (x(b0) + k(1)) * (k(1) - x(fl))));
        tb.con(X(E::IsTransition) * (nx(b1) - x(b1) - x(fl)));
        tb.int(PAIR, false, mb.iter().map(|c| x(*c)).collect(), vec![x(b0), x(b1)]);
        let w = tb.names.len();
        let mut v = vec![F::ZERO; w * 65536];
        for i in 0..65536usize {
            let row = &mut v[i * w..(i + 1) * w];
            let (x0, x1) = (i & 255, i >> 8);
            row[b0] = F::from_usize(x0);
            row[b1] = F::from_usize(x1);
            row[fl] = F::from_bool(x0 == 255);
            row[inv] = if x0 == 255 { F::ZERO } else { (F::from_usize(x0) - F::from_u32(255)).inverse() };
            set_bits(row, &mb, cnt.pair[i]);
        }
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(65536);
        kind.push("fixed");
    }
    // 16-bit range table
    {
        let mut tb = TB::new("range16");
        let vc = tb.c("v");
        let nb = bits_for(*cnt.range.iter().max().unwrap());
        let mb = mult_cols(&mut tb, nb);
        tb.con(X(E::IsFirst) * x(vc));
        tb.con(X(E::IsTransition) * (nx(vc) - x(vc) - k(1)));
        tb.int(RANGE, false, mb.iter().map(|c| x(*c)).collect(), vec![x(vc)]);
        let w = tb.names.len();
        let mut v = vec![F::ZERO; w * 65536];
        for i in 0..65536usize {
            v[i * w + vc] = F::from_usize(i);
            set_bits(&mut v[i * w..(i + 1) * w], &mb, cnt.range[i]);
        }
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(65536);
        kind.push("fixed");
    }
    let air = Air {
        tables,
        num_buses: NBUS,
        num_pub: 0,
        pub_segs: vec![],
        max_pub: 0,
        aux_group: 1,
        v2: false,
    };
    Built { air, traces, active, kind }
}
