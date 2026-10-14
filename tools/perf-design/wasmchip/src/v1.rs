//! Spike #1b / #4: the v1 layouts of V3-PERF-DESIGN §2 on the np-udr-stark-v2 prover.
//!
//! * Multi-function WASM subset with calls, unaligned i32 load/store, i64.div_u, memory.copy.
//! * Register-form translation with typed operands: `L` (local slot: RW memory, space 0),
//!   `T` (stack temporary: write-once *channel*, P-PERF-5), `Imm`, `None`.
//! * Memory argument with timestamps `8·ts + k`, ONE range lookup per access into a `RANGE-T`
//!   table (2^21 entries here; 2^24 per GPU slice in the design).
//! * Frames: `call` writes the frame record `(ret_pc, caller_fp)` at `(space 3, callee_fp)`,
//!   `return` reads it (memory argument: latest-value semantics). Arguments are produced directly
//!   into the callee's local slots; the result is a channel at `callee_fp` (zero-copy frames).
//! * Bulk copy (memory.copy, also the register→memory copy path): 16 bytes per row, word aligned.
//! * Public binding: the code table, the initial state / final state and every non-zero initial
//!   memory word are public-segment records (claim bytes) received by the tables.
use std::collections::HashMap;
use std::ops::{Add, Mul, Sub};

use npudr::air::{Air, Expr as E, Interaction, PubSeg, Table};
use npudr::field::F;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;

// =========================================================================================
// WASM subset and reference interpreter
// =========================================================================================

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum I {
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    I64Const(u64),
    I32Const(u32),
    I64Add,
    I64Sub,
    I64Mul,
    I64DivU,
    I64Eqz,
    BrIf(usize),
    Br(usize),
    I32Load(u32),
    I32Store(u32),
    Call(usize),
    /// memory.copy (dst, src, n): spike restriction: dst, src word aligned, n > 0, n % 16 == 0,
    /// non-overlapping or dst < src
    MemCopy,
    /// function end (fee 0)
    End,
}

pub struct Func {
    pub nparams: u32,
    pub nlocals: u32,
    pub nresults: u32,
    pub code: Vec<I>,
}

pub const MEMB: usize = 1 << 20;

pub struct Prog {
    pub name: String,
    pub funcs: Vec<Func>,
    pub args: Vec<u64>,
    pub mem0: Vec<u8>,
}

pub fn fee_of(i: &I) -> u64 {
    match i {
        I::End => 0,
        I::MemCopy => 32,
        _ => 1,
    }
}

pub struct Ref {
    pub gas: u64,
    pub ops: u64,
    pub locals0: Vec<u64>,
    pub mem: Vec<u8>,
}

pub fn interpret(p: &Prog) -> Ref {
    struct Fr {
        f: usize,
        pc: usize,
        loc: Vec<u64>,
        sb: usize,
    }
    let mut mem = p.mem0.clone();
    mem.resize(MEMB, 0);
    let mut st: Vec<u64> = vec![];
    let f0 = &p.funcs[0];
    let mut loc = vec![0u64; f0.nlocals as usize];
    loc[..p.args.len()].copy_from_slice(&p.args);
    let mut fr = vec![Fr { f: 0, pc: 0, loc, sb: 0 }];
    let (mut gas, mut ops) = (f0.nlocals as u64 - f0.nparams as u64, 0u64);
    let rd = |m: &Vec<u8>, a: usize| u32::from_le_bytes(m[a..a + 4].try_into().unwrap()) as u64;
    loop {
        let top = fr.len() - 1;
        let (f, pc) = (fr[top].f, fr[top].pc);
        let i = p.funcs[f].code[pc];
        fr[top].pc += 1;
        gas += fee_of(&i);
        if i != I::End {
            ops += 1;
        }
        let loc = &mut fr[top].loc;
        match i {
            I::LocalGet(x) => st.push(loc[x as usize]),
            I::LocalSet(x) => loc[x as usize] = st.pop().unwrap(),
            I::LocalTee(x) => loc[x as usize] = *st.last().unwrap(),
            I::I64Const(c) => st.push(c),
            I::I32Const(c) => st.push(c as u64),
            I::I64Add | I::I64Sub | I::I64Mul | I::I64DivU => {
                let b = st.pop().unwrap();
                let a = st.pop().unwrap();
                st.push(match i {
                    I::I64Add => a.wrapping_add(b),
                    I::I64Sub => a.wrapping_sub(b),
                    I::I64Mul => a.wrapping_mul(b),
                    _ => {
                        assert!(b != 0, "spike: no div traps");
                        a / b
                    }
                })
            }
            I::I64Eqz => {
                let a = st.pop().unwrap();
                st.push((a == 0) as u64)
            }
            I::BrIf(t) => {
                if st.pop().unwrap() != 0 {
                    fr[top].pc = t
                }
            }
            I::Br(t) => fr[top].pc = t,
            I::I32Load(o) => {
                let a = (st.pop().unwrap() as u32) as usize + o as usize;
                st.push(rd(&mem, a))
            }
            I::I32Store(o) => {
                let v = st.pop().unwrap() as u32;
                let a = (st.pop().unwrap() as u32) as usize + o as usize;
                mem[a..a + 4].copy_from_slice(&v.to_le_bytes());
            }
            I::MemCopy => {
                let n = st.pop().unwrap() as usize;
                let s = st.pop().unwrap() as usize;
                let d = st.pop().unwrap() as usize;
                assert!(n > 0 && n % 16 == 0 && s % 4 == 0 && d % 4 == 0 && (d + n <= s || s + n <= d || d < s));
                mem.copy_within(s..s + n, d);
                gas += n as u64;
            }
            I::Call(g) => {
                let fg = &p.funcs[g];
                let np = fg.nparams as usize;
                let mut l = vec![0u64; fg.nlocals as usize];
                let base = st.len() - np;
                l[..np].copy_from_slice(&st[base..]);
                st.truncate(base);
                gas += (fg.nlocals - fg.nparams) as u64;
                fr.push(Fr { f: g, pc: 0, loc: l, sb: base });
            }
            I::End => {
                let nr = p.funcs[f].nresults as usize;
                let sb = fr[top].sb;
                let res: Vec<u64> = st[st.len() - nr..].to_vec();
                st.truncate(sb);
                st.extend(res);
                let done = fr.pop().unwrap();
                if fr.is_empty() {
                    return Ref { gas, ops, locals0: done.loc, mem };
                }
            }
        }
    }
}

// =========================================================================================
// Register form
// =========================================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    N,
    L(u32),
    T(u32),
    Imm,
}
impl Op {
    pub fn kind(&self) -> u8 {
        match self {
            Op::N => 0,
            Op::L(_) => 1,
            Op::T(_) => 2,
            Op::Imm => 3,
        }
    }
    pub fn off(&self) -> u32 {
        match self {
            Op::L(o) | Op::T(o) => *o,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Cls {
    Alu,
    Mul,
    Div,
    Brz,
    Ld,
    St,
    Call,
    Ret,
    BulkStart,
    Bulk16,
}

#[derive(Clone, Debug)]
pub struct R {
    pub cls: Cls,
    pub d: Op,
    pub a: Op,
    pub b: Op,
    pub c: Op,
    pub imm: u64,
    pub sub: bool,
    pub pol: bool,
    pub next: usize,
    /// Brz: branch target; Call: callee entry
    pub tgt: usize,
    /// Call: callee frame offset
    pub fdelta: u32,
    pub fee: u32,
}
impl R {
    fn new(cls: Cls) -> R {
        R { cls, d: Op::N, a: Op::N, b: Op::N, c: Op::N, imm: 0, sub: false, pol: false, next: 0, tgt: 0, fdelta: 0, fee: 0 }
    }
    /// chip key: class + operand forms
    pub fn key(&self) -> (Cls, Op, Op, Op, Op) {
        let f = |o: Op| match o {
            Op::L(_) => Op::L(0),
            Op::T(_) => Op::T(0),
            x => x,
        };
        (self.cls, f(self.d), f(self.a), f(self.b), f(self.c))
    }
}

pub struct RProg {
    pub rows: Vec<R>,
    pub entry: Vec<usize>,
    pub halt: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum AE {
    Local(u32),
    Const(u64),
    Temp(u32),
    Eqz(Op),
}

pub fn translate(p: &Prog) -> RProg {
    let mut rows: Vec<R> = vec![];
    let mut entry = vec![0; p.funcs.len()];
    let mut call_fix: Vec<(usize, usize)> = vec![];
    for (fi, f) in p.funcs.iter().enumerate() {
        entry[fi] = rows.len();
        let nl = f.nlocals;
        let tslot = |h: u32| nl + 1 + h;
        let code = &f.code;
        let mut lead = vec![false; code.len() + 1];
        lead[0] = true;
        for (pc, i) in code.iter().enumerate() {
            if let I::BrIf(t) | I::Br(t) = i {
                lead[*t] = true;
                lead[pc + 1] = true;
            }
        }
        let mut rpc_of: Vec<Option<usize>> = vec![None; code.len() + 1];
        let mut fix_tgt = vec![];
        let mut fix_next = vec![];
        let mut st: Vec<AE> = vec![];
        let mut pend: u32 = 0;
        let mut block_start = rows.len();
        // prologue: zero the non-param locals (fee = their count)
        let mut prologue = nl - f.nparams;
        for i in f.nparams..nl {
            let mut r = R::new(Cls::Alu);
            r.d = Op::L(i);
            r.b = Op::Imm;
            r.fee = std::mem::take(&mut prologue);
            r.next = rows.len() + 1;
            rows.push(r);
        }
        pend += prologue;
        macro_rules! emit {
            ($r:expr) => {{
                let mut r: R = $r;
                r.fee = std::mem::take(&mut pend);
                r.next = rows.len() + 1;
                rows.push(r);
                rows.len() - 1
            }};
        }
        macro_rules! mat {
            ($e:expr, $h:expr) => {{
                match $e {
                    AE::Local(i) => Op::L(i),
                    AE::Temp(h) => Op::T(tslot(h)),
                    AE::Const(c) => {
                        let mut r = R::new(Cls::Alu);
                        r.d = Op::T(tslot($h));
                        r.b = Op::Imm;
                        r.imm = c;
                        emit!(r);
                        Op::T(tslot($h))
                    }
                    AE::Eqz(_) => panic!("eqz must feed br_if"),
                }
            }};
        }
        // the previous row (of this block) produced temp h: retarget its destination
        macro_rules! can_retarget {
            ($h:expr) => {
                rows.len() > block_start && rows.last().unwrap().d == Op::T(tslot($h))
            };
        }
        macro_rules! place {
            ($e:expr, $h:expr, $d:expr) => {{
                let d: Op = $d;
                match $e {
                    AE::Temp(h) if can_retarget!(h) => {
                        rows.last_mut().unwrap().d = d;
                    }
                    AE::Const(c) => {
                        let mut r = R::new(Cls::Alu);
                        r.d = d;
                        r.b = Op::Imm;
                        r.imm = c;
                        emit!(r);
                    }
                    e => {
                        let s = mat!(e, $h);
                        let mut r = R::new(Cls::Alu);
                        r.d = d;
                        r.a = s;
                        r.b = Op::Imm;
                        emit!(r);
                    }
                }
            }};
        }
        for pc in 0..code.len() {
            if lead[pc] {
                assert!(st.is_empty(), "stack must be empty at block boundaries");
                rpc_of[pc] = Some(rows.len());
                block_start = rows.len();
                let mut q = pc;
                while q < code.len() && (q == pc || !lead[q]) {
                    pend += fee_of(&code[q]) as u32;
                    q += 1;
                }
            }
            let depth = st.len() as u32;
            let ins = code[pc];
            match ins {
                I::LocalGet(i) => st.push(AE::Local(i)),
                I::I64Const(c) => st.push(AE::Const(c)),
                I::I32Const(c) => st.push(AE::Const(c as u64)),
                I::LocalSet(i) | I::LocalTee(i) => {
                    let top = st.pop().unwrap();
                    for dpos in 0..st.len() {
                        if st[dpos] == AE::Local(i) {
                            let mut r = R::new(Cls::Alu);
                            r.d = Op::T(tslot(dpos as u32));
                            r.a = Op::L(i);
                            r.b = Op::Imm;
                            emit!(r);
                            st[dpos] = AE::Temp(dpos as u32);
                        }
                    }
                    place!(top, depth - 1, Op::L(i));
                    if matches!(ins, I::LocalTee(_)) {
                        st.push(AE::Local(i));
                    }
                }
                I::I64Add | I::I64Sub | I::I64Mul | I::I64DivU => {
                    let b = st.pop().unwrap();
                    let a = st.pop().unwrap();
                    let h = depth - 2;
                    let mut r = R::new(match ins {
                        I::I64Mul => Cls::Mul,
                        I::I64DivU => Cls::Div,
                        _ => Cls::Alu,
                    });
                    r.d = Op::T(tslot(h));
                    r.sub = ins == I::I64Sub;
                    match (ins, a, b) {
                        (I::I64Add | I::I64Sub, a, AE::Const(c)) => {
                            r.a = mat!(a, h);
                            r.b = Op::Imm;
                            r.imm = c;
                        }
                        (I::I64Add, AE::Const(c), b) => {
                            r.a = mat!(b, h + 1);
                            r.b = Op::Imm;
                            r.imm = c;
                        }
                        _ => {
                            r.a = mat!(a, h);
                            r.b = mat!(b, h + 1);
                        }
                    }
                    emit!(r);
                    st.push(AE::Temp(h));
                }
                I::I64Eqz => {
                    let a = st.pop().unwrap();
                    let s = mat!(a, depth - 1);
                    st.push(AE::Eqz(s));
                }
                I::BrIf(t) => {
                    let c = st.pop().unwrap();
                    let mut r = R::new(Cls::Brz);
                    match c {
                        AE::Eqz(o) => {
                            r.a = o;
                            r.pol = true
                        }
                        e => r.a = mat!(e, depth - 1),
                    }
                    let k = emit!(r);
                    fix_tgt.push((k, t));
                }
                I::Br(t) => {
                    assert!(st.is_empty() && rows.len() > block_start, "br must follow a row of its block");
                    fix_next.push((rows.len() - 1, t));
                }
                I::I32Load(o) => {
                    let a = st.pop().unwrap();
                    let h = depth - 1;
                    let mut r = R::new(Cls::Ld);
                    r.a = mat!(a, h);
                    r.d = Op::T(tslot(h));
                    r.imm = o as u64;
                    emit!(r);
                    st.push(AE::Temp(h));
                }
                I::I32Store(o) => {
                    let v = st.pop().unwrap();
                    let a = st.pop().unwrap();
                    let h = depth - 2;
                    let mut r = R::new(Cls::St);
                    r.a = mat!(a, h);
                    match v {
                        AE::Const(c) => {
                            r.b = Op::Imm;
                            r.imm = (o as u64) | (c & 0xffff_ffff) << 32;
                        }
                        v => {
                            r.b = mat!(v, h + 1);
                            r.imm = o as u64;
                        }
                    }
                    emit!(r);
                }
                I::MemCopy => {
                    let n = st.pop().unwrap();
                    let s = st.pop().unwrap();
                    let d = st.pop().unwrap();
                    let h = depth - 3;
                    let mut r = R::new(Cls::BulkStart);
                    r.a = mat!(d, h);
                    r.b = mat!(s, h + 1);
                    r.c = mat!(n, h + 2);
                    emit!(r);
                    let mut r = R::new(Cls::Bulk16);
                    r.next = rows.len() + 1;
                    rows.push(r);
                }
                I::Call(g) => {
                    let fg = &p.funcs[g];
                    let np = fg.nparams as usize;
                    let h0 = st.len() - np;
                    let args: Vec<AE> = st.split_off(h0);
                    // top argument first (its producer may be the previous row)
                    for kx in (0..np).rev() {
                        place!(args[kx], (h0 + kx) as u32, Op::L(tslot((h0 + kx) as u32)));
                    }
                    let mut r = R::new(Cls::Call);
                    r.fdelta = tslot(h0 as u32);
                    let k = emit!(r);
                    call_fix.push((k, g));
                    if fg.nresults == 1 {
                        st.push(AE::Temp(h0 as u32));
                    }
                }
                I::End => {
                    if f.nresults == 1 {
                        let e = st.pop().unwrap();
                        place!(e, depth - 1, Op::T(0));
                    }
                    assert!(st.is_empty());
                    emit!(R::new(Cls::Ret));
                }
            }
        }
        for (r, t) in fix_tgt {
            rows[r].tgt = rpc_of[t].unwrap();
        }
        for (r, t) in fix_next {
            rows[r].next = rpc_of[t].unwrap();
        }
    }
    for (r, g) in call_fix {
        rows[r].tgt = entry[g];
    }
    let halt = rows.len();
    RProg { rows, entry, halt }
}

// =========================================================================================
// Register machine with access recording
// =========================================================================================

pub type Limbs = [u16; 4];
pub fn limbs(v: u64) -> Limbs {
    [v as u16, (v >> 16) as u16, (v >> 32) as u16, (v >> 48) as u16]
}
pub fn unl(l: &Limbs) -> u64 {
    l[0] as u64 | (l[1] as u64) << 16 | (l[2] as u64) << 32 | (l[3] as u64) << 48
}

pub const SP_LOCAL: u32 = 0;
pub const SP_MEM: u32 = 1;
pub const SP_FRAME: u32 = 3;
pub const TS_MUL: u32 = 8;

/// One access: RW memory (`ch == false`) or channel (`ch == true`: producer has `prev_t == u32::MAX`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Acc {
    pub space: u32,
    pub addr: u32,
    pub prev: Limbs,
    pub new: Limbs,
    pub t_prev: u32,
    pub t: u32,
}

pub struct Step {
    pub rpc: usize,
    pub ts: u32,
    pub fp: u32,
    pub u: u32,
    pub regs: [u32; 3],
    pub npc: usize,
    pub nfp: u32,
    pub nu: u32,
    pub nregs: [u32; 3],
    /// accesses keyed by port name
    pub acc: HashMap<&'static str, Acc>,
}

pub struct Run {
    pub steps: Vec<Step>,
    pub mem: HashMap<(u32, u32), (Limbs, u32)>,
    pub init: HashMap<(u32, u32), Limbs>,
    pub final_state: (usize, u32, u32, u32),
}

struct M<'a> {
    cur: HashMap<(u32, u32), (Limbs, u32)>,
    init: HashMap<(u32, u32), Limbs>,
    src: &'a HashMap<(u32, u32), Limbs>,
    ch: HashMap<u32, (Limbs, u32)>,
}
impl M<'_> {
    fn rw(&mut self, space: u32, addr: u32, newv: Option<Limbs>, t: u32) -> Acc {
        let (prev, t_prev) = match self.cur.get(&(space, addr)) {
            Some(v) => *v,
            None => {
                let v = *self.src.get(&(space, addr)).unwrap_or(&[0; 4]);
                self.init.insert((space, addr), v);
                (v, 0)
            }
        };
        let new = newv.unwrap_or(prev);
        self.cur.insert((space, addr), (new, t));
        Acc { space, addr, prev, new, t_prev, t }
    }
    fn produce(&mut self, slot: u32, v: Limbs, t: u32) -> Acc {
        assert!(self.ch.insert(slot, (v, t)).is_none(), "channel discipline: slot {slot} produced twice");
        Acc { space: 2, addr: slot, prev: [0; 4], new: v, t_prev: u32::MAX, t }
    }
    fn consume(&mut self, slot: u32, t: u32) -> Acc {
        let (v, tp) = self.ch.remove(&slot).expect("channel discipline: consume before produce");
        Acc { space: 2, addr: slot, prev: v, new: v, t_prev: tp, t }
    }
    fn read(&mut self, o: Op, fp: u32, t: u32) -> Acc {
        match o {
            Op::L(x) => self.rw(SP_LOCAL, fp + x, None, t),
            Op::T(x) => self.consume(fp + x, t),
            _ => unreachable!(),
        }
    }
    fn write(&mut self, o: Op, fp: u32, v: Limbs, t: u32) -> Acc {
        match o {
            Op::L(x) => self.rw(SP_LOCAL, fp + x, Some(v), t),
            Op::T(x) => self.produce(fp + x, v, t),
            _ => unreachable!(),
        }
    }
}

pub fn initial_words(p: &Prog) -> HashMap<(u32, u32), Limbs> {
    let mut src = HashMap::new();
    for (i, v) in p.args.iter().enumerate() {
        if *v != 0 {
            src.insert((SP_LOCAL, i as u32), limbs(*v));
        }
    }
    for w in 0..p.mem0.len() / 4 {
        let v = u32::from_le_bytes(p.mem0[4 * w..4 * w + 4].try_into().unwrap());
        if v != 0 {
            src.insert((SP_MEM, w as u32), limbs(v as u64));
        }
    }
    src
}

pub fn execute(rp: &RProg, p: &Prog) -> Run {
    let mut src = initial_words(p);
    src.insert((SP_FRAME, 0), [rp.halt as u16, 0, 0, 0]);
    let mut m = M { cur: HashMap::new(), init: HashMap::new(), src: &src, ch: HashMap::new() };
    let mut steps = vec![];
    let (mut pc, mut ts, mut fp, mut u, mut regs) = (rp.entry[0], 1u32, 0u32, 0u32, [0u32; 3]);
    let wv = |w: u32| -> Limbs { [w as u16, (w >> 16) as u16, 0, 0] };
    while pc != rp.halt {
        let r = &rp.rows[pc];
        let t = |k: u32| TS_MUL * ts + k;
        let mut acc: HashMap<&'static str, Acc> = HashMap::new();
        let (mut npc, mut nfp, mut nu, mut nregs) = (r.next, fp, u + r.fee, [0u32; 3]);
        match r.cls {
            Cls::Alu | Cls::Mul | Cls::Div => {
                let av = if r.a == Op::N {
                    0
                } else {
                    let x = m.read(r.a, fp, t(0));
                    acc.insert("a", x);
                    unl(&x.new)
                };
                let bv = if r.b == Op::Imm {
                    r.imm
                } else {
                    let x = m.read(r.b, fp, t(1));
                    acc.insert("b", x);
                    unl(&x.new)
                };
                let c = match r.cls {
                    Cls::Mul => av.wrapping_mul(bv),
                    Cls::Div => av / bv,
                    _ if r.sub => av.wrapping_sub(bv),
                    _ => av.wrapping_add(bv),
                };
                acc.insert("d", m.write(r.d, fp, limbs(c), t(3)));
            }
            Cls::Brz => {
                let x = m.read(r.a, fp, t(0));
                acc.insert("a", x);
                if (unl(&x.new) == 0) == r.pol {
                    npc = r.tgt
                }
            }
            Cls::Ld => {
                let x = m.read(r.a, fp, t(0));
                acc.insert("a", x);
                let ea = (unl(&x.new) as u32) as u64 + (r.imm & 0xffff_ffff);
                let (q, o) = ((ea / 4) as u32, (ea % 4) as usize);
                let w1 = m.rw(SP_MEM, q, None, t(1));
                let w2 = m.rw(SP_MEM, q + 1, None, t(2));
                let bytes = [w1.new[0].to_le_bytes(), w1.new[1].to_le_bytes(), w2.new[0].to_le_bytes(), w2.new[1].to_le_bytes()].concat();
                let v = u32::from_le_bytes(bytes[o..o + 4].try_into().unwrap());
                acc.insert("w1", w1);
                acc.insert("w2", w2);
                acc.insert("d", m.write(r.d, fp, limbs(v as u64), t(3)));
            }
            Cls::St => {
                let x = m.read(r.a, fp, t(0));
                acc.insert("a", x);
                let v = if r.b == Op::Imm {
                    (r.imm >> 32) as u32
                } else {
                    let y = m.read(r.b, fp, t(1));
                    acc.insert("b", y);
                    unl(&y.new) as u32
                };
                let ea = (unl(&x.new) as u32) as u64 + (r.imm & 0xffff_ffff);
                let (q, o) = ((ea / 4) as u32, (ea % 4) as usize);
                let get = |m: &mut M, q| m.cur.get(&(SP_MEM, q)).map(|x| x.0).unwrap_or(*m.src.get(&(SP_MEM, q)).unwrap_or(&[0; 4]));
                let (p1, p2) = (get(&mut m, q), get(&mut m, q + 1));
                let mut bytes = [p1[0].to_le_bytes(), p1[1].to_le_bytes(), p2[0].to_le_bytes(), p2[1].to_le_bytes()].concat();
                bytes[o..o + 4].copy_from_slice(&v.to_le_bytes());
                let n1 = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
                let n2 = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
                acc.insert("w1", m.rw(SP_MEM, q, Some(wv(n1)), t(2)));
                acc.insert("w2", m.rw(SP_MEM, q + 1, Some(wv(n2)), t(3)));
            }
            Cls::Call => {
                let nf = fp + r.fdelta;
                acc.insert("fr", m.rw(SP_FRAME, nf, Some([r.next as u16, fp as u16, 0, 0]), t(0)));
                npc = r.tgt;
                nfp = nf;
            }
            Cls::Ret => {
                let x = m.rw(SP_FRAME, fp, None, t(0));
                npc = x.new[0] as usize;
                nfp = x.new[1] as u32;
                acc.insert("fr", x);
            }
            Cls::BulkStart => {
                let d = m.read(r.a, fp, t(0));
                let s = m.read(r.b, fp, t(1));
                let n = m.read(r.c, fp, t(2));
                nregs = [(unl(&d.new) / 4) as u32, (unl(&s.new) / 4) as u32, unl(&n.new) as u32];
                acc.insert("a", d);
                acc.insert("b", s);
                acc.insert("c", n);
            }
            Cls::Bulk16 => {
                let [qd, qs, n] = regs;
                for k in 0..4u32 {
                    let x = m.rw(SP_MEM, qs + k, None, t(k));
                    acc.insert(["s0", "s1", "s2", "s3"][k as usize], x);
                    acc.insert(["d0", "d1", "d2", "d3"][k as usize], m.rw(SP_MEM, qd + k, Some(x.new), t(4 + k)));
                }
                nu = u + 16;
                if n > 16 {
                    npc = pc;
                    nregs = [qd + 4, qs + 4, n - 16];
                }
            }
        }
        steps.push(Step { rpc: pc, ts, fp, u, regs, npc, nfp, nu, nregs, acc });
        pc = npc;
        fp = nfp;
        u = nu;
        regs = nregs;
        ts += 1;
    }
    assert!(m.ch.is_empty(), "channel discipline: {} unconsumed temporaries", m.ch.len());
    Run { steps, mem: m.cur, init: m.init, final_state: (pc, ts, fp, u) }
}

// =========================================================================================
// Chips
// =========================================================================================

pub const STATE: usize = 0;
pub const FETCH: usize = 1;
pub const MEM: usize = 2;
pub const RANGE: usize = 3;
pub const PAIR: usize = 4;
pub const RANGET: usize = 5;
pub const PUBC: usize = 6;
pub const PUBM: usize = 7;
pub const PUBIO: usize = 8;
pub const MINIT: usize = 9;
pub const NBUS: usize = 10;
pub const LOG_RT: usize = 21;

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

pub struct TB {
    pub name: String,
    pub names: Vec<String>,
    pub cons: Vec<E>,
    pub ints: Vec<Interaction>,
}
impl TB {
    pub fn new(n: &str) -> TB {
        TB { name: n.into(), names: vec![], cons: vec![], ints: vec![] }
    }
    pub fn c(&mut self, n: &str) -> usize {
        self.names.push(n.into());
        self.names.len() - 1
    }
    pub fn cs<const N: usize>(&mut self, n: &str) -> [usize; N] {
        std::array::from_fn(|i| self.c(&format!("{n}{i}")))
    }
    pub fn con(&mut self, e: X) {
        self.cons.push(e.0)
    }
    pub fn int(&mut self, bus: usize, send: bool, mult: Vec<X>, msg: Vec<X>) {
        self.ints.push(Interaction { bus, mult: mult.into_iter().map(|m| m.0).collect(), msg: msg.into_iter().map(|m| m.0).collect(), send })
    }
    pub fn table(self) -> Table {
        let mut t = Table { name: self.name, width: self.names.len(), constraints: self.cons, interactions: self.ints, max_log: 22 };
        let b = npudr::aux::bit_constraints(&t);
        t.constraints.extend(b);
        t
    }
}

#[derive(Default)]
pub struct Counts {
    pub range: Vec<u32>,
    pub pair: Vec<u32>,
    pub rt: Vec<u32>,
    pub code: Vec<u32>,
}
impl Counts {
    fn r(&mut self, v: u64) {
        assert!(v < 65536, "range16 out of range: {v}");
        self.range[v as usize] += 1
    }
    fn t(&mut self, v: u64) {
        assert!(v < (1 << LOG_RT), "timestamp gap out of range: {v}");
        self.rt[v as usize] += 1
    }
    fn p(&mut self, a: u32, b: u32) {
        assert!(a < 256 && b < 256);
        self.pair[(a | b << 8) as usize] += 1
    }
}

/// A port = one memory/channel access of a chip row; columns it owns and its fill.
#[derive(Clone, Copy)]
pub enum PortKind {
    /// RW memory read: value columns given by the caller (prev = new)
    Read,
    /// RW memory write: owns 4 prev-value columns (or `nprev`)
    Write,
    /// channel consume
    Consume,
    /// channel produce
    Produce,
}
#[derive(Clone)]
pub struct Port {
    pub name: &'static str,
    pub kind: PortKind,
    pub tcol: Option<usize>,
    pub prev: Vec<usize>,
}

pub type Ts = X;

/// Adds a port's interactions. `space`/`addr` are expressions; `val` the (new) value limbs.
fn port(tb: &mut TB, act: X, name: &'static str, kind: PortKind, ts: Ts, sub: u64, space: X, addr: X, val: [X; 4], nprev: usize) -> Port {
    let tnow = k(TS_MUL as u64) * ts + k(sub);
    match kind {
        PortKind::Read | PortKind::Write => {
            let tc = tb.c(&format!("{name}_t"));
            let prev: Vec<usize> = if matches!(kind, PortKind::Write) { (0..nprev).map(|i| tb.c(&format!("{name}_p{i}"))).collect() } else { vec![] };
            let pv: [X; 4] = if matches!(kind, PortKind::Write) { std::array::from_fn(|i| if i < nprev { x(prev[i]) } else { k(0) }) } else { val.clone() };
            let mut m1 = vec![space.clone(), addr.clone()];
            m1.extend(pv);
            m1.push(x(tc));
            tb.int(MEM, false, vec![act.clone()], m1);
            let mut m2 = vec![space, addr];
            m2.extend(val);
            m2.push(tnow.clone());
            tb.int(MEM, true, vec![act.clone()], m2);
            tb.int(RANGET, true, vec![act.clone()], vec![tnow - x(tc) - k(1)]);
            Port { name, kind, tcol: Some(tc), prev }
        }
        PortKind::Consume => {
            let tc = tb.c(&format!("{name}_t"));
            let mut m1 = vec![k(2), addr];
            m1.extend(val);
            m1.push(x(tc));
            tb.int(MEM, false, vec![act.clone()], m1);
            tb.int(RANGET, true, vec![act], vec![tnow - x(tc) - k(1)]);
            Port { name, kind, tcol: Some(tc), prev: vec![] }
        }
        PortKind::Produce => {
            let mut m2 = vec![k(2), addr];
            m2.extend(val);
            m2.push(tnow);
            tb.int(MEM, true, vec![act], m2);
            Port { name, kind, tcol: None, prev: vec![] }
        }
    }
}

fn fill_port(row: &mut [F], p: &Port, a: &Acc, cnt: &mut Counts) {
    if let Some(tc) = p.tcol {
        row[tc] = F::from_u32(a.t_prev);
        cnt.t((a.t - a.t_prev - 1) as u64);
    }
    for (i, c) in p.prev.iter().enumerate() {
        row[*c] = F::from_u32(a.prev[i] as u32);
    }
}

/// Port for an operand slot by its kind.
fn operand(tb: &mut TB, act: X, name: &'static str, o: Op, write: bool, ts: Ts, sub: u64, fp: X, off: X, val: [X; 4]) -> Option<Port> {
    let addr = fp + off;
    match (o, write) {
        (Op::L(_), false) => Some(port(tb, act, name, PortKind::Read, ts, sub, k(SP_LOCAL as u64), addr, val, 0)),
        (Op::L(_), true) => Some(port(tb, act, name, PortKind::Write, ts, sub, k(SP_LOCAL as u64), addr, val, 4)),
        (Op::T(_), false) => Some(port(tb, act, name, PortKind::Consume, ts, sub, k(2), addr, val, 0)),
        (Op::T(_), true) => Some(port(tb, act, name, PortKind::Produce, ts, sub, k(2), addr, val, 0)),
        _ => None,
    }
}

/// common prefix
#[derive(Clone, Copy)]
struct Pre {
    act: usize,
    pc: usize,
    ts: usize,
    fp: usize,
    u: usize,
    fee: usize,
    nxt: usize,
    doff: usize,
    aoff: usize,
    boff: usize,
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
        doff: tb.c("doff"),
        aoff: tb.c("aoff"),
        boff: tb.c("boff"),
    }
}

/// FETCH message: (pc, key-id, doff, aoff, boff, coff, imm0..imm3, sub/pol, fee, next, tgt, fdelta)
pub const FETCH_W: usize = 15;
fn fetch_msg(p: &Pre, kid: u64, coff: X, imm: [X; 4], pol: X, tgt: X, fd: X) -> Vec<X> {
    let [i0, i1, i2, i3] = imm;
    vec![x(p.pc), k(kid), x(p.doff), x(p.aoff), x(p.boff), coff, i0, i1, i2, i3, pol, x(p.fee), x(p.nxt), tgt, fd]
}
fn state(tb: &mut TB, p: &Pre, npc: X, nfp: X, nu: X, regs: [X; 3], nregs: [X; 3]) {
    let mut m = vec![x(p.pc), x(p.ts), x(p.fp), x(p.u)];
    m.extend(regs);
    tb.int(STATE, false, vec![x(p.act)], m);
    let mut m = vec![npc, x(p.ts) + k(1), nfp, nu];
    m.extend(nregs);
    tb.int(STATE, true, vec![x(p.act)], m);
}
fn fill_pre(row: &mut [F], p: &Pre, r: &R, s: &Step, cnt: &mut Counts) {
    row[p.act] = F::ONE;
    row[p.pc] = F::from_usize(s.rpc);
    row[p.ts] = F::from_u32(s.ts);
    row[p.fp] = F::from_u32(s.fp);
    row[p.u] = F::from_u32(s.u);
    row[p.fee] = F::from_u32(r.fee);
    row[p.nxt] = F::from_usize(r.next);
    row[p.doff] = F::from_u32(r.d.off());
    row[p.aoff] = F::from_u32(r.a.off());
    row[p.boff] = F::from_u32(if r.cls == Cls::Call { r.fdelta } else { r.b.off() });
    cnt.code[s.rpc] += 1;
}
fn z3() -> [X; 3] {
    [k(0), k(0), k(0)]
}
fn set(row: &mut [F], c: usize, v: u64) {
    row[c] = F::from_u64(v);
}

pub type Fill = Box<dyn Fn(&mut [F], &R, &Step, &mut Counts)>;
pub struct Chip {
    pub tb: TB,
    pub fill: Fill,
}

/// key id for FETCH: unique per (cls, forms)
pub fn kid(r: &R) -> u64 {
    let (c, d, a, b, cc) = r.key();
    (c as u64) * 1000 + d.kind() as u64 * 64 + a.kind() as u64 * 16 + b.kind() as u64 * 4 + cc.kind() as u64
}

fn name_of(r: &R) -> String {
    let f = |o: Op| match o {
        Op::N => "_",
        Op::L(_) => "L",
        Op::T(_) => "T",
        Op::Imm => "I",
    };
    let c = match r.cls {
        Cls::Alu => if r.b == Op::Imm { "alu_ri" } else { "alu_rr" },
        Cls::Mul => "mul",
        Cls::Div => "divu",
        Cls::Brz => "brz",
        Cls::Ld => "ld_gen",
        Cls::St => "st_gen",
        Cls::Call => "call",
        Cls::Ret => "ret",
        Cls::BulkStart => "bulk_start",
        Cls::Bulk16 => "bulk16",
    };
    format!("{c}[{}{}{}{}]", f(r.d), f(r.a), f(r.b), f(r.c))
}

/// value limbs from 16-bit columns (n limbs, zero above)
fn lv(cols: &[usize]) -> [X; 4] {
    std::array::from_fn(|i| if i < cols.len() { x(cols[i]) } else { k(0) })
}
fn lb(bytes: &[usize]) -> [X; 4] {
    std::array::from_fn(|i| if 2 * i + 1 < bytes.len() { x(bytes[2 * i]) + k(256) * x(bytes[2 * i + 1]) } else { k(0) })
}
fn bytes_of(l: &Limbs, n: usize) -> Vec<u64> {
    (0..n).map(|i| ((l[i / 2] >> (8 * (i % 2))) & 255) as u64).collect()
}

pub fn chip_for(r: &R) -> Chip {
    let mut tb = TB::new(&name_of(r));
    let p = prefix(&mut tb);
    let ts = x(p.ts);
    let act = x(p.act);
    let fp = x(p.fp);
    let id = kid(r);
    let (d_op, a_op, b_op, c_op) = (r.d, r.a, r.b, r.c);
    match r.cls {
        Cls::Alu => {
            let sub = tb.c("sub");
            let a: [usize; 4] = tb.cs("A");
            let b: [usize; 4] = tb.cs(if b_op == Op::Imm { "I" } else { "B" });
            let c: [usize; 4] = tb.cs("C");
            let kk: [usize; 4] = tb.cs("k");
            let pa = operand(&mut tb, act.clone(), "a", a_op, false, ts.clone(), 0, fp.clone(), x(p.aoff), lv(&a));
            if a_op == Op::N {
                for i in 0..4 {
                    tb.con(x(a[i]));
                }
            }
            let pb = operand(&mut tb, act.clone(), "b", b_op, false, ts.clone(), 1, fp.clone(), x(p.boff), lv(&b));
            let pd = operand(&mut tb, act.clone(), "d", d_op, true, ts.clone(), 3, fp.clone(), x(p.doff), lv(&c));
            for i in 0..4 {
                let cin = if i == 0 { k(0) } else { x(kk[i - 1]) };
                let add = x(a[i]) + x(b[i]) + cin.clone() - x(c[i]) - k(65536) * x(kk[i]);
                let subr = x(c[i]) + x(b[i]) + cin - x(a[i]) - k(65536) * x(kk[i]);
                tb.con((k(1) - x(sub)) * add + x(sub) * subr);
                tb.con(x(kk[i]) * (x(kk[i]) - k(1)));
                tb.int(RANGE, true, vec![act.clone()], vec![x(c[i])]);
            }
            tb.con(x(sub) * (x(sub) - k(1)));
            let imm = if b_op == Op::Imm { lv(&b) } else { [k(0), k(0), k(0), k(0)] };
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), imm, x(sub), k(0), k(0)));
            state(&mut tb, &p, x(p.nxt), fp, x(p.u) + x(p.fee), z3(), z3());
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                set(row, sub, r.sub as u64);
                let av = s.acc.get("a").map(|x| x.new).unwrap_or([0; 4]);
                let bv = s.acc.get("b").map(|x| x.new).unwrap_or(limbs(r.imm));
                let cv = s.acc["d"].new;
                for i in 0..4 {
                    set(row, a[i], av[i] as u64);
                    set(row, b[i], bv[i] as u64);
                    set(row, c[i], cv[i] as u64);
                    cnt.r(cv[i] as u64);
                }
                let (x0, y0) = if r.sub { (cv, bv) } else { (av, bv) };
                let mut carry = 0u64;
                for i in 0..4 {
                    let t = x0[i] as u64 + y0[i] as u64 + carry;
                    carry = t >> 16;
                    set(row, kk[i], carry);
                }
                for (pp, n) in [(&pa, "a"), (&pb, "b"), (&pd, "d")] {
                    if let Some(pp) = pp {
                        fill_port(row, pp, &s.acc[n], cnt);
                    }
                }
            });
            Chip { tb, fill }
        }
        Cls::Mul | Cls::Div => {
            let div = r.cls == Cls::Div;
            let a: [usize; 8] = tb.cs("a");
            let b: [usize; 8] = tb.cs("b");
            let c: [usize; 8] = tb.cs(if div { "q" } else { "c" });
            let rr: Vec<usize> = if div { tb.cs::<8>("r").to_vec() } else { vec![] };
            let kk: [usize; 8] = tb.cs("k");
            let dd: Vec<usize> = if div { tb.cs::<4>("dd").to_vec() } else { vec![] };
            let bo: Vec<usize> = if div { tb.cs::<4>("bo").to_vec() } else { vec![] };
            let pa = operand(&mut tb, act.clone(), "a", a_op, false, ts.clone(), 0, fp.clone(), x(p.aoff), lb(&a));
            let pb = operand(&mut tb, act.clone(), "b", b_op, false, ts.clone(), 1, fp.clone(), x(p.boff), lb(&b));
            let pd = operand(&mut tb, act.clone(), "d", d_op, true, ts.clone(), 3, fp.clone(), x(p.doff), lb(&c));
            // mul: a*b = c (mod 2^64): conv_k(a,b) + cin = c_k + 256 k_k
            // div: q*b + r = a: conv_k(q,b) + r_k + cin = a_k + 256 k_k, k_7 = 0, conv_k = 0 for k >= 8
            let (x1, x2, out) = if div { (c, b, a) } else { (a, b, c) };
            for kx in 0..8 {
                let mut t = vec![];
                for i in 0..=kx {
                    t.push(x(x1[i]) * x(x2[kx - i]));
                }
                if div {
                    t.push(x(rr[kx]));
                }
                let cin = if kx == 0 { k(0) } else { x(kk[kx - 1]) };
                tb.con(sum(t) + cin - x(out[kx]) - k(256) * x(kk[kx]));
                tb.int(RANGE, true, vec![act.clone()], vec![x(kk[kx])]);
            }
            if div {
                tb.con(x(kk[7]));
                for kx in 8..15 {
                    let mut t = vec![];
                    for i in (kx - 7)..8 {
                        t.push(x(x1[i]) * x(x2[kx - i]));
                    }
                    tb.con(sum(t));
                }
                // r < b: B - R - 1 = DD (16-bit limbs, borrows bo)
                for l in 0..4 {
                    let bl = x(b[2 * l]) + k(256) * x(b[2 * l + 1]);
                    let rl = x(rr[2 * l]) + k(256) * x(rr[2 * l + 1]);
                    let bin = if l == 0 { k(1) } else { x(bo[l - 1]) };
                    tb.con(bl - rl - bin - x(dd[l]) + k(65536) * x(bo[l]));
                    tb.con(x(bo[l]) * (x(bo[l]) - k(1)));
                    tb.int(RANGE, true, vec![act.clone()], vec![x(dd[l])]);
                }
                tb.con(x(bo[3]));
            }
            let groups: Vec<&[usize]> = if div { vec![&a, &b, &c, &rr] } else { vec![&a, &b, &c] };
            for v in &groups {
                for i in 0..4 {
                    tb.int(PAIR, true, vec![act.clone()], vec![x(v[2 * i]), x(v[2 * i + 1])]);
                }
            }
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), [k(0), k(0), k(0), k(0)], k(0), k(0), k(0)));
            state(&mut tb, &p, x(p.nxt), fp, x(p.u) + x(p.fee), z3(), z3());
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                let av = bytes_of(&s.acc["a"].new, 8);
                let bv = bytes_of(&s.acc["b"].new, 8);
                let cv = bytes_of(&s.acc["d"].new, 8);
                let rv: Vec<u64> = if div { bytes_of(&limbs(unl(&s.acc["a"].new) % unl(&s.acc["b"].new)), 8) } else { vec![] };
                for i in 0..8 {
                    set(row, a[i], av[i]);
                    set(row, b[i], bv[i]);
                    set(row, c[i], cv[i]);
                    if div {
                        set(row, rr[i], rv[i]);
                    }
                }
                let groups: Vec<&Vec<u64>> = if div { vec![&av, &bv, &cv, &rv] } else { vec![&av, &bv, &cv] };
                for v in groups {
                    for i in 0..4 {
                        cnt.p(v[2 * i] as u32, v[2 * i + 1] as u32);
                    }
                }
                let (y1, y2, yo) = if div { (&cv, &bv, &av) } else { (&av, &bv, &cv) };
                let mut carry = 0u64;
                for kx in 0..8 {
                    let mut t = carry;
                    for i in 0..=kx {
                        t += y1[i] * y2[kx - i];
                    }
                    if div {
                        t += rv[kx];
                    }
                    assert_eq!(t & 255, yo[kx]);
                    carry = t >> 8;
                    set(row, kk[kx], carry);
                    cnt.r(carry);
                }
                if div {
                    let (bb, r0) = (unl(&s.acc["b"].new), unl(&limbs(unl(&s.acc["a"].new) % unl(&s.acc["b"].new))));
                    let dv = limbs(bb - r0 - 1);
                    let mut borrow = 1i64;
                    for l in 0..4 {
                        let bl = (bb >> (16 * l)) & 0xffff;
                        let rl = (r0 >> (16 * l)) & 0xffff;
                        let t = bl as i64 - rl as i64 - borrow;
                        let bout = (t < 0) as i64;
                        set(row, dd[l], dv[l] as u64);
                        set(row, bo[l], bout as u64);
                        cnt.r(dv[l] as u64);
                        borrow = bout;
                    }
                }
                for (pp, n) in [(&pa, "a"), (&pb, "b"), (&pd, "d")] {
                    if let Some(pp) = pp {
                        fill_port(row, pp, &s.acc[n], cnt);
                    }
                }
            });
            Chip { tb, fill }
        }
        Cls::Brz => {
            let pol = tb.c("pol");
            let tgt = tb.c("tgt");
            let a: [usize; 4] = tb.cs("A");
            let inv = tb.c("inv");
            let z = tb.c("z");
            let taken = tb.c("taken");
            let npc = tb.c("npc");
            let pa = operand(&mut tb, act.clone(), "a", a_op, false, ts.clone(), 0, fp.clone(), x(p.aoff), lv(&a));
            let s = sum(a.iter().map(|c| x(*c)).collect());
            tb.con(act.clone() * (x(z) - k(1) + s.clone() * x(inv)));
            tb.con(x(z) * s);
            tb.con(x(pol) * (x(pol) - k(1)));
            tb.con(act.clone() * (x(taken) - x(pol) * x(z) - (k(1) - x(pol)) * (k(1) - x(z))));
            tb.con(x(npc) - x(taken) * x(tgt) - (k(1) - x(taken)) * x(p.nxt));
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), [k(0), k(0), k(0), k(0)], x(pol), x(tgt), k(0)));
            state(&mut tb, &p, x(npc), fp, x(p.u) + x(p.fee), z3(), z3());
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                set(row, pol, r.pol as u64);
                set(row, tgt, r.tgt as u64);
                let av = s.acc["a"].new;
                for i in 0..4 {
                    set(row, a[i], av[i] as u64);
                }
                let sm: u64 = av.iter().map(|v| *v as u64).sum();
                row[inv] = if sm == 0 { F::ZERO } else { F::from_u64(sm).inverse() };
                set(row, z, (sm == 0) as u64);
                set(row, taken, ((sm == 0) == r.pol) as u64);
                set(row, npc, s.npc as u64);
                fill_port(row, pa.as_ref().unwrap(), &s.acc["a"], cnt);
            });
            Chip { tb, fill }
        }
        Cls::Ld | Cls::St => {
            let store = r.cls == Cls::St;
            let off = tb.c("off");
            let a: [usize; 2] = tb.cs("A");
            let c0 = tb.c("c0");
            let l0 = tb.c("L0");
            let l1 = tb.c("L1");
            let q0 = tb.c("q0");
            let sel: [usize; 4] = tb.cs("s");
            let w: [usize; 8] = tb.cs("w"); // bytes of words q, q+1 (loads: value; stores: previous)
            let vb: Vec<usize> = if store { tb.cs::<4>("v").to_vec() } else { vec![] };
            let vimm: Vec<usize> = if store && b_op == Op::Imm { tb.cs::<2>("vi").to_vec() } else { vec![] };
            tb.con(x(a[0]) + x(off) - x(l0) - k(65536) * x(c0));
            tb.con(x(a[1]) + x(c0) - x(l1));
            tb.con(x(c0) * (x(c0) - k(1)));
            let o = x(sel[1]) + k(2) * x(sel[2]) + k(3) * x(sel[3]);
            tb.con(x(l0) - k(4) * x(q0) - o);
            tb.con(act.clone() * (sum(sel.iter().map(|c| x(*c)).collect()) - k(1)));
            for s in sel {
                tb.con(x(s) * (x(s) - k(1)));
            }
            for e in [x(l0), x(q0), k(4096) * x(l1)] {
                tb.int(RANGE, true, vec![act.clone()], vec![e]);
            }
            let q = x(q0) + k(16384) * x(l1);
            // selected value bytes: r_j = Σ_o s_o w[o+j]
            let selb = |j: usize| -> X { sum((0..4).map(|o| x(sel[o]) * x(w[o + j])).collect()) };
            let pa = operand(&mut tb, act.clone(), "a", a_op, false, ts.clone(), 0, fp.clone(), x(p.aoff), lv(&a));
            let wv = |bs: [X; 4]| -> [X; 4] {
                let [b0, b1, b2, b3] = bs;
                [b0 + k(256) * b1, b2 + k(256) * b3, k(0), k(0)]
            };
            let (pb, pw1, pw2, pd);
            if store {
                let val: [X; 4] = if b_op == Op::Imm { lv(&vimm) } else { lb(&vb) };
                if b_op == Op::Imm {
                    // immediate value: bytes vb must equal the fetched immediate limbs
                    tb.con(x(vimm[0]) - x(vb[0]) - k(256) * x(vb[1]));
                    tb.con(x(vimm[1]) - x(vb[2]) - k(256) * x(vb[3]));
                }
                pb = operand(&mut tb, act.clone(), "b", b_op, false, ts.clone(), 1, fp.clone(), x(p.boff), val);
                // new byte m of the 8-byte window
                let nb = |m: usize| -> X {
                    let mut t = vec![];
                    for o in 0..4 {
                        if m >= o && m - o < 4 {
                            t.push(x(sel[o]) * x(vb[m - o]));
                        } else {
                            t.push(x(sel[o]) * x(w[m]));
                        }
                    }
                    sum(t)
                };
                let n1 = wv([nb(0), nb(1), nb(2), nb(3)]);
                let n2 = wv([nb(4), nb(5), nb(6), nb(7)]);
                let p1 = wv([x(w[0]), x(w[1]), x(w[2]), x(w[3])]);
                let p2 = wv([x(w[4]), x(w[5]), x(w[6]), x(w[7])]);
                // RW writes whose previous value is given by the w bytes
                let mut mk = |nm: &'static str, sub: u64, addr: X, prev: [X; 4], newv: [X; 4]| -> Port {
                    let tc = tb.c(&format!("{nm}_t"));
                    let tnow = k(TS_MUL as u64) * ts.clone() + k(sub);
                    let mut m1 = vec![k(SP_MEM as u64), addr.clone()];
                    m1.extend(prev);
                    m1.push(x(tc));
                    tb.int(MEM, false, vec![act.clone()], m1);
                    let mut m2 = vec![k(SP_MEM as u64), addr];
                    m2.extend(newv);
                    m2.push(tnow.clone());
                    tb.int(MEM, true, vec![act.clone()], m2);
                    tb.int(RANGET, true, vec![act.clone()], vec![tnow - x(tc) - k(1)]);
                    Port { name: nm, kind: PortKind::Write, tcol: Some(tc), prev: vec![] }
                };
                pw1 = Some(mk("w1", 2, q.clone(), p1, n1));
                pw2 = Some(mk("w2", 3, q.clone() + k(1), p2, n2));
                pd = None;
                for i in 0..2 {
                    tb.int(PAIR, true, vec![act.clone()], vec![x(vb[2 * i]), x(vb[2 * i + 1])]);
                }
            } else {
                pb = None;
                pw1 = Some(port(&mut tb, act.clone(), "w1", PortKind::Read, ts.clone(), 1, k(SP_MEM as u64), q.clone(), wv([x(w[0]), x(w[1]), x(w[2]), x(w[3])]), 0));
                pw2 = Some(port(&mut tb, act.clone(), "w2", PortKind::Read, ts.clone(), 2, k(SP_MEM as u64), q.clone() + k(1), wv([x(w[4]), x(w[5]), x(w[6]), x(w[7])]), 0));
                pd = operand(&mut tb, act.clone(), "d", d_op, true, ts.clone(), 3, fp.clone(), x(p.doff), wv([selb(0), selb(1), selb(2), selb(3)]));
            }
            for i in 0..4 {
                tb.int(PAIR, true, vec![act.clone()], vec![x(w[2 * i]), x(w[2 * i + 1])]);
            }
            let imm = if store && b_op == Op::Imm { [x(off), k(0), x(vimm[0]), x(vimm[1])] } else { [x(off), k(0), k(0), k(0)] };
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), imm, k(0), k(0), k(0)));
            state(&mut tb, &p, x(p.nxt), fp, x(p.u) + x(p.fee), z3(), z3());
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                let ofs = r.imm & 0xffff_ffff;
                assert!(ofs < 65536);
                set(row, off, ofs);
                let av = s.acc["a"].new;
                assert!(av[2] == 0 && av[3] == 0);
                set(row, a[0], av[0] as u64);
                set(row, a[1], av[1] as u64);
                let lo = av[0] as u64 + ofs;
                let cc = lo >> 16;
                let (ll0, ll1) = (lo & 0xffff, av[1] as u64 + cc);
                assert!(ll1 < 16);
                set(row, c0, cc);
                set(row, l0, ll0);
                set(row, l1, ll1);
                set(row, q0, ll0 / 4);
                cnt.r(ll0);
                cnt.r(ll0 / 4);
                cnt.r(4096 * ll1);
                for o in 0..4 {
                    set(row, sel[o], (ll0 % 4 == o as u64) as u64);
                }
                let (w1, w2) = (&s.acc["w1"], &s.acc["w2"]);
                let wb: Vec<u64> = [bytes_of(&w1.prev, 4), bytes_of(&w2.prev, 4)].concat();
                for i in 0..8 {
                    set(row, w[i], wb[i]);
                }
                for i in 0..4 {
                    cnt.p(wb[2 * i] as u32, wb[2 * i + 1] as u32);
                }
                if store {
                    let v = if r.b == Op::Imm { (r.imm >> 32) as u32 } else { unl(&s.acc["b"].new) as u32 };
                    let vbs = v.to_le_bytes();
                    for i in 0..4 {
                        set(row, vb[i], vbs[i] as u64);
                    }
                    cnt.p(vbs[0] as u32, vbs[1] as u32);
                    cnt.p(vbs[2] as u32, vbs[3] as u32);
                    if r.b == Op::Imm {
                        set(row, vimm[0], (v & 0xffff) as u64);
                        set(row, vimm[1], (v >> 16) as u64);
                    }
                }
                for (pp, n) in [(&pa, "a"), (&pb, "b"), (&pw1, "w1"), (&pw2, "w2"), (&pd, "d")] {
                    if let Some(pp) = pp {
                        fill_port(row, pp, &s.acc[n], cnt);
                    }
                }
            });
            Chip { tb, fill }
        }
        Cls::Call | Cls::Ret => {
            let ret = r.cls == Cls::Ret;
            let tgt = tb.c("tgt");
            let rpc = tb.c("rpc");
            let cfp = tb.c("cfp");
            let pf = if ret {
                port(&mut tb, act.clone(), "fr", PortKind::Read, ts.clone(), 0, k(SP_FRAME as u64), fp.clone(), [x(rpc), x(cfp), k(0), k(0)], 0)
            } else {
                port(&mut tb, act.clone(), "fr", PortKind::Write, ts.clone(), 0, k(SP_FRAME as u64), fp.clone() + x(p.boff), [x(p.nxt), fp.clone(), k(0), k(0)], 2)
            };
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), [k(0), k(0), k(0), k(0)], k(0), x(tgt), k(0)));
            if ret {
                state(&mut tb, &p, x(rpc), x(cfp), x(p.u) + x(p.fee), z3(), z3());
            } else {
                state(&mut tb, &p, x(tgt), fp.clone() + x(p.boff), x(p.u) + x(p.fee), z3(), z3());
            }
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                set(row, tgt, r.tgt as u64);
                let f = &s.acc["fr"];
                if ret {
                    set(row, rpc, f.new[0] as u64);
                    set(row, cfp, f.new[1] as u64);
                }
                fill_port(row, &pf, f, cnt);
            });
            Chip { tb, fill }
        }
        Cls::BulkStart => {
            let dv: [usize; 2] = tb.cs("D");
            let sv: [usize; 2] = tb.cs("S");
            let nv: [usize; 2] = tb.cs("N");
            let qd: [usize; 2] = tb.cs("qd");
            let qs: [usize; 2] = tb.cs("qs");
            let coff = tb.c("coff");
            let pa = operand(&mut tb, act.clone(), "a", a_op, false, ts.clone(), 0, fp.clone(), x(p.aoff), lv(&dv));
            let pb = operand(&mut tb, act.clone(), "b", b_op, false, ts.clone(), 1, fp.clone(), x(p.boff), lv(&sv));
            let pc_ = operand(&mut tb, act.clone(), "c", c_op, false, ts.clone(), 2, fp.clone(), x(coff), lv(&nv));
            // addr = 4·(q_lo + 2^16 q_hi), q < 2^18 (q_hi < 4)
            for (v, q) in [(&dv, &qd), (&sv, &qs)] {
                tb.con(x(v[0]) + k(65536) * x(v[1]) - k(4) * (x(q[0]) + k(65536) * x(q[1])));
                tb.int(RANGE, true, vec![act.clone()], vec![x(q[0])]);
                tb.int(RANGE, true, vec![act.clone()], vec![k(16384) * x(q[1])]);
            }
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, x(coff), [k(0), k(0), k(0), k(0)], k(0), k(0), k(0)));
            let qq = |q: &[usize; 2]| x(q[0]) + k(65536) * x(q[1]);
            state(&mut tb, &p, x(p.nxt), fp, x(p.u) + x(p.fee), z3(), [qq(&qd), qq(&qs), x(nv[0]) + k(65536) * x(nv[1])]);
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                set(row, coff, r.c.off() as u64);
                for (v, nm) in [(&dv, "a"), (&sv, "b"), (&nv, "c")] {
                    let l = s.acc[nm].new;
                    set(row, v[0], l[0] as u64);
                    set(row, v[1], l[1] as u64);
                }
                for (q, nm) in [(&qd, "a"), (&qs, "b")] {
                    let w = unl(&s.acc[nm].new) / 4;
                    set(row, q[0], w & 0xffff);
                    set(row, q[1], w >> 16);
                    cnt.r(w & 0xffff);
                    cnt.r(16384 * (w >> 16));
                }
                for (pp, n) in [(&pa, "a"), (&pb, "b"), (&pc_, "c")] {
                    fill_port(row, pp.as_ref().unwrap(), &s.acc[n], cnt);
                }
            });
            Chip { tb, fill }
        }
        Cls::Bulk16 => {
            let rg: [usize; 3] = tb.cs("r");
            let inv = tb.c("inv");
            let z = tb.c("z");
            let v: [usize; 8] = tb.cs("v");
            let mut ps = vec![];
            for kx in 0..4 {
                let val = [x(v[2 * kx]), x(v[2 * kx + 1]), k(0), k(0)];
                let sn: &'static str = ["s0", "s1", "s2", "s3"][kx];
                let dn: &'static str = ["d0", "d1", "d2", "d3"][kx];
                ps.push(port(&mut tb, act.clone(), sn, PortKind::Read, ts.clone(), kx as u64, k(SP_MEM as u64), x(rg[1]) + k(kx as u64), val.clone(), 0));
                ps.push(port(&mut tb, act.clone(), dn, PortKind::Write, ts.clone(), 4 + kx as u64, k(SP_MEM as u64), x(rg[0]) + k(kx as u64), val, 2));
            }
            // z = (n == 16)
            let nm16 = x(rg[2]) - k(16);
            tb.con(act.clone() * (x(z) - k(1) + nm16.clone() * x(inv)));
            tb.con(x(z) * nm16);
            tb.int(FETCH, true, vec![act.clone()], fetch_msg(&p, id, k(0), [k(0), k(0), k(0), k(0)], k(0), k(0), k(0)));
            let nz = k(1) - x(z);
            state(
                &mut tb,
                &p,
                x(z) * x(p.nxt) + nz.clone() * x(p.pc),
                fp,
                x(p.u) + k(16),
                [x(rg[0]), x(rg[1]), x(rg[2])],
                [nz.clone() * (x(rg[0]) + k(4)), nz.clone() * (x(rg[1]) + k(4)), nz * (x(rg[2]) - k(16))],
            );
            let fill: Fill = Box::new(move |row, r, s, cnt| {
                fill_pre(row, &p, r, s, cnt);
                for i in 0..3 {
                    set(row, rg[i], s.regs[i] as u64);
                }
                let n = s.regs[2] as u64;
                row[inv] = if n == 16 { F::ZERO } else { (F::from_u64(n) - F::from_u64(16)).inverse() };
                set(row, z, (n == 16) as u64);
                for kx in 0..4 {
                    let a = &s.acc[["s0", "s1", "s2", "s3"][kx]];
                    set(row, v[2 * kx], a.new[0] as u64);
                    set(row, v[2 * kx + 1], a.new[1] as u64);
                }
                for pp in &ps {
                    fill_port(row, pp, &s.acc[pp.name], cnt);
                }
            });
            Chip { tb, fill }
        }
    }
}

// =========================================================================================
// Build: chips + memory boundary + public-bound code/io/initial memory + lookup tables
// =========================================================================================

pub struct Built {
    pub air: Air,
    pub traces: Vec<RowMajorMatrix<F>>,
    pub active: Vec<usize>,
    pub kind: Vec<&'static str>,
    pub names: Vec<Vec<String>>,
    /// claim bytes (public segments)
    pub cb: Vec<u8>,
}

fn pad(n: usize) -> usize {
    n.max(4).next_power_of_two()
}
fn bits_for(m: u32) -> usize {
    (32 - m.leading_zeros()).max(1) as usize
}

/// code record bytes: kid(2) doff(2) aoff(2) boff(2) coff(2) imm(8) pol(1) fee(4) next(3) tgt(3) fdelta(2) = 31
pub const CODE_REC: usize = 31;
fn code_fields(i: usize, r: &R) -> [u64; FETCH_W] {
    let imm = match r.cls {
        Cls::Alu if r.b == Op::Imm => limbs(r.imm),
        Cls::Ld => [r.imm as u16, 0, 0, 0],
        Cls::St if r.b == Op::Imm => [r.imm as u16, 0, (r.imm >> 32) as u16, (r.imm >> 48) as u16],
        Cls::St => [r.imm as u16, 0, 0, 0],
        _ => [0; 4],
    };
    let pol = match r.cls {
        Cls::Alu => r.sub as u64,
        Cls::Brz => r.pol as u64,
        _ => 0,
    };
    let boff = if r.cls == Cls::Call { r.fdelta } else { r.b.off() };
    let tgt = if matches!(r.cls, Cls::Brz | Cls::Call) { r.tgt as u64 } else { 0 };
    [i as u64, kid(r), r.d.off() as u64, r.a.off() as u64, boff as u64, r.c.off() as u64, imm[0] as u64, imm[1] as u64, imm[2] as u64, imm[3] as u64, pol, r.fee as u64, r.next as u64, tgt, 0]
}
const CODE_W: [usize; FETCH_W] = [0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3, 3, 2];

pub fn build(rp: &RProg, run: &Run) -> Built {
    let mut cnt = Counts { range: vec![0; 65536], pair: vec![0; 65536], rt: vec![0; 1 << LOG_RT], code: vec![0; rp.rows.len()] };
    let (mut tables, mut traces, mut active, mut kind) = (vec![], vec![], vec![], vec![]);
    let mut names: Vec<Vec<String>> = vec![];
    // chips grouped by key
    let mut by: Vec<((Cls, Op, Op, Op, Op), Vec<usize>)> = vec![];
    for (i, s) in run.steps.iter().enumerate() {
        let key = rp.rows[s.rpc].key();
        match by.iter_mut().find(|(k, _)| *k == key) {
            Some((_, v)) => v.push(i),
            None => by.push((key, vec![i])),
        }
    }
    for (_, ix) in &by {
        let r0 = &rp.rows[run.steps[ix[0]].rpc];
        let ch = chip_for(r0);
        let w = ch.tb.names.len();
        let h = pad(ix.len());
        let mut v = vec![F::ZERO; w * h];
        for (r, si) in ix.iter().enumerate() {
            let s = &run.steps[*si];
            (ch.fill)(&mut v[r * w..(r + 1) * w], &rp.rows[s.rpc], s, &mut cnt);
        }
        names.push(ch.tb.names.clone());
        tables.push(ch.tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(ix.len());
        kind.push("chip");
    }
    // ---------------- claim bytes (public) ----------------
    // header: [n_code, off_code, n_mem, off_mem, n_io, off_io] (u32 LE), then the records
    let mut init_pub: Vec<((u32, u32), Limbs)> = run.init.iter().filter(|(_, v)| **v != [0; 4]).map(|(k, v)| (*k, *v)).collect();
    init_pub.sort();
    const MEM_REC: usize = 1 + 4 + 8;
    const IO_REC: usize = 1 + 3 + 4 + 4 + 4 + 12;
    let mut cb = vec![0u8; 24];
    let put = |cb: &mut Vec<u8>, at: usize, v: u32| cb[at..at + 4].copy_from_slice(&v.to_le_bytes());
    let off_code = cb.len();
    for (i, r) in rp.rows.iter().enumerate() {
        let f = code_fields(i, r);
        for j in 1..FETCH_W {
            cb.extend_from_slice(&f[j].to_le_bytes()[..CODE_W[j]]);
        }
    }
    let off_mem = cb.len();
    for ((sp, ad), v) in &init_pub {
        cb.push(*sp as u8);
        cb.extend_from_slice(&ad.to_le_bytes());
        for l in v {
            cb.extend_from_slice(&l.to_le_bytes());
        }
    }
    let off_io = cb.len();
    let (fpc, fts, ffp, fu) = run.final_state;
    for (kd, pc, ts, fp, u) in [(0u8, rp.entry[0] as u32, 1u32, 0u32, 0u32), (1, fpc as u32, fts, ffp, fu)] {
        cb.push(kd);
        cb.extend_from_slice(&pc.to_le_bytes()[..3]);
        cb.extend_from_slice(&ts.to_le_bytes());
        cb.extend_from_slice(&fp.to_le_bytes());
        cb.extend_from_slice(&u.to_le_bytes());
        cb.extend_from_slice(&[0u8; 12]);
    }
    put(&mut cb, 0, rp.rows.len() as u32);
    put(&mut cb, 4, off_code as u32);
    put(&mut cb, 8, init_pub.len() as u32);
    put(&mut cb, 12, off_mem as u32);
    put(&mut cb, 16, 2);
    put(&mut cb, 20, off_io as u32);
    let seg = |bus, w, ca, sa, idx: Option<u64>| PubSeg { bus, send: true, width: w, count_at: ca, start: 0, prefix: vec![], index_base: idx, start_at: Some(sa) };
    let pub_segs = vec![seg(PUBC, CODE_REC, 0, 4, Some(0)), seg(PUBM, MEM_REC, 8, 12, None), seg(PUBIO, IO_REC, 16, 20, None)];
    // ---------------- memory boundary ----------------
    {
        let mut tb = TB::new("mbound");
        let act = tb.c("act");
        let nact = tb.c("nact");
        let hi_ = tb.c("has_init");
        let sp = tb.c("space");
        let ad = tb.c("addr");
        let iv: [usize; 4] = tb.cs("I");
        let fv: [usize; 4] = tb.cs("F");
        let tf = tb.c("tf");
        let lo = tb.c("lo");
        let hi = tb.c("hi");
        let mut m = vec![x(sp), x(ad)];
        m.extend(lv(&iv));
        m.push(k(0));
        tb.int(MEM, true, vec![x(act)], m);
        let mut m = vec![x(sp), x(ad)];
        m.extend(lv(&fv));
        m.push(x(tf));
        tb.int(MEM, false, vec![x(act)], m);
        let mut m = vec![x(sp), x(ad)];
        m.extend(lv(&iv));
        tb.int(MINIT, false, vec![x(hi_)], m);
        for l in iv {
            tb.con((k(1) - x(hi_)) * x(l));
        }
        tb.con(x(hi_) * (k(1) - x(act)));
        let key = |s: X, a: X| s * k(1 << 24) + a;
        tb.con(X(E::IsTransition) * (x(nact) - nx(act)));
        tb.con(X(E::IsLast) * x(nact));
        tb.con(X(E::IsTransition) * (k(1) - x(act)) * nx(act));
        tb.con(X(E::IsTransition) * x(nact) * (key(nx(sp), nx(ad)) - key(x(sp), x(ad)) - k(1) - x(lo) - k(65536) * x(hi)));
        tb.int(RANGE, true, vec![x(act)], vec![x(lo)]);
        tb.int(RANGE, true, vec![x(act)], vec![x(hi)]);
        let mut keys: Vec<(u32, u32)> = run.mem.keys().copied().collect();
        keys.sort();
        let w = tb.names.len();
        let h = pad(keys.len());
        let mut v = vec![F::ZERO; w * h];
        for (r, kk) in keys.iter().enumerate() {
            let row = &mut v[r * w..(r + 1) * w];
            let (fin, t) = run.mem[kk];
            let init = run.init[kk];
            row[act] = F::ONE;
            row[nact] = F::from_bool(r + 1 < keys.len());
            row[hi_] = F::from_bool(init != [0; 4]);
            row[sp] = F::from_u32(kk.0);
            row[ad] = F::from_u32(kk.1);
            for i in 0..4 {
                set(row, iv[i], init[i] as u64);
                set(row, fv[i], fin[i] as u64);
            }
            row[tf] = F::from_u32(t);
            let d = if r + 1 < keys.len() { ((keys[r + 1].0 << 24) | keys[r + 1].1) - ((kk.0 << 24) | kk.1) - 1 } else { 0 };
            set(row, lo, (d & 0xffff) as u64);
            set(row, hi, (d >> 16) as u64);
            cnt.r((d & 0xffff) as u64);
            cnt.r((d >> 16) as u64);
        }
        names.push(tb.names.clone());
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(keys.len());
        kind.push("mem");
    }
    // ---------------- minit: public initial words -> MINIT ----------------
    {
        let mut tb = TB::new("minit");
        let act = tb.c("act");
        let b: [usize; MEM_REC] = tb.cs("b");
        tb.int(PUBM, false, vec![x(act)], b.iter().map(|c| x(*c)).collect());
        let addr = x(b[1]) + k(1 << 8) * x(b[2]) + k(1 << 16) * x(b[3]) + k(1 << 24) * x(b[4]);
        let mut m = vec![x(b[0]), addr];
        for l in 0..4 {
            m.push(x(b[5 + 2 * l]) + k(256) * x(b[6 + 2 * l]));
        }
        tb.int(MINIT, true, vec![x(act)], m);
        let w = tb.names.len();
        let h = pad(init_pub.len());
        let mut v = vec![F::ZERO; w * h];
        for (r, i) in (0..init_pub.len()).enumerate() {
            let row = &mut v[r * w..(r + 1) * w];
            row[act] = F::ONE;
            for j in 0..MEM_REC {
                row[b[j]] = F::from_u32(cb[off_mem + i * MEM_REC + j] as u32);
            }
        }
        names.push(tb.names.clone());
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(init_pub.len());
        kind.push("fixed");
    }
    // ---------------- code table (public) ----------------
    {
        let mut tb = TB::new("code");
        let act = tb.c("act");
        let pc = tb.c("pc");
        let nb: usize = CODE_W.iter().sum();
        let by: Vec<usize> = (0..nb).map(|i| tb.c(&format!("b{i}"))).collect();
        let mb = bits_for(*cnt.code.iter().max().unwrap_or(&1));
        let mcols: Vec<usize> = (0..mb).map(|i| tb.c(&format!("m{i}"))).collect();
        let mut msg = vec![x(pc)];
        let mut o = 0;
        for j in 1..FETCH_W {
            let mut e = k(0);
            for q in 0..CODE_W[j] {
                e = e + k(1u64 << (8 * q)) * x(by[o + q]);
            }
            o += CODE_W[j];
            msg.push(e);
        }
        tb.int(FETCH, false, mcols.iter().map(|c| x(*c)).collect(), msg);
        let mut pm = vec![x(pc)];
        pm.extend(by.iter().map(|c| x(*c)));
        tb.int(PUBC, false, vec![x(act)], pm);
        for m in &mcols {
            tb.con(x(*m) * (k(1) - x(act)));
        }
        let w = tb.names.len();
        let h = pad(rp.rows.len());
        let mut v = vec![F::ZERO; w * h];
        for i in 0..rp.rows.len() {
            let row = &mut v[i * w..(i + 1) * w];
            row[act] = F::ONE;
            row[pc] = F::from_usize(i);
            for j in 0..nb {
                row[by[j]] = F::from_u32(cb[off_code + i * CODE_REC + j] as u32);
            }
            for (q, m) in mcols.iter().enumerate() {
                row[*m] = F::from_u32((cnt.code[i] >> q) & 1);
            }
        }
        names.push(tb.names.clone());
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(rp.rows.len());
        kind.push("fixed");
    }
    // ---------------- io (public initial / final state) ----------------
    {
        let mut tb = TB::new("io");
        let act = tb.c("act");
        let b: [usize; IO_REC] = tb.cs("b");
        tb.int(PUBIO, false, vec![x(act)], b.iter().map(|c| x(*c)).collect());
        let le = |o: usize, n: usize| -> X { sum((0..n).map(|q| k(1u64 << (8 * q)) * x(b[o + q])).collect()) };
        let mut st = vec![le(1, 3), le(4, 4), le(8, 4), le(12, 4)];
        for r in 0..3 {
            st.push(le(16 + 4 * r, 4));
        }
        tb.con(x(b[0]) * (x(b[0]) - k(1)));
        tb.int(STATE, true, vec![x(act) * (k(1) - x(b[0]))], st.clone());
        tb.int(STATE, false, vec![x(act) * x(b[0])], st);
        let w = tb.names.len();
        let mut v = vec![F::ZERO; w * 4];
        for r in 0..2 {
            v[r * w + act] = F::ONE;
            for j in 0..IO_REC {
                v[r * w + b[j]] = F::from_u32(cb[off_io + r * IO_REC + j] as u32);
            }
        }
        names.push(tb.names.clone());
        tables.push(tb.table());
        traces.push(RowMajorMatrix::new(v, w));
        active.push(2);
        kind.push("fixed");
    }
    // ---------------- lookup tables ----------------
    let lookup = |name: &str, logn: usize, counts: &Vec<u32>, bus: usize, pair: bool| -> (Table, RowMajorMatrix<F>) {
        let mut tb = TB::new(name);
        let n = 1usize << logn;
        let mb = bits_for(*counts.iter().max().unwrap_or(&1));
        let (vc, mcols, extra);
        if pair {
            let b0 = tb.c("b0");
            let b1 = tb.c("b1");
            let fl = tb.c("fl");
            let inv = tb.c("inv");
            vc = (b0, b1);
            extra = Some((fl, inv));
            mcols = (0..mb).map(|i| tb.c(&format!("m{i}"))).collect::<Vec<_>>();
            tb.con(X(E::IsFirst) * x(b0));
            tb.con(X(E::IsFirst) * x(b1));
            tb.con(x(fl) * (x(fl) - k(1)));
            tb.con(x(fl) * (x(b0) - k(255)));
            tb.con((x(b0) - k(255)) * x(inv) - (k(1) - x(fl)));
            tb.con(X(E::IsTransition) * (nx(b0) - (x(b0) + k(1)) * (k(1) - x(fl))));
            tb.con(X(E::IsTransition) * (nx(b1) - x(b1) - x(fl)));
            tb.int(bus, false, mcols.iter().map(|c| x(*c)).collect(), vec![x(b0), x(b1)]);
        } else {
            let v0 = tb.c("v");
            vc = (v0, 0);
            extra = None;
            mcols = (0..mb).map(|i| tb.c(&format!("m{i}"))).collect::<Vec<_>>();
            tb.con(X(E::IsFirst) * x(v0));
            tb.con(X(E::IsTransition) * (nx(v0) - x(v0) - k(1)));
            tb.int(bus, false, mcols.iter().map(|c| x(*c)).collect(), vec![x(v0)]);
        }
        let w = tb.names.len();
        let mut v = vec![F::ZERO; w * n];
        for i in 0..n {
            let row = &mut v[i * w..(i + 1) * w];
            if pair {
                let (x0, x1) = (i & 255, i >> 8);
                row[vc.0] = F::from_usize(x0);
                row[vc.1] = F::from_usize(x1);
                let (fl, inv) = extra.unwrap();
                row[fl] = F::from_bool(x0 == 255);
                row[inv] = if x0 == 255 { F::ZERO } else { (F::from_usize(x0) - F::from_u32(255)).inverse() };
            } else {
                row[vc.0] = F::from_usize(i);
            }
            for (q, m) in mcols.iter().enumerate() {
                row[*m] = F::from_u32((counts[i] >> q) & 1);
            }
        }
        (tb.table(), RowMajorMatrix::new(v, w))
    };
    let mut add = |t: (Table, RowMajorMatrix<F>), n: usize| {
        names.push(vec![]);
        tables.push(t.0);
        traces.push(t.1);
        active.push(n);
        kind.push("fixed");
    };
    if cnt.pair.iter().any(|c| *c > 0) {
        add(lookup("pair8", 16, &cnt.pair, PAIR, true), 65536);
    }
    add(lookup("range16", 16, &cnt.range, RANGE, false), 65536);
    add(lookup("rangeT", LOG_RT, &cnt.rt, RANGET, false), 1 << LOG_RT);
    let air = Air { tables, num_buses: NBUS, num_pub: 0, pub_segs, max_pub: 1 << 26, aux_group: 1, v2: true };
    Built { air, traces, active, kind, names, cb }
}

// =========================================================================================
// Programs
// =========================================================================================

fn f0(nparams: u32, nlocals: u32, nresults: u32, code: Vec<I>) -> Func {
    Func { nparams, nlocals, nresults, code }
}

/// measured-mix loop (as v0): while i != 0 { acc = acc*x + K; i -= 1 }
pub fn measured(iters: u64) -> Prog {
    use I::*;
    let code = vec![LocalGet(0), I64Eqz, BrIf(14), LocalGet(1), LocalGet(2), I64Mul, I64Const(0x9e37_79b9_7f4a_7c15), I64Add, LocalSet(1), LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0), End];
    Prog { name: "measured-mix loop".into(), funcs: vec![f0(3, 3, 0, code)], args: vec![iters, 7, 0x1234_5678_9abc_def1], mem0: vec![] }
}

/// adversarial: unaligned i32.load pointer chase, `chain` loads per iteration
pub fn loadchain(iters: u64, chain: usize) -> Prog {
    use I::*;
    let mut code = vec![LocalGet(0), I64Eqz, BrIf(0), LocalGet(1)];
    for _ in 0..chain {
        code.push(I32Load(0));
    }
    code.push(LocalSet(1));
    code.extend([LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0)]);
    let e = code.len();
    code.push(End);
    code[2] = BrIf(e);
    // a pointer cycle over 4096 unaligned addresses (stride 1031 words, +1..3 bytes)
    let mut mem0 = vec![0u8; 8 * 4096 + 64];
    let addr = |w: u32| w * 8 + 1 + (w % 3);
    for w in 0..4096u32 {
        let a = addr(w) as usize;
        mem0[a..a + 4].copy_from_slice(&addr((w * 1031 + 17) % 4096).to_le_bytes());
    }
    Prog { name: format!("unaligned i32.load chain ({chain}/iter)"), funcs: vec![f0(2, 2, 0, code)], args: vec![iters, addr(0) as u64], mem0 }
}

/// adversarial: `x = x / d` style div chain (local.get b; i64.div_u), 8 per iteration
pub fn divchain(iters: u64) -> Prog {
    use I::*;
    let mut code = vec![LocalGet(0), I64Eqz, BrIf(0)];
    for _ in 0..8 {
        code.extend([LocalGet(1), LocalGet(2), I64DivU, LocalSet(1)]);
    }
    code.extend([LocalGet(1), LocalGet(3), I64Add, LocalSet(1), LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0)]);
    let e = code.len();
    code.push(End);
    code[2] = BrIf(e);
    Prog { name: "i64.div_u chain (8/iter)".into(), funcs: vec![f0(4, 4, 0, code)], args: vec![iters, u64::MAX - 12345, 3, u64::MAX / 2], mem0: vec![] }
}

/// adversarial: calls of an empty function (and a 1-param/1-result function)
pub fn callchain(iters: u64) -> Prog {
    use I::*;
    let mut code = vec![LocalGet(0), I64Eqz, BrIf(0)];
    for _ in 0..8 {
        code.push(Call(1));
    }
    code.extend([LocalGet(1), Call(2), LocalSet(1)]);
    code.extend([LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0)]);
    let e = code.len();
    code.push(End);
    code[2] = BrIf(e);
    let empty = f0(0, 0, 0, vec![End]);
    let inc = f0(1, 2, 1, vec![LocalGet(0), I64Const(3), I64Add, LocalSet(1), LocalGet(1), End]);
    Prog { name: "call chain (8 empty calls + 1 call(x)->x+3 per iter)".into(), funcs: vec![f0(2, 2, 0, code), empty, inc], args: vec![iters, 5], mem0: vec![] }
}

/// store/load mix with unaligned stores and constant stores
pub fn memmix(iters: u64) -> Prog {
    use I::*;
    let code = vec![
        LocalGet(0), I64Eqz, BrIf(23),
        LocalGet(1), LocalGet(2), I32Store(1),
        LocalGet(1), I32Const(0xdead_beef), I32Store(7),
        LocalGet(1), I32Load(3), LocalSet(2),
        LocalGet(1), I64Const(8), I64Add, LocalSet(1),
        LocalGet(0), I64Const(1), I64Sub, LocalSet(0),
        Br(0), End, End, End,
    ];
    let mut c = code;
    c.truncate(21);
    c.push(End);
    c[2] = BrIf(21);
    let mut mem0 = vec![0u8; 8 * iters as usize + 64];
    for (i, b) in mem0.iter_mut().enumerate() {
        *b = (i * 151 % 251) as u8;
    }
    Prog { name: "unaligned store/load mix".into(), funcs: vec![f0(3, 3, 0, c)], args: vec![iters, 0, 5], mem0 }
}

/// bulk copy: memory.copy of `n` bytes per iteration
pub fn bulk(iters: u64, n: u64) -> Prog {
    use I::*;
    let code = vec![
        LocalGet(0), I64Eqz, BrIf(13),
        I32Const(0x8_0000), LocalGet(1), I64Const(n), MemCopy,
        LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0), End, End,
    ];
    let mut c = code;
    c.truncate(12);
    c.push(End);
    c[2] = BrIf(12);
    let mut mem0 = vec![0u8; 0x4_0000];
    for (i, b) in mem0.iter_mut().enumerate() {
        *b = (i * 7 % 253) as u8;
    }
    Prog { name: format!("memory.copy {n} B per iteration"), funcs: vec![f0(2, 2, 0, c)], args: vec![iters, 0x1_0000], mem0 }
}
