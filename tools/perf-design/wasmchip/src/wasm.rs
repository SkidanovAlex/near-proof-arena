//! A WASM subset (flat IR with absolute branch targets), its reference stack interpreter, the
//! register-form translator of V3-PERF-DESIGN §2.2 and the register machine whose rows the
//! chips prove.
//!
//! Translation rules (all static, per basic block; this is what PREP would do per contract):
//! * `local.get i` / `*.const c` push *pending operands* and emit no row;
//! * a pending `local.get i` is materialised (a `mov` row) only if local `i` is overwritten
//!   while the operand is still on the stack;
//! * `local.set/tee i` retargets the destination of the row that produced the stack top
//!   (if it was the immediately preceding row), otherwise it is a `mov` row;
//! * `i64.eqz; br_if` fuse into one `brz` row; `br` is folded into the `next` field of the
//!   preceding row (static jump);
//! * gas: block-level charge (finite-wasm style): the fee of a basic block (its WASM op count,
//!   in `regular_op_cost` units) is attached to the first row emitted for the block.
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum W {
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    I64Const(u64),
    I32Const(u32),
    I64Add,
    I64Sub,
    I64Mul,
    I64Eqz,
    /// branch to absolute pc if top != 0
    BrIf(usize),
    Br(usize),
    I32Load(u32),
    I32Store(u32),
    Halt,
}

pub struct Prog {
    pub name: String,
    pub code: Vec<W>,
    pub nlocals: u32,
    pub locals0: Vec<u64>,
    /// initial linear memory, word-addressed (byte address / 4)
    pub mem0: HashMap<u32, u32>,
}

/// Reference semantics. Returns (wasm ops executed, final locals, final memory words).
pub fn interpret(p: &Prog) -> (u64, Vec<u64>, HashMap<u32, u32>) {
    let mut loc = p.locals0.clone();
    let mut mem = p.mem0.clone();
    let mut st: Vec<u64> = vec![];
    let mut pc = 0usize;
    let mut n = 0u64;
    loop {
        let i = p.code[pc];
        if i == W::Halt {
            break;
        }
        n += 1;
        pc += 1;
        match i {
            W::LocalGet(x) => st.push(loc[x as usize]),
            W::LocalSet(x) => loc[x as usize] = st.pop().unwrap(),
            W::LocalTee(x) => loc[x as usize] = *st.last().unwrap(),
            W::I64Const(c) => st.push(c),
            W::I32Const(c) => st.push(c as u64),
            W::I64Add | W::I64Sub | W::I64Mul => {
                let b = st.pop().unwrap();
                let a = st.pop().unwrap();
                st.push(match i {
                    W::I64Add => a.wrapping_add(b),
                    W::I64Sub => a.wrapping_sub(b),
                    _ => a.wrapping_mul(b),
                });
            }
            W::I64Eqz => {
                let a = st.pop().unwrap();
                st.push((a == 0) as u64)
            }
            W::BrIf(t) => {
                if st.pop().unwrap() != 0 {
                    pc = t
                }
            }
            W::Br(t) => pc = t,
            W::I32Load(off) => {
                let a = st.pop().unwrap() as u32 as u64 + off as u64;
                assert!(a % 4 == 0, "spike: aligned accesses only");
                st.push(*mem.get(&((a / 4) as u32)).unwrap_or(&0) as u64)
            }
            W::I32Store(off) => {
                let v = st.pop().unwrap() as u32;
                let a = st.pop().unwrap() as u32 as u64 + off as u64;
                assert!(a % 4 == 0, "spike: aligned accesses only");
                mem.insert((a / 4) as u32, v);
            }
            W::Halt => unreachable!(),
        }
    }
    (n, loc, mem)
}

// ---------------------------------------------------------------------------------------
// Register form
// ---------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Cls {
    AluRI = 1,
    AluRR = 2,
    Mul = 3,
    Brz = 4,
    Ld = 5,
    St = 6,
}

#[derive(Clone, Debug)]
pub struct RI {
    pub cls: Cls,
    pub dst: u32,
    pub a: u32,
    pub b: u32,
    pub imm: u64,
    /// AluRI/AluRR: subtract; Brz: jump if zero (1) / if non-zero (0)
    pub pol: bool,
    pub next: usize,
    pub tgt: usize,
    pub fee: u32,
}

pub struct RProg {
    pub rows: Vec<RI>,
    pub halt: usize,
    pub nslots: u32,
    pub zero: u32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum AE {
    Local(u32),
    Const(u64),
    Temp(u32),
    Eqz(u32),
}

fn leaders(code: &[W]) -> Vec<bool> {
    let mut l = vec![false; code.len() + 1];
    l[0] = true;
    for (pc, i) in code.iter().enumerate() {
        match i {
            W::BrIf(t) | W::Br(t) => {
                l[*t] = true;
                l[pc + 1] = true;
            }
            _ => {}
        }
    }
    l
}

pub fn translate(p: &Prog) -> RProg {
    let code = &p.code;
    let lead = leaders(code);
    let zero = p.nlocals;
    let t0 = p.nlocals + 1;
    let mut rows: Vec<RI> = vec![];
    let mut rpc_of: Vec<Option<usize>> = vec![None; code.len() + 1];
    let mut fix_tgt: Vec<(usize, usize)> = vec![]; // (row, wasm pc) for brz targets
    let mut fix_next: Vec<(usize, usize)> = vec![]; // (row, wasm pc) for folded br
    let mut st: Vec<AE> = vec![];
    let mut maxdepth = 0u32;
    let mut pending_fee = 0u32;
    let mut block_first_row = 0usize;
    // the row that produced the current stack top (for local.set retargeting)
    let mut last_prod: Option<usize> = None;
    let emit = |rows: &mut Vec<RI>, pending_fee: &mut u32, mut r: RI| -> usize {
        r.fee = std::mem::take(pending_fee);
        r.next = rows.len() + 1;
        rows.push(r);
        rows.len() - 1
    };
    let ri = |cls, dst, a, b, imm, pol| RI { cls, dst, a, b, imm, pol, next: 0, tgt: 0, fee: 0 };
    for pc in 0..code.len() {
        if lead[pc] {
            assert!(st.is_empty(), "spike translator: stack must be empty at block boundaries");
            assert!(pending_fee == 0, "block emitted no row");
            rpc_of[pc] = Some(rows.len());
            block_first_row = rows.len();
            // block fee: ops until the next leader (Halt excluded)
            let mut f = 0;
            let mut q = pc;
            while q < code.len() && code[q] != W::Halt && (q == pc || !lead[q]) {
                f += 1;
                q += 1;
            }
            pending_fee = f;
            last_prod = None;
        }
        let depth = st.len() as u32;
        maxdepth = maxdepth.max(depth + 1);
        // materialise an abstract entry into a slot (consts go through a mov from ZERO)
        macro_rules! mat {
            ($e:expr, $d:expr) => {{
                match $e {
                    AE::Local(i) => i,
                    AE::Temp(s) => s,
                    AE::Const(c) => {
                        let s = t0 + $d;
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, s, zero, 0, c, false));
                        s
                    }
                    AE::Eqz(_) => panic!("spike: eqz must feed br_if"),
                }
            }};
        }
        match code[pc] {
            W::Halt => {
                rpc_of[pc] = Some(rows.len());
            }
            W::LocalGet(i) => {
                st.push(AE::Local(i));
                last_prod = None
            }
            W::I64Const(c) => {
                st.push(AE::Const(c));
                last_prod = None
            }
            W::I32Const(c) => {
                st.push(AE::Const(c as u64));
                last_prod = None
            }
            W::LocalSet(i) | W::LocalTee(i) => {
                let tee = matches!(code[pc], W::LocalTee(_));
                let top = st.pop().unwrap();
                // pending reads of local i below the top must be materialised first
                for d in 0..st.len() {
                    if st[d] == AE::Local(i) {
                        let s = t0 + d as u32;
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, s, i, 0, 0, false));
                        st[d] = AE::Temp(s);
                    }
                }
                match (top, last_prod) {
                    (AE::Temp(s), Some(r)) if rows[r].dst == s && r + 1 == rows.len() => {
                        rows[r].dst = i;
                    }
                    (AE::Const(c), _) => {
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, i, zero, 0, c, false));
                    }
                    (e, _) => {
                        let s = mat!(e, depth - 1);
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, i, s, 0, 0, false));
                    }
                }
                if tee {
                    st.push(AE::Local(i));
                }
                last_prod = None
            }
            W::I64Add | W::I64Sub | W::I64Mul => {
                let b = st.pop().unwrap();
                let a = st.pop().unwrap();
                let d = depth - 2;
                let dst = t0 + d;
                let sub = code[pc] == W::I64Sub;
                let r = match (code[pc], a, b) {
                    (W::I64Mul, _, _) => {
                        let sa = mat!(a, d);
                        let sb = mat!(b, d + 1);
                        emit(&mut rows, &mut pending_fee, ri(Cls::Mul, dst, sa, sb, 0, false))
                    }
                    (_, a, AE::Const(c)) if !matches!(a, AE::Const(_)) => {
                        let sa = mat!(a, d);
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, dst, sa, 0, c, sub))
                    }
                    (W::I64Add, AE::Const(c), b) if !matches!(b, AE::Const(_)) => {
                        let sb = mat!(b, d + 1);
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRI, dst, sb, 0, c, false))
                    }
                    _ => {
                        let sa = mat!(a, d);
                        let sb = mat!(b, d + 1);
                        emit(&mut rows, &mut pending_fee, ri(Cls::AluRR, dst, sa, sb, 0, sub))
                    }
                };
                st.push(AE::Temp(dst));
                last_prod = Some(r);
            }
            W::I64Eqz => {
                let a = st.pop().unwrap();
                let s = mat!(a, depth - 1);
                st.push(AE::Eqz(s));
                last_prod = None
            }
            W::BrIf(t) => {
                let c = st.pop().unwrap();
                let (s, pol) = match c {
                    AE::Eqz(s) => (s, true),
                    e => (mat!(e, depth - 1), false),
                };
                let r = emit(&mut rows, &mut pending_fee, ri(Cls::Brz, 0, s, 0, 0, pol));
                fix_tgt.push((r, t));
                last_prod = None
            }
            W::Br(t) => {
                assert!(st.is_empty());
                assert!(rows.len() > block_first_row, "spike: br must follow a row in its block");
                fix_next.push((rows.len() - 1, t));
                last_prod = None
            }
            W::I32Load(off) => {
                let a = st.pop().unwrap();
                let d = depth - 1;
                let sa = mat!(a, d);
                let r = emit(&mut rows, &mut pending_fee, ri(Cls::Ld, t0 + d, sa, 0, off as u64, false));
                st.push(AE::Temp(t0 + d));
                last_prod = Some(r);
            }
            W::I32Store(off) => {
                let v = st.pop().unwrap();
                let a = st.pop().unwrap();
                let d = depth - 2;
                let sa = mat!(a, d);
                let sv = mat!(v, d + 1);
                emit(&mut rows, &mut pending_fee, ri(Cls::St, 0, sa, sv, off as u64, false));
                last_prod = None
            }
        }
    }
    for (r, t) in fix_tgt {
        rows[r].tgt = rpc_of[t].expect("branch target must be a leader");
    }
    for (r, t) in fix_next {
        rows[r].next = rpc_of[t].expect("br target must be a leader");
    }
    let halt = rpc_of[code.iter().position(|i| *i == W::Halt).unwrap()].unwrap();
    RProg { rows, halt, nslots: t0 + maxdepth + 2, zero }
}

// ---------------------------------------------------------------------------------------
// Register machine with memory-access recording
// ---------------------------------------------------------------------------------------

pub type Limbs = [u16; 4];
pub fn limbs(v: u64) -> Limbs {
    [v as u16, (v >> 16) as u16, (v >> 32) as u16, (v >> 48) as u16]
}
pub fn unlimbs(l: &Limbs) -> u64 {
    l[0] as u64 | (l[1] as u64) << 16 | (l[2] as u64) << 32 | (l[3] as u64) << 48
}

/// One memory access as seen by a chip row.
#[derive(Clone, Copy, Debug, Default)]
pub struct Acc {
    pub space: u32,
    pub addr: u32,
    pub prev: Limbs,
    pub new: Limbs,
    pub t_prev: u32,
    pub t: u32,
}

/// One executed row: the instruction, its state, and its accesses (in sub-slot order).
pub struct Step {
    pub rpc: usize,
    pub ts: u32,
    pub u: u32,
    pub npc: usize,
    pub acc: Vec<Acc>,
}

pub struct Mem {
    pub cur: HashMap<(u32, u32), (Limbs, u32)>,
    pub init: HashMap<(u32, u32), Limbs>,
    init_src: HashMap<(u32, u32), Limbs>,
}

impl Mem {
    fn get(&mut self, k: (u32, u32)) -> (Limbs, u32) {
        if let Some(v) = self.cur.get(&k) {
            return *v;
        }
        let v = *self.init_src.get(&k).unwrap_or(&[0; 4]);
        self.init.insert(k, v);
        self.cur.insert(k, (v, 0));
        (v, 0)
    }
    fn access(&mut self, space: u32, addr: u32, newv: Option<Limbs>, t: u32) -> Acc {
        let (prev, t_prev) = self.get((space, addr));
        let new = newv.unwrap_or(prev);
        self.cur.insert((space, addr), (new, t));
        Acc { space, addr, prev, new, t_prev, t }
    }
}

pub struct Run {
    pub steps: Vec<Step>,
    pub mem: Mem,
    pub final_state: (usize, u32, u32),
}

pub fn execute(rp: &RProg, p: &Prog) -> Run {
    let mut init_src = HashMap::new();
    for (i, v) in p.locals0.iter().enumerate() {
        init_src.insert((0, i as u32), limbs(*v));
    }
    for (w, v) in &p.mem0 {
        init_src.insert((1, *w), limbs(*v as u64));
    }
    let mut mem = Mem { cur: HashMap::new(), init: HashMap::new(), init_src };
    let mut steps = vec![];
    let (mut rpc, mut ts, mut u) = (0usize, 1u32, 0u32);
    while rpc != rp.halt {
        let r = &rp.rows[rpc];
        let t = |k: u32| 4 * ts + k;
        let mut acc = vec![];
        let mut npc = r.next;
        match r.cls {
            Cls::AluRI | Cls::AluRR | Cls::Mul => {
                let a = mem.access(0, r.a, None, t(0));
                let av = unlimbs(&a.new);
                acc.push(a);
                let bv = if r.cls == Cls::AluRI {
                    r.imm
                } else {
                    let b = mem.access(0, r.b, None, t(1));
                    acc.push(b);
                    unlimbs(&b.new)
                };
                let c = match (r.cls, r.pol) {
                    (Cls::Mul, _) => av.wrapping_mul(bv),
                    (_, true) => av.wrapping_sub(bv),
                    _ => av.wrapping_add(bv),
                };
                acc.push(mem.access(0, r.dst, Some(limbs(c)), t(2)));
            }
            Cls::Brz => {
                let a = mem.access(0, r.a, None, t(0));
                let z = unlimbs(&a.new) == 0;
                acc.push(a);
                if z == r.pol {
                    npc = r.tgt
                }
            }
            Cls::Ld => {
                let a = mem.access(0, r.a, None, t(0));
                let ea = (unlimbs(&a.new) as u32) as u64 + r.imm;
                acc.push(a);
                let w = mem.access(1, (ea / 4) as u32, None, t(1));
                let v = w.new;
                acc.push(w);
                acc.push(mem.access(0, r.dst, Some([v[0], v[1], 0, 0]), t(2)));
            }
            Cls::St => {
                let a = mem.access(0, r.a, None, t(0));
                let ea = (unlimbs(&a.new) as u32) as u64 + r.imm;
                acc.push(a);
                let v = mem.access(0, r.b, None, t(1));
                let vv = v.new;
                acc.push(v);
                acc.push(mem.access(1, (ea / 4) as u32, Some([vv[0], vv[1], 0, 0]), t(2)));
            }
        }
        steps.push(Step { rpc, ts, u, npc, acc });
        u += r.fee;
        ts += 1;
        rpc = npc;
    }
    Run { steps, mem, final_state: (rpc, ts, u) }
}

// ---------------------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------------------

/// The dominant loop of the measured D3a corpora (§1 of V3-D3A-STUDY: local.get 22 %,
/// i64.const 19.7 %, local.set 13.3 %, br/br_if/add/sub/mul/eqz ≈ 6.4–6.9 % each):
/// `while i != 0 { acc = acc * x + K; i = i - 1 }`, 14 WASM ops per iteration.
pub fn measured_loop(iters: u64) -> Prog {
    use W::*;
    // locals: 0 = i, 1 = acc, 2 = x
    let code = vec![
        /*0*/ LocalGet(0),
        /*1*/ I64Eqz,
        /*2*/ BrIf(14),
        /*3*/ LocalGet(1),
        /*4*/ LocalGet(2),
        /*5*/ I64Mul,
        /*6*/ I64Const(0x9e37_79b9_7f4a_7c15),
        /*7*/ I64Add,
        /*8*/ LocalSet(1),
        /*9*/ LocalGet(0),
        /*10*/ I64Const(1),
        /*11*/ I64Sub,
        /*12*/ LocalSet(0),
        /*13*/ Br(0),
        /*14*/ Halt,
    ];
    Prog {
        name: "measured-mix loop".into(),
        code,
        nlocals: 3,
        locals0: vec![iters, 7, 0x1234_5678_9abc_def1],
        mem0: HashMap::new(),
    }
}

/// Adversarial: unfusable 1-op-per-row pointer chase `p = *(*(*p))…` (`i32.load` chain of
/// length `chain` per iteration, aligned), the costliest self-sustaining op sequence of this
/// spike's subset.
pub fn load_chain(iters: u64, chain: usize) -> Prog {
    use W::*;
    let mut code = vec![LocalGet(0), I64Eqz, BrIf(0) /*patched*/, LocalGet(1)];
    for _ in 0..chain {
        code.push(I32Load(0));
    }
    code.push(LocalSet(1));
    code.extend([LocalGet(0), I64Const(1), I64Sub, LocalSet(0), Br(0)]);
    let halt = code.len();
    code.push(Halt);
    code[2] = BrIf(halt);
    // a pointer cycle over 4096 words with stride 1031 (mod 4096)
    let mut mem0 = HashMap::new();
    for w in 0..4096u32 {
        mem0.insert(w, ((w * 1031 + 17) % 4096) * 4);
    }
    Prog { name: format!("adversarial i32.load chain ({chain}/iter)"), code, nlocals: 2, locals0: vec![iters, 0], mem0 }
}

/// Store/load mix: `mem[p] = acc; acc = acc + mem[p+4]` style (exercises St and Ld fused forms).
pub fn mem_loop(iters: u64) -> Prog {
    use W::*;
    // locals: 0 = i, 1 = p, 2 = v
    let code = vec![
        /*0*/ LocalGet(0),
        /*1*/ I64Eqz,
        /*2*/ BrIf(17),
        /*3*/ LocalGet(1),
        /*4*/ LocalGet(2),
        /*5*/ I32Store(0),
        /*6*/ LocalGet(1),
        /*7*/ I32Load(4),
        /*8*/ LocalSet(2),
        /*9*/ LocalGet(1),
        /*10*/ I64Const(4),
        /*11*/ I64Add,
        /*12*/ LocalSet(1),
        /*13*/ LocalGet(0),
        /*14*/ I64Const(1),
        /*15*/ I64Sub,
        /*16*/ LocalSet(0),
        /*17*/ Halt,
    ];
    // close the loop: replace the last LocalSet with LocalSet; Br(0) by inserting
    let mut c = code[..17].to_vec();
    c.push(Br(0));
    c.push(Halt);
    c[2] = BrIf(18);
    let mut mem0 = HashMap::new();
    for w in 0..(iters as u32 + 2) {
        mem0.insert(w, w.wrapping_mul(2654435761));
    }
    Prog { name: "store/load loop".into(), code: c, nlocals: 3, locals0: vec![iters, 0, 5], mem0 }
}
