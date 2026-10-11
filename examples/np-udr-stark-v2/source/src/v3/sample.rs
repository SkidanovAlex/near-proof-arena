//! Seeded random entry lists for the differential tests of [`super`].
//!
//! Each sampler returns entries satisfying the Lean honest-input predicate of
//! its table (`BndWf`, `AkeyOk`, `HeadOk`, `ValOk`, `UOk`, `WalkOk`), so the
//! rendered trace must also satisfy the table's local constraints
//! (`npudr v3check`).  Sizes are kept small: the Lean cell functions recompute
//! record lists per cell.

use super::*;

/// splitmix64.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9e37_79b9_7f4a_7c15)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    pub fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
    /// A field element, biased towards the edges `0`, `1`, `P − 1`.
    pub fn fe(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => P as u64 - 1,
            _ => self.below(P as u64),
        }
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u64> {
        (0..n).map(|_| self.below(256)).collect()
    }
}

pub fn bnd(r: &mut Rng, n: usize) -> Vec<BndE> {
    (0..n)
        .map(|_| BndE {
            x: r.fe(),
            lo: r.fe(),
            hi: r.fe(),
            hn: r.fe(),
            u: r.fe(),
        })
        .collect()
}

pub fn akey(r: &mut Rng, n: usize) -> Vec<AkeyE> {
    (0..n)
        .map(|_| {
            let mut bytes = r.bytes(9);
            bytes[8] = 1;
            AkeyE {
                vid: r.fe(),
                u: r.fe(),
                bytes,
            }
        })
        .collect()
}

pub fn head(r: &mut Rng, n: usize) -> Vec<HeadE> {
    (0..n.max(1))
        .map(|_| HeadE {
            tau: r.fe(),
            rid: r.fe(),
            rlen: r.fe(),
            rres: r.fe(),
            m_e: r.fe(),
            pre: r.bytes(32),
            post: r.bytes(32),
        })
        .collect()
}

pub fn val(r: &mut Rng, n: usize) -> Vec<ValE> {
    (0..n as u64)
        .map(|vid| {
            let vz = r.below(4) == 0;
            let len = if vz { 0 } else { 1 + r.below(9) };
            ValE {
                vid,
                len,
                vz,
                dup: r.coin(),
                hd: r.coin(),
                rep_e: r.fe(),
                bytes: r.bytes(len as usize),
            }
        })
        .collect()
}

/// Sorted by `(τ, le256 bytes)`, `τ` stepping by `0` or `1`, with repeats.
pub fn uniq(r: &mut Rng, n: usize) -> Vec<UEnt> {
    let mut tau = r.below(3);
    let mut out: Vec<UEnt> = Vec::new();
    for _ in 0..n.max(1) {
        let fresh = out.is_empty() || r.below(4) == 0;
        if !fresh && r.below(3) == 0 {
            tau += 1;
        }
        let bytes = match out.last() {
            Some(p) if p.tau == tau && r.below(4) == 0 => p.bytes.clone(),
            Some(p) if p.tau == tau => {
                // a larger key: bump a random byte, randomize the lower ones
                let mut b = p.bytes.clone();
                let k = r.below(32) as usize;
                if let Some(i) = (k..32).find(|&i| b[i] < 255) {
                    b[i] += 1;
                    for x in b.iter_mut().take(i) {
                        *x = r.below(256);
                    }
                }
                b
            }
            _ => r.bytes(32),
        };
        out.push(UEnt {
            eid: r.fe(),
            tau,
            bytes,
        });
    }
    out
}

fn edge(r: &mut Rng) -> Vec<u64> {
    (0..6).map(|_| r.fe()).collect()
}

/// One walk of `n ≥ 2` steps satisfying `WalkWf3` (`START`, descents, then one of
/// the four endings: `VAL`, absent by key, absent at a branch, or a mode-3 tail).
fn walk1(r: &mut Rng, n: usize) -> WalkR {
    const EK_DOWN: u64 = 0;
    const EK_KEY: u64 = 1;
    const EK_VAL: u64 = 2;
    const EK_LEND: u64 = 3;
    const SYM_END: u64 = 16;
    const SYM_START: u64 = 18;
    let (w, tau) = (r.fe(), r.fe());
    let ending = r.below(5);
    // descents: rows 0 .. d−1 (mode 0, not last)
    let d = match ending {
        0 | 3 | 4 => n - 1,
        _ => n - 2,
    };
    let mut steps: Vec<WStep3> = Vec::new();
    let st = |r: &mut Rng, mode, sym, e: Vec<u64>| WStep3 {
        mode,
        sym,
        e,
        u: r.fe(),
        bm: 0,
        hv: 0,
        ub: r.fe(),
    };
    for i in 0..d {
        let sym = if i == 0 { SYM_START } else { r.below(16) };
        let mut e = edge(r);
        if i == 0 {
            e[1] = tau;
        } else {
            let p: &WStep3 = steps.last().unwrap();
            e[0] = p.e[3];
            e[1] = p.e[4];
        }
        e[2] = sym;
        e[5] = if r.coin() { EK_DOWN } else { EK_KEY };
        steps.push(st(r, 0, sym, e));
    }
    let chained = |r: &mut Rng, steps: &Vec<WStep3>| {
        let mut e = edge(r);
        let p = steps.last().unwrap();
        e[0] = p.e[3];
        e[1] = p.e[4];
        e
    };
    let bm_free = |r: &mut Rng, sym: u64| r.below(1 << 16) & !(1u64 << sym);
    match ending {
        // last row `VAL`
        0 => {
            let mut e = chained(r, &steps);
            e[2] = SYM_END;
            e[5] = EK_VAL;
            steps.push(st(r, 0, SYM_END, e));
        }
        // absent by key / at a branch, then a mode-3 tail row
        1 | 2 => {
            let sym = r.below(16);
            let mut e = chained(r, &steps);
            let mut s = if ending == 1 {
                e[5] = if r.coin() { EK_KEY } else { EK_LEND };
                e[2] = (sym + 1 + r.below(15)) % 16;
                st(r, 1, sym, e)
            } else {
                let p = steps.last_mut().unwrap();
                p.e[4] = 0;
                e[1] = 0;
                st(r, 2, sym, e)
            };
            if ending == 2 {
                s.bm = bm_free(r, sym);
                s.hv = r.below(2);
            }
            steps.push(s);
            let e = edge(r);
            let tail = st(r, 3, SYM_END, e);
            steps.push(tail);
        }
        // last row absent by key
        3 => {
            let mut e = chained(r, &steps);
            e[5] = if r.coin() { EK_KEY } else { EK_LEND };
            e[2] = r.below(16);
            steps.push(st(r, 1, SYM_END, e));
        }
        // last row absent at a branch
        _ => {
            let p = steps.last_mut().unwrap();
            p.e[4] = 0;
            let e = chained(r, &steps);
            let mut s = st(r, 2, SYM_END, e);
            s.bm = r.below(1 << 16);
            steps.push(s);
        }
    }
    WalkR { w, tau, steps }
}

pub fn walk(r: &mut Rng, n: usize) -> Vec<WalkR> {
    (0..n.max(1))
        .map(|_| {
            let len = 3 + r.below(6) as usize;
            walk1(r, len)
        })
        .collect()
}

/// `n` random entries of `table` as JSON.
pub fn sample_json(table: &str, seed: u64, n: usize) -> Result<String, String> {
    let r = &mut Rng::new(seed);
    let j = match table {
        "bnd" => serde_json::to_string(&bnd(r, n)),
        "akey" => serde_json::to_string(&akey(r, n)),
        "head" => serde_json::to_string(&head(r, n)),
        "val" => serde_json::to_string(&val(r, n)),
        "uniq" => serde_json::to_string(&uniq(r, n)),
        "walk" => serde_json::to_string(&walk(r, n)),
        "node" => serde_json::to_string(&node(r, n)),
        t => return Err(format!("unknown table {t}")),
    };
    j.map_err(|e| e.to_string())
}

// ------------------------------------------------------------------- node

use super::node::{Kid, NODE_WIDTH, NodeS3, NodeV3, Slot};

fn slot_ref(r: &mut Rng) -> Slot {
    Slot::Ref {
        lenB: vec![0, 0, 0, 0],
        h: r.bytes(32),
    }
}

fn slot_val(r: &mut Rng) -> Slot {
    Slot::Val {
        lenB: vec![1 + r.below(4) as u64, 0, 0, 0],
        vid: r.fe(),
        vlen: 1 + r.below(20),
        pre: r.bytes(32),
        post: r.bytes(32),
        written: r.coin(),
    }
}

fn kid(r: &mut Rng) -> Kid {
    match r.below(3) {
        0 => Kid::None,
        1 => Kid::Hash { h: r.bytes(32) },
        _ => {
            let mut pre = r.bytes(32);
            let post = if r.coin() { pre.clone() } else { r.bytes(32) };
            if !r.coin() {
                pre = post.clone();
            }
            Kid::Node {
                cid: r.fe(),
                clen: r.fe(),
                cres: r.fe(),
                pre,
                post,
            }
        }
    }
}

/// A random `NodeV3` (not necessarily honest; byte-identity only needs a
/// deterministic function of the entries).
fn nodev(r: &mut Rng) -> NodeV3 {
    match r.below(3) {
        0 => {
            let klen = r.below(6) as usize;
            NodeV3::Leaf {
                key: r.bytes(klen).into_iter().map(|x| x % 16).collect(),
                v: if r.coin() { slot_val(r) } else { slot_ref(r) },
                memB: r.bytes(8),
            }
        }
        1 => {
            let klen = r.below(6) as usize;
            NodeV3::Ext {
                key: r.bytes(klen).into_iter().map(|x| x % 16).collect(),
                kid: if r.coin() {
                    kid(r)
                } else {
                    Kid::Hash { h: r.bytes(32) }
                },
                memB: r.bytes(8),
            }
        }
        _ => {
            let kids: Vec<Kid> = (0..16)
                .map(|_| if r.below(3) == 0 { kid(r) } else { Kid::None })
                .collect();
            NodeV3::Branch {
                v: if r.coin() { Some(slot_val(r)) } else { None },
                kids,
                memB: r.bytes(8),
            }
        }
    }
}

pub fn node(r: &mut Rng, n: usize) -> Vec<NodeS3> {
    (0..n.max(1))
        .map(|i| {
            let v = nodev(r);
            let len = v.ser_len();
            NodeS3 {
                v,
                tau: r.fe(),
                depth: if i == 0 { 0 } else { r.below(6) },
                res: r.fe(),
                uses: r.bytes(4),
                ubm: r.fe(),
                dup: r.coin(),
                hd: r.coin(),
                rep_e: r.fe(),
                ucid: r.bytes(len),
                m_u: r.bytes(len),
            }
        })
        .collect()
}
