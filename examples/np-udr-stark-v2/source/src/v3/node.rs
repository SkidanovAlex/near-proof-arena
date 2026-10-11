//! Honest `nodeV3` trace generator (part 2b), the Rust twin of the Lean aligned
//! generator `ZkFormal.NearV3.Render.NodeGen3.cell` + `nodeTraceAligned`
//! (`Render/PaddedTrie.lean`, `Render/Node/Gen.lean`).
//!
//! Input: the `List NodeS3` entries, deserialized from JSON with the Lean field
//! names (`NodeV3`/`NKid`/`NSlot3` are nested tagged objects); the `F`-level
//! layout is recomputed here from `fieldsOf`/`F.len`.  Output: the trace at the
//! aligned height `padLog22 (logOf (Σ bytes + 1))`, every cell reduced mod `P`.
//! `conformance/run-v2.sh` compares the dumps with `np-lean-render-v3` byte for
//! byte.

use serde::Deserialize;

use crate::field::P;

use super::{Tab, b, get, log_of, pad_log22};

pub const NODE_WIDTH: usize = 186;

const S_TAG: u64 = 14;
const S_HPL: u64 = 15;
const S_HPF: u64 = 16;
const S_KEY: u64 = 17;
const S_VLEN: u64 = 18;
const S_VH: u64 = 19;
const S_BM: u64 = 20;
const S_CH: u64 = 21;
const S_MEM: u64 = 22;
const K_NPRE: u64 = 7;
const K_VPRE: u64 = 9;
const SYM_END: u64 = 16;
const EK_DOWN: u64 = 0;
const EK_KEY: u64 = 1;
const EK_VAL: u64 = 2;
const EK_LEND: u64 = 3;

fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}
fn bit_of(x: u64, b: u64) -> u64 {
    (x >> b) & 1
}
fn le256(xs: &[u64]) -> u64 {
    let mut a: u64 = 0;
    for &x in xs.iter().rev() {
        a = a.wrapping_mul(256).wrapping_add(x);
    }
    a
}

// ---------------------------------------------------------------------------
// JSON mirrors
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub enum Kid {
    #[serde(rename = "none")]
    None,
    #[serde(rename = "hash")]
    Hash { h: Vec<u64> },
    #[serde(rename = "node")]
    Node {
        cid: u64,
        clen: u64,
        cres: u64,
        pre: Vec<u64>,
        post: Vec<u64>,
    },
}

impl Default for Kid {
    fn default() -> Kid {
        Kid::None
    }
}

impl Kid {
    fn bytes(&self, post: bool) -> &[u64] {
        match self {
            Kid::None => &[],
            Kid::Hash { h } => h,
            Kid::Node { pre, post: po, .. } => {
                if post {
                    po
                } else {
                    pre
                }
            }
        }
    }
    fn present(&self) -> bool {
        !matches!(self, Kid::None)
    }
    fn is_node(&self) -> bool {
        matches!(self, Kid::Node { .. })
    }
}

#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub enum Slot {
    #[serde(rename = "ref")]
    Ref { lenB: Vec<u64>, h: Vec<u64> },
    #[serde(rename = "val")]
    Val {
        lenB: Vec<u64>,
        vid: u64,
        vlen: u64,
        pre: Vec<u64>,
        post: Vec<u64>,
        written: bool,
    },
}

impl Slot {
    fn bytes(&self, post: bool) -> Vec<u64> {
        match self {
            Slot::Ref { lenB, h } => {
                let mut v = lenB.clone();
                v.extend_from_slice(h);
                v
            }
            Slot::Val {
                lenB,
                pre,
                post: po,
                ..
            } => {
                let mut v = lenB.clone();
                v.extend_from_slice(if post { po } else { pre });
                v
            }
        }
    }
    fn len_b(&self) -> &[u64] {
        match self {
            Slot::Ref { lenB, .. } => lenB,
            Slot::Val { lenB, .. } => lenB,
        }
    }
    fn h(&self) -> Option<&[u64]> {
        match self {
            Slot::Ref { h, .. } => Some(h),
            Slot::Val { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub enum NodeV3 {
    #[serde(rename = "leaf")]
    Leaf {
        key: Vec<u64>,
        v: Slot,
        memB: Vec<u64>,
    },
    #[serde(rename = "ext")]
    Ext {
        key: Vec<u64>,
        kid: Kid,
        memB: Vec<u64>,
    },
    #[serde(rename = "branch")]
    Branch {
        v: Option<Slot>,
        kids: Vec<Kid>,
        memB: Vec<u64>,
    },
}

impl Default for NodeV3 {
    fn default() -> NodeV3 {
        NodeV3::Branch {
            v: None,
            kids: vec![],
            memB: vec![],
        }
    }
}

impl NodeV3 {
    fn key(&self) -> &[u64] {
        match self {
            NodeV3::Leaf { key, .. } | NodeV3::Ext { key, .. } => key,
            NodeV3::Branch { .. } => &[],
        }
    }
    fn is_le(&self) -> bool {
        !matches!(self, NodeV3::Branch { .. })
    }
    fn is_leaf(&self) -> bool {
        matches!(self, NodeV3::Leaf { .. })
    }
    fn is_ext(&self) -> bool {
        matches!(self, NodeV3::Ext { .. })
    }
    fn kids(&self) -> &[Kid] {
        match self {
            NodeV3::Branch { kids, .. } => kids,
            _ => &[],
        }
    }
    fn slot(&self) -> Option<&Slot> {
        match self {
            NodeV3::Leaf { v, .. } => Some(v),
            NodeV3::Branch { v: Some(s), .. } => Some(s),
            _ => None,
        }
    }
    fn mem(&self) -> &[u64] {
        match self {
            NodeV3::Leaf { memB, .. } | NodeV3::Ext { memB, .. } | NodeV3::Branch { memB, .. } => {
                memB
            }
        }
    }
    fn value(&self) -> Option<(u64, u64, &[u64], &[u64], bool)> {
        let s = match self {
            NodeV3::Leaf {
                v: Slot::Val { .. },
                ..
            } => self.slot(),
            NodeV3::Branch {
                v: Some(Slot::Val { .. }),
                ..
            } => self.slot(),
            _ => None,
        };
        match s {
            Some(Slot::Val {
                vid,
                vlen,
                pre,
                post,
                written,
                ..
            }) => Some((*vid, *vlen, pre, post, *written)),
            _ => None,
        }
    }
    fn revealed(&self) -> Vec<(u64, u64, u64, &[u64], &[u64])> {
        match self {
            NodeV3::Ext {
                kid:
                    Kid::Node {
                        cid,
                        clen,
                        cres,
                        pre,
                        post,
                    },
                ..
            } => {
                vec![(*cid, *clen, *cres, pre, post)]
            }
            NodeV3::Branch { kids, .. } => kids
                .iter()
                .filter_map(|k| match k {
                    Kid::Node {
                        cid,
                        clen,
                        cres,
                        pre,
                        post,
                    } => Some((*cid, *clen, *cres, pre.as_slice(), post.as_slice())),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        }
    }
    pub fn ser_len(&self) -> usize {
        self.ser(false).len()
    }
    fn ser(&self, post: bool) -> Vec<u64> {
        match self {
            NodeV3::Leaf { key, v, memB } => {
                let h = hpn(key, true);
                let mut o = vec![0u64];
                o.extend(u32_bytes(h.len() as u64));
                o.extend(h);
                o.extend(v.bytes(post));
                o.extend(memB);
                o
            }
            NodeV3::Ext { key, kid, memB } => {
                let h = hpn(key, false);
                let mut o = vec![3u64];
                o.extend(u32_bytes(h.len() as u64));
                o.extend(h);
                o.extend_from_slice(kid.bytes(post));
                o.extend(memB);
                o
            }
            NodeV3::Branch { v, kids, memB } => {
                let mut o = match v {
                    None => vec![1u64],
                    Some(s) => {
                        let mut x = vec![2u64];
                        x.extend(s.bytes(post));
                        x
                    }
                };
                let bm = kid_bitmap(kids);
                o.push(bm % 256);
                o.push(bm / 256);
                for k in kids {
                    o.extend_from_slice(k.bytes(post));
                }
                o.extend(memB);
                o
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub struct NodeS3 {
    pub v: NodeV3,
    pub tau: u64,
    pub depth: u64,
    pub res: u64,
    pub uses: Vec<u64>,
    pub ubm: u64,
    pub dup: bool,
    pub hd: bool,
    #[serde(rename = "repE")]
    pub rep_e: u64,
    pub ucid: Vec<u64>,
    #[serde(rename = "mU")]
    pub m_u: Vec<u64>,
}

/// `hpN`: `hexPrefix` as byte naturals.
fn hpn(nibs: &[u64], leaf: bool) -> Vec<u64> {
    let leaf_bit = if leaf { 32u64 } else { 0 };
    let mut out = Vec::new();
    if nibs.len() % 2 == 1 {
        out.push(16 + nibs[0] + leaf_bit);
        pack_nibbles(&nibs[1..], &mut out);
    } else {
        out.push(leaf_bit);
        pack_nibbles(nibs, &mut out);
    }
    out
}
fn pack_nibbles(xs: &[u64], out: &mut Vec<u64>) {
    let mut i = 0;
    while i + 1 < xs.len() {
        out.push(xs[i] * 16 + xs[i + 1]);
        i += 2;
    }
}
fn u32_bytes(n: u64) -> Vec<u64> {
    vec![
        n % 256,
        (n / 256) % 256,
        (n / 65536) % 256,
        (n / 16777216) % 256,
    ]
}
fn kid_bitmap(kids: &[Kid]) -> u64 {
    kids.iter()
        .enumerate()
        .fold(0u64, |a, (j, k)| a | (if k.present() { 1 << j } else { 0 }))
}

// ---------------------------------------------------------------------------
// Field / window
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Field {
    Tag,
    Hpl,
    Hpf,
    Key,
    Vlen,
    Vh,
    Bm,
    Ch,
    Mem,
}

#[derive(Clone, Debug)]
struct Win {
    look: bool,
    cid: u64,
    clen: u64,
    cres: u64,
    w: u64,
    lastw: bool,
    slot: Option<u64>,
    pre: Vec<u64>,
    post: Vec<u64>,
}

#[derive(Clone, Debug)]
enum Fld {
    Plain(Field),
    Ch(Win),
    Vh(Win),
}
impl Fld {
    fn field(&self) -> Field {
        match self {
            Fld::Plain(f) => *f,
            Fld::Ch(_) => Field::Ch,
            Fld::Vh(_) => Field::Vh,
        }
    }
    fn win(&self) -> Option<&Win> {
        match self {
            Fld::Ch(w) | Fld::Vh(w) => Some(w),
            Fld::Plain(_) => None,
        }
    }
    fn chw(&self) -> Option<&Win> {
        match self {
            Fld::Ch(w) => Some(w),
            _ => None,
        }
    }
}
impl Field {
    fn state(self) -> u64 {
        match self {
            Field::Tag => S_TAG,
            Field::Hpl => S_HPL,
            Field::Hpf => S_HPF,
            Field::Key => S_KEY,
            Field::Vlen => S_VLEN,
            Field::Vh => S_VH,
            Field::Bm => S_BM,
            Field::Ch => S_CH,
            Field::Mem => S_MEM,
        }
    }
    fn len(self, hplen: u64) -> u64 {
        match self {
            Field::Tag => 1,
            Field::Hpl => 4,
            Field::Hpf => 1,
            Field::Key => hplen.saturating_sub(1),
            Field::Vlen => 4,
            Field::Vh => 32,
            Field::Bm => 2,
            Field::Ch => 32,
            Field::Mem => 8,
        }
    }
    fn is_nib(self) -> bool {
        matches!(self, Field::Hpf | Field::Key)
    }
}

fn hplen_of(v: &NodeV3) -> u64 {
    if v.is_le() {
        1 + v.key().len() as u64 / 2
    } else {
        0
    }
}
fn odd_of(v: &NodeV3) -> u64 {
    if v.is_le() {
        v.key().len() as u64 % 2
    } else {
        0
    }
}
fn nokey_of(v: &NodeV3) -> u64 {
    b(v.is_le() && hplen_of(v) == 1)
}
fn bmv_of(v: &NodeV3) -> u64 {
    if v.is_le() { 0 } else { kid_bitmap(v.kids()) }
}
fn pop_of(v: &NodeV3) -> u64 {
    let bm = bmv_of(v);
    (0..16).map(|i| bit_of(bm, i)).sum()
}
fn nochild_of(v: &NodeV3) -> u64 {
    b(!v.is_le() && pop_of(v) == 0)
}
fn type_of(v: &NodeV3) -> (u64, u64, u64, u64) {
    match v {
        NodeV3::Leaf { .. } => (1, 0, 0, 0),
        NodeV3::Ext { .. } => (0, 1, 0, 0),
        NodeV3::Branch { v: None, .. } => (0, 0, 1, 0),
        NodeV3::Branch { v: Some(_), .. } => (0, 0, 0, 1),
    }
}
fn tv_of(v: &NodeV3) -> bool {
    v.value().is_some()
}
fn vid_of(v: &NodeV3) -> u64 {
    v.value().map(|x| x.0).unwrap_or(0)
}
fn vlen_of(v: &NodeV3) -> u64 {
    v.value().map(|x| x.1).unwrap_or(0)
}
fn tw_of(v: &NodeV3) -> bool {
    v.value().map(|x| x.4).unwrap_or(false)
}
fn s_of(v: &NodeV3) -> u64 {
    v.key().len() as u64
}
fn xrv_of(v: &NodeV3) -> bool {
    matches!(
        v,
        NodeV3::Ext {
            kid: Kid::Node { .. },
            ..
        }
    )
}
fn xres_of(v: &NodeV3) -> u64 {
    match v {
        NodeV3::Ext {
            kid: Kid::Node { cres, .. },
            ..
        } => *cres,
        _ => 0,
    }
}
fn xdead_of(v: &NodeV3) -> bool {
    v.is_ext() && !xrv_of(v)
}
fn xlast0_of(v: &NodeV3) -> bool {
    v.is_ext() && nokey_of(v) == 1
}
fn eext_of(v: &NodeV3) -> bool {
    v.is_ext() && nokey_of(v) == 1 && odd_of(v) == 0
}
fn xtgt_of(n: u64, v: &NodeV3) -> u64 {
    if xrv_of(v) {
        xres_of(v)
    } else if xdead_of(v) {
        n
    } else {
        0
    }
}
fn xtgj_of(v: &NodeV3) -> u64 {
    if xdead_of(v) { s_of(v) } else { 0 }
}

fn kid_win(kid: &Kid, w: u64, lastw: bool, slot: Option<u64>) -> Win {
    match kid {
        Kid::Node {
            cid,
            clen,
            cres,
            pre,
            post,
        } => Win {
            look: true,
            cid: *cid,
            clen: *clen,
            cres: *cres,
            w,
            lastw,
            slot,
            pre: pre.clone(),
            post: post.clone(),
        },
        Kid::Hash { h } => Win {
            look: false,
            cid: 0,
            clen: 0,
            cres: 0,
            w,
            lastw,
            slot,
            pre: h.clone(),
            post: h.clone(),
        },
        Kid::None => Win {
            look: false,
            cid: 0,
            clen: 0,
            cres: 0,
            w,
            lastw,
            slot,
            pre: vec![],
            post: vec![],
        },
    }
}
fn val_win(s: &Slot) -> Win {
    match s {
        Slot::Ref { h, .. } => Win {
            look: false,
            cid: 0,
            clen: 0,
            cres: 0,
            w: 0,
            lastw: false,
            slot: None,
            pre: h.clone(),
            post: h.clone(),
        },
        Slot::Val { pre, post, .. } => Win {
            look: true,
            cid: 0,
            clen: 0,
            cres: 0,
            w: 0,
            lastw: false,
            slot: None,
            pre: pre.clone(),
            post: post.clone(),
        },
    }
}
fn branch_wins(kids: &[Kid]) -> Vec<Fld> {
    // Lean: `present := (kids.zip (range kids.length)).filter (k ≠ none)`, then
    // `((k, origIdx), w).map (fun ... => .ch (kidWin k w last (some origIdx)))`:
    // `slot` is the *original* kid index, `w` the present-order index.
    let present: Vec<(usize, &Kid)> = kids
        .iter()
        .enumerate()
        .filter(|(_, k)| k.present())
        .collect();
    let last = present.len();
    present
        .iter()
        .enumerate()
        .map(|(w, (orig, k))| Fld::Ch(kid_win(k, w as u64, w + 1 == last, Some(*orig as u64))))
        .collect()
}
fn fields_of(v: &NodeV3) -> Vec<Fld> {
    match v {
        NodeV3::Leaf { v: s, .. } => vec![
            Fld::Plain(Field::Tag),
            Fld::Plain(Field::Hpl),
            Fld::Plain(Field::Hpf),
            Fld::Plain(Field::Key),
            Fld::Plain(Field::Vlen),
            Fld::Vh(val_win(s)),
            Fld::Plain(Field::Mem),
        ],
        NodeV3::Ext { kid, .. } => vec![
            Fld::Plain(Field::Tag),
            Fld::Plain(Field::Hpl),
            Fld::Plain(Field::Hpf),
            Fld::Plain(Field::Key),
            Fld::Ch(kid_win(kid, 0, true, None)),
            Fld::Plain(Field::Mem),
        ],
        NodeV3::Branch { v: None, kids, .. } => {
            let mut o = vec![Fld::Plain(Field::Tag), Fld::Plain(Field::Bm)];
            o.extend(branch_wins(kids));
            o.push(Fld::Plain(Field::Mem));
            o
        }
        NodeV3::Branch {
            v: Some(s), kids, ..
        } => {
            let mut o = vec![
                Fld::Plain(Field::Tag),
                Fld::Plain(Field::Vlen),
                Fld::Vh(val_win(s)),
                Fld::Plain(Field::Bm),
            ];
            o.extend(branch_wins(kids));
            o.push(Fld::Plain(Field::Mem));
            o
        }
    }
}

/// `layout (fieldsOf v) hplen`: `(field-at-byte, index-in-field)` per byte.
fn layout_of(v: &NodeV3) -> Vec<(Fld, u64)> {
    let hplen = hplen_of(v);
    let mut o = Vec::new();
    for f in fields_of(v) {
        for i in 0..f.field().len(hplen) {
            o.push((f.clone(), i));
        }
    }
    o
}
fn rec(vs: &[NodeS3], n: usize) -> &NodeS3 {
    &vs[n.min(vs.len().saturating_sub(1))]
}
fn sz_before(vs: &[NodeS3], n: usize) -> u64 {
    (0..n)
        .map(|m| {
            if vs[m].dup {
                0
            } else {
                vs[m].v.ser(false).len() as u64
            }
        })
        .sum()
}
fn rev_below(kids: &[Kid], j: usize) -> u64 {
    kids.iter().take(j).filter(|k| k.is_node()).count() as u64
}
fn use_count(s: &NodeS3, i: u64) -> u64 {
    s.uses.get(i as usize).copied().unwrap_or(0)
}

/// `edgeAOf`: `(edge, use-index)`.
fn edge_a(vs: &[NodeS3], n: u64, fld: &Fld, idx: u64, bbyte: u64) -> Option<(Vec<u64>, u64)> {
    let f = fld.field();
    let v = &vs[n as usize].v;
    let odd = odd_of(v);
    let ki = 2 * idx + odd;
    match f {
        Field::Key => Some((vec![n, ki, bbyte / 16, n, ki + 1, EK_KEY], ki)),
        Field::Hpf => {
            if odd == 1 {
                Some((
                    if xlast0_of(v) {
                        vec![n, 0, bbyte % 16, xtgt_of(n, v), xtgj_of(v), EK_KEY]
                    } else {
                        vec![n, 0, bbyte % 16, n, 1, EK_KEY]
                    },
                    0,
                ))
            } else {
                None
            }
        }
        Field::Ch => match fld.chw() {
            Some(w) if idx == 0 && w.look && !v.is_le() => Some((
                vec![n, 0, w.slot.unwrap_or(0), w.cres, 0, EK_DOWN],
                rev_below(v.kids(), w.slot.unwrap_or(0) as usize),
            )),
            _ => None,
        },
        Field::Vh => {
            if idx == 0 && tv_of(v) {
                let j = if v.is_leaf() {
                    s_of(v)
                } else {
                    v.revealed().len() as u64
                };
                Some((
                    vec![n, type_of(v).0 * s_of(v), SYM_END, vid_of(v), 0, EK_VAL],
                    j,
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn edge_b(vs: &[NodeS3], n: u64, fld: &Fld, idx: u64, bbyte: u64) -> Option<(Vec<u64>, u64)> {
    let f = fld.field();
    let v = &vs[n as usize].v;
    let odd = odd_of(v);
    let ki = 2 * idx + odd;
    match f {
        Field::Key => {
            if idx + 1 == Field::Key.len(hplen_of(v)) && v.is_ext() {
                Some((
                    vec![n, ki + 1, bbyte % 16, xtgt_of(n, v), xtgj_of(v), EK_KEY],
                    ki + 1,
                ))
            } else {
                Some((vec![n, ki + 1, bbyte % 16, n, ki + 2, EK_KEY], ki + 1))
            }
        }
        Field::Mem => {
            if idx == 0 && v.is_leaf() {
                Some((
                    vec![n, s_of(v), SYM_END, n, s_of(v), EK_LEND],
                    s_of(v) + b(tv_of(v)),
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `NodeGen3.rowCell(vs, ⟨n, p, f, idx, bbyte, pb⟩)`.
fn row_cell(
    vs: &[NodeS3],
    n: u64,
    p: u64,
    fld_in: &Fld,
    idx: u64,
    bbyte: u64,
    pb: u64,
) -> Vec<u64> {
    let f = fld_in.field();
    let s = &vs[n as usize];
    let v = &s.v;
    let len = v.ser(false).len() as u64;
    let hplen = hplen_of(v);
    let d = s.depth + 112;
    let bm = bmv_of(v);
    let win = fld_in.win().cloned();
    let chw = fld_in.chw().cloned();
    let ty = type_of(v);
    let mut c = vec![0u64; NODE_WIDTH];
    c[0] = 1;
    c[1] = b(p == 0);
    c[2] = b(p + 1 == len);
    c[4] = n;
    c[5] = p;
    c[6] = len;
    c[7] = s.depth;
    c[8] = bbyte;
    c[9] = pb;
    c[10] = ty.0;
    c[11] = ty.1;
    c[12] = ty.2;
    c[13] = ty.3;
    c[23] = idx;
    c[24] = b(idx == 0);
    c[25] = b(idx + 1 == f.len(hplen));
    c[26] = hplen;
    c[27] = odd_of(v);
    c[28] = nokey_of(v);
    for cc in 14..23usize {
        c[cc] = b(f.state() == cc as u64);
    }
    let nib_or15 = f.is_nib() || f.state() == 15;
    for k in 0..4usize {
        if nib_or15 {
            c[29 + k] = bit_of(bbyte / 16, k as u64);
            c[33 + k] = bit_of(bbyte % 16, k as u64);
        } else if f == Field::Tag {
            c[29 + k] = bit_of(d, k as u64);
            c[33 + k] = bit_of(d, (k + 4) as u64);
        }
    }
    for k in 0..16usize {
        c[37 + k] = bit_of(bm, k as u64);
    }
    c[53] = nochild_of(v);
    if let Some(w) = &chw {
        for k in 0..16usize {
            c[54 + k] = b(w.slot == Some(k as u64));
        }
        c[70] = w.w;
        c[71] = b(w.lastw);
    }
    if let Some(w) = &win {
        for m in 0..32usize {
            c[72 + m] = *w.pre.get(idx as usize + m).unwrap_or(&0);
            c[104 + m] = *w.post.get(idx as usize + m).unwrap_or(&0);
        }
    }
    c[136] = chw.as_ref().map(|w| b(w.look)).unwrap_or(0);
    c[137] = chw.as_ref().map(|w| w.cid).unwrap_or(0);
    c[138] = chw.as_ref().map(|w| w.clen).unwrap_or(0);
    c[139] = b(tv_of(v));
    let dig = match f {
        Field::Ch => chw.as_ref().and_then(|w| {
            if idx == 0 && w.look {
                Some((msg_id(K_NPRE, w.cid), w.clen, true))
            } else {
                None
            }
        }),
        Field::Vh => {
            if idx == 0 && tv_of(v) {
                Some((msg_id(K_VPRE, vid_of(v)), vlen_of(v), false))
            } else {
                None
            }
        }
        _ => None,
    };
    if let Some((di, dl, _)) = dig {
        c[140] = di;
        c[141] = dl;
        c[142] = 1;
    }
    c[143] = matches!(dig, Some((_, _, true))) as u64;
    c[144] = b(p == 0 && s.dup);
    let ea = edge_a(vs, n, fld_in, idx, bbyte);
    let eb = edge_b(vs, n, fld_in, idx, bbyte);
    if let Some((e, u)) = &ea {
        c[145] = 1;
        for j in 0..5usize {
            c[146 + j] = *e.get(j + 1).unwrap_or(&0);
        }
        c[150] = use_count(s, *u);
    }
    if let Some((_, u)) = &eb {
        c[151] = use_count(s, *u);
    }
    c[152] = sz_before(vs, n as usize) + if s.dup { 0 } else { p };
    c[153] = s.res;
    c[154] = chw.as_ref().map(|w| w.cres).unwrap_or(0);
    c[155] = xres_of(v);
    c[156] = b(xrv_of(v));
    c[157] = b(xdead_of(v));
    c[158] = b(xlast0_of(v));
    c[159] = b(eext_of(v));
    if let Some((e, _)) = &eb {
        c[160] = 1;
        c[161] = *e.get(3).unwrap_or(&0);
        c[162] = *e.get(4).unwrap_or(&0);
    }
    c[163] = s.tau;
    c[164] = if f == Field::Tag { bit_of(d, 8) } else { 0 };
    c[165] = vid_of(v);
    c[166] = vlen_of(v);
    c[167] = b(tw_of(v));
    if f.state() == 15 {
        let t = u32_bytes(hplen);
        c[168] = le256(&t[..(idx as usize + 1).min(t.len())]);
    } else if f == Field::Vlen {
        let lb = v.slot().map(|s| s.len_b().to_vec()).unwrap_or_default();
        c[168] = le256(&lb[..(idx as usize + 1).min(lb.len())]);
    }
    if f == Field::Vlen || f.state() == 15 {
        c[169] = 256u64.wrapping_pow(idx as u32);
    }
    c[170] = b(s.dup);
    c[171] = b(s.hd);
    c[172] = s.rep_e;
    if f == Field::Bm && idx == 0 {
        c[173] = s.ubm;
    }
    if let Some((e, _)) = &ea {
        c[174] = *e.get(5).unwrap_or(&0);
    }
    if let Some((e, _)) = &eb {
        c[175] = *e.get(5).unwrap_or(&0);
        c[176] = *e.get(1).unwrap_or(&0);
        c[177] = *e.get(2).unwrap_or(&0);
    }
    c[178] = b(v.is_leaf() && f == Field::Mem && idx == 0);
    c[179] = xtgt_of(n, v);
    c[180] = xtgj_of(v);
    c[181] = b(
        (f == Field::Ch && chw.as_ref().map(|w| w.look).unwrap_or(false))
            || (f == Field::Vh && tv_of(v)),
    );
    c[182] = match f {
        Field::Ch => msg_id(K_NPRE, chw.as_ref().map(|w| w.cid).unwrap_or(0)),
        Field::Vh => msg_id(K_VPRE, vid_of(v)),
        _ => 0,
    };
    c[183] = matches!(dig, Some((_, _, true))) as u64
        + if matches!(dig, Some((_, _, false))) {
            b(tw_of(v))
        } else {
            0
        };
    c[184] = b(f == Field::Bm && idx == 0);
    c[185] = s.m_u.get(p as usize).copied().unwrap_or(0);
    for x in c.iter_mut() {
        *x %= P as u64;
    }
    c
}

/// Build the honest `nodeV3` trace.
pub fn node_aligned(vs: &[NodeS3]) -> Tab {
    let recs: Vec<(usize, usize)> = (0..vs.len())
        .flat_map(|n| (0..layout_of(&vs[n].v).len()).map(move |p| (n, p)))
        .collect();
    // `nodeTraceAligned`: height from Σ (ser false).length (all records) + 1.
    let r = recs.len() as u64;
    let total = sz_before(vs, vs.len());
    let nbytes: usize = vs.iter().map(|s| s.v.ser(false).len()).sum();
    let log = pad_log22(log_of(nbytes + 1));
    let mut t = Tab::zero(log, NODE_WIDTH);
    let h = t.height();
    let mut q = 0usize;
    for (n, p) in &recs {
        if q >= h {
            break;
        }
        let v = &vs[*n].v;
        let lay = layout_of(v);
        let (fld, idx) = lay[*p].clone();
        let pre = v.ser(false);
        let post = v.ser(true);
        let bb = *pre.get(*p).unwrap_or(&0);
        let pb = *post.get(*p).unwrap_or(&0);
        let cells = row_cell(vs, *n as u64, *p as u64, &fld, idx, bb, pb);
        for (cc, x) in cells.into_iter().enumerate().take(NODE_WIDTH) {
            t.set(q, cc, x);
        }
        q += 1;
    }
    if q < h {
        for cc in 0..NODE_WIDTH {
            let x = if cc == 3 {
                1
            } else if cc == 152 {
                total
            } else {
                0
            };
            t.set(q, cc, x);
        }
        q += 1;
    }
    while q < h {
        if total != 0 {
            t.set(q, 152, total);
        }
        q += 1;
    }
    t
}

// keep `get`, `rec` referenced (used by future extensions)
#[allow(dead_code)]
fn _unused(vs: &[NodeS3]) {
    let _ = rec(vs, 0);
    let _ = get(&[0u64], 0);
}
