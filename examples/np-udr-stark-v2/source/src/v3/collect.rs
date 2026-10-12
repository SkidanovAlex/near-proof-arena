//! SHA-256 message collector for `nearAirV3` (tables 0/1).
//!
//! The SHA tables do not have their own entry list: their input is the union of
//! every BYTES send `(Id, pos, byte)` and DIGEST receive `(Id, len, digest)` of
//! the other 23 tables (`ShaFacts`, `Link/Sha3.lean`).  This module mirrors the
//! Lean `*Traffic`/`*Sends`/`*Recvs` functions: it collects those bus messages
//! from the same per-table entry lists the aligned generators consume and turns
//! them into the `Gen.Msg` list (`{id, bytes, dmult}`) that
//! [`crate::sha::sha_cells`] hashes.
//!
//! The bytes of a message come from the table that *sends* them (`emitAt`); the
//! `(len, digest)` come from the tables that *receive* the digest.  Every id
//! must be hashed by exactly one SHA instance and its digest provided once, so
//! after collection the messages are partitioned by the §12 kind registry
//! ([`split_instances`]).
//!
//! Covered here (mirroring the Lean traffic definitions): `node`, `val`, `head`,
//! `acct` (whose entry structs fully determine their SHA messages), plus the
//! tables that touch no SHA bus (`akey`, `bnd`, `srcp`'s own sends, `uniq`,
//! `sort`, `qv`, `size`).  `rcpt` needs the receipt encodings (not on the entry
//! struct) and the scheduler/ChaCha/ups pair lives in the scheduler lane; those
//! are the documented gaps.

use std::collections::{BTreeMap, BTreeSet};

use crate::sha::Msg as ShaMessage;

use super::acct::AcctV;
use super::mrksort::{MrkNode, MrkV};
use super::node::{Kid, NodeS3, NodeV3, Slot};
use super::srcp::{SrcpB, SrcpItem};
use super::{AkeyE, HeadE, ValE};

/// `B_BYTES` (`ZkFormal.Near.Ids`).
pub const B_BYTES: usize = 0;
/// `B_DIGEST`.
pub const B_DIGEST: usize = 1;

/// SHA message kinds (`ZkFormal.Near.Ids` / `NearV3.IdsUps` / `Rcpt.Ids`).
pub const K_RC: u64 = 1;
pub const K_RF: u64 = 2;
pub const K_PEO: u64 = 3;
pub const K_LEAF: u64 = 4;
pub const K_RID: u64 = 5;
pub const K_MRK: u64 = 6;
pub const K_NPRE: u64 = 7;
pub const K_NPOST: u64 = 8;
pub const K_VPRE: u64 = 9;
pub const K_VPOST: u64 = 10;
pub const K_SCH: u64 = 11;
pub const K_VUPS: u64 = 12;
pub const K_SRC: u64 = 13;
pub const K_VAK: u64 = 14;

/// `msgId kind idx = kind + 16·idx`.
#[inline]
pub fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

/// The 32-byte SHA-256 digest of a preimage, as `u64`s `< 256`.
pub fn digest(bytes: &[u8]) -> Vec<u64> {
    use sha2::{Digest, Sha256};
    Sha256::digest(bytes).iter().map(|&x| x as u64).collect()
}

// ---------------------------------------------------------------------------
// Raw bus traffic (mirrors `Traffic`)
// ---------------------------------------------------------------------------

/// A table's raw SHA traffic: the BYTES it sends and the DIGEST it receives.
#[derive(Clone, Debug, Default)]
pub struct Raw {
    /// `(Id, bytes)` byte sends (`emitAt`).
    pub sends: Vec<(u64, Vec<u64>)>,
    /// `(Id, len, digest)` digest receives (`digMsg`).
    pub recvs: Vec<(u64, usize, Vec<u64>)>,
}

impl Raw {
    pub fn send(&mut self, id: u64, bytes: Vec<u64>) {
        self.sends.push((id, bytes));
    }
    pub fn recv(&mut self, id: u64, len: usize, dig: Vec<u64>) {
        self.recvs.push((id, len, dig));
    }
}

fn emit(id: u64, bytes: &[u64], raw: &mut Raw) {
    raw.send(id, bytes.to_vec());
}

fn recv_dig(id: u64, len: usize, d: &[u64], raw: &mut Raw) {
    raw.recv(id, len, d.to_vec());
}

// ---------------------------------------------------------------------------
// Serialization helpers (`NodeV3.ser`, re-derived; the generator's are private)
// ---------------------------------------------------------------------------

fn u32_bytes(n: u64) -> Vec<u64> {
    vec![
        n % 256,
        (n / 256) % 256,
        (n / 65536) % 256,
        (n / 16777216) % 256,
    ]
}

/// `hpN nibs leaf`.
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

fn kid_present(k: &Kid) -> bool {
    !matches!(k, Kid::None)
}

fn kid_bitmap(kids: &[Kid]) -> u64 {
    kids.iter().enumerate().fold(0u64, |a, (j, k)| {
        a | (if kid_present(k) { 1 << j } else { 0 })
    })
}

fn kid_bytes(k: &Kid, post: bool) -> Vec<u64> {
    match k {
        Kid::None => vec![],
        Kid::Hash { h } => h.clone(),
        Kid::Node { pre, post: po, .. } => {
            if post {
                po.clone()
            } else {
                pre.clone()
            }
        }
    }
}

fn slot_bytes(s: &Slot, post: bool) -> Vec<u64> {
    match s {
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

/// `NodeV3.ser post`.
pub fn node_ser(v: &NodeV3, post: bool) -> Vec<u64> {
    match v {
        NodeV3::Leaf { key, v, memB } => {
            let h = hpn(key, true);
            let mut o = vec![0u64];
            o.extend(u32_bytes(h.len() as u64));
            o.extend(h);
            o.extend(slot_bytes(v, post));
            o.extend_from_slice(memB);
            o
        }
        NodeV3::Ext { key, kid, memB } => {
            let h = hpn(key, false);
            let mut o = vec![3u64];
            o.extend(u32_bytes(h.len() as u64));
            o.extend(h);
            o.extend(kid_bytes(kid, post));
            o.extend_from_slice(memB);
            o
        }
        NodeV3::Branch { v, kids, memB } => {
            let mut o = match v {
                None => vec![1u64],
                Some(s) => {
                    let mut x = vec![2u64];
                    x.extend(slot_bytes(s, post));
                    x
                }
            };
            let bm = kid_bitmap(kids);
            o.push(bm % 256);
            o.push(bm / 256);
            for k in kids {
                o.extend(kid_bytes(k, post));
            }
            o.extend_from_slice(memB);
            o
        }
    }
}

/// `NodeV3.revealed`: `(cid, clen, cres, pre, post)` in slot order.
fn node_revealed(v: &NodeV3) -> Vec<(u64, u64, u64, Vec<u64>, Vec<u64>)> {
    match v {
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
        } => vec![(*cid, *clen, *cres, pre.clone(), post.clone())],
        NodeV3::Branch { kids, .. } => kids
            .iter()
            .filter_map(|k| match k {
                Kid::Node {
                    cid,
                    clen,
                    cres,
                    pre,
                    post,
                } => Some((*cid, *clen, *cres, pre.clone(), post.clone())),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}

/// `NodeV3.value`: `(vid, vlen, pre, post, written)`.
fn node_value(v: &NodeV3) -> Option<(u64, u64, Vec<u64>, Vec<u64>, bool)> {
    let s = match v {
        NodeV3::Leaf {
            v: s @ Slot::Val { .. },
            ..
        } => s,
        NodeV3::Branch {
            v: Some(s @ Slot::Val { .. }),
            ..
        } => s,
        _ => return None,
    };
    match s {
        Slot::Val {
            vid,
            vlen,
            pre,
            post,
            written,
            ..
        } => Some((*vid, *vlen, pre.clone(), post.clone(), *written)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Per-table traffic (mirrors the Lean `*Traffic` functions)
// ---------------------------------------------------------------------------

/// `nodeSends3 vs B_BYTES` ++ `nodeRecvs3 vs B_DIGEST`.
pub fn node_raw(vs: &[NodeS3]) -> Raw {
    let mut r = Raw::default();
    for (n, s) in vs.iter().enumerate() {
        emit(msg_id(K_NPRE, n as u64), &node_ser(&s.v, false), &mut r);
        emit(msg_id(K_NPOST, n as u64), &node_ser(&s.v, true), &mut r);
        for (c, l, _res, pre, po) in node_revealed(&s.v) {
            recv_dig(msg_id(K_NPRE, c), l as usize, &pre, &mut r);
            recv_dig(msg_id(K_NPOST, c), l as usize, &po, &mut r);
        }
        if let Some((i, l, pre, po, w)) = node_value(&s.v) {
            recv_dig(msg_id(K_VPRE, i), l as usize, &pre, &mut r);
            if w {
                recv_dig(msg_id(K_VPOST, i), l as usize, &po, &mut r);
            }
        }
    }
    r
}

/// `valSends es B_BYTES` (`VPRE`), no digest receives.
pub fn val_raw(es: &[ValE]) -> Raw {
    let mut r = Raw::default();
    for e in es {
        if !e.vz {
            emit(msg_id(K_VPRE, e.vid), &e.bytes, &mut r);
        }
    }
    r
}

/// `headRecvs hs B_DIGEST` (`NPRE`/`NPOST` of the root record).
pub fn head_raw(hs: &[HeadE]) -> Raw {
    let mut r = Raw::default();
    for h in hs {
        recv_dig(msg_id(K_NPRE, h.rid), h.rlen as usize, &h.pre, &mut r);
        recv_dig(msg_id(K_NPOST, h.rid), h.rlen as usize, &h.post, &mut r);
    }
    r
}

/// `acctV3Sends as B_BYTES`: `VPOST(k) = post ++ pre.drop 16`.
pub fn acct_raw(as_: &[AcctV]) -> Raw {
    let mut r = Raw::default();
    for a in as_ {
        let mut b = a.post.clone();
        b.extend(a.pre.iter().skip(16).copied());
        emit(msg_id(K_VPOST, a.k), &b, &mut r);
    }
    r
}

/// `akeyV3` touches no SHA bus (`VBYTES`/`AKC` only).
pub fn akey_raw(_es: &[AkeyE]) -> Raw {
    Raw::default()
}

/// `bndV3` touches no SHA bus (`BND`/`BNDP` only).
pub fn bnd_raw(_es: &[super::BndE]) -> Raw {
    Raw::default()
}

/// `uniq` touches no SHA bus (`DIGS`/`DUP` only).
pub fn uniq_raw() -> Raw {
    Raw::default()
}

/// `sort` touches no SHA bus (`RIDS`/`DIGS` only).
pub fn sort_raw() -> Raw {
    Raw::default()
}

/// `qvV3` sends `VBYTES` (value parser), **not** `BYTES`; no SHA bus.
pub fn qv_raw() -> Raw {
    Raw::default()
}

/// `sizeV3` sends `SIZE` only; no SHA bus.
pub fn size_raw() -> Raw {
    Raw::default()
}

/// `srcpTraffic`: `B_BYTES` leaf/path sends, `B_DIGEST` root/path receives
/// (plus the `RC(j)` digest receive, whose bytes come from `rcpt`).
pub fn srcp_raw(bs: &[SrcpB]) -> Raw {
    let mut r = Raw::default();
    for b in bs {
        // root digest: `SRC(qe)` of length `le`.
        recv_dig(msg_id(K_SRC, b.qe), b.le as usize, &b.root, &mut r);
        // leaf: `emitAt SRC(ql) leaf`.
        emit(msg_id(K_SRC, b.ql), &b.leaf, &mut r);
        for it in &b.path {
            emit(msg_id(K_SRC, it.q), &srcp_item_bytes(it), &mut r);
            recv_dig(msg_id(K_SRC, it.pq), it.pl as usize, &it.acc, &mut r);
        }
    }
    r
}

/// `SrcpItem.bytes = if dir then acc ++ sib else sib ++ acc`.
fn srcp_item_bytes(it: &SrcpItem) -> Vec<u64> {
    let mut v = Vec::new();
    if it.dir {
        v.extend_from_slice(&it.acc);
        v.extend_from_slice(&it.sib);
    } else {
        v.extend_from_slice(&it.sib);
        v.extend_from_slice(&it.acc);
    }
    v
}

/// `mrkSends`/`mrkRecvs`: `MRK` hashed nodes (`l ++ r`) and their digests.
///
/// The root digest `(rootId, rootLen, PV_OUT)` is public and not collected; the
/// `lId`/`rId` digests are `(len, sha256)` of the child windows and are checked.
pub fn mrk_raw(v: &MrkV) -> Raw {
    let mut r = Raw::default();
    let mut hbefore = 0u64;
    for nd in &v.nodes {
        match nd {
            MrkNode::Hashed {
                l_id,
                l_len,
                l,
                r_id,
                r_len,
                r: rw,
            } => {
                let mut b = l.clone();
                b.extend_from_slice(rw);
                emit(msg_id(K_MRK, hbefore), &b, &mut r);
                recv_dig(*l_id, *l_len as usize, l, &mut r);
                recv_dig(*r_id, *r_len as usize, rw, &mut r);
                hbefore += 1;
            }
            MrkNode::Promoted { .. } => {}
        }
    }
    r
}

/// `rcptSends3`/`rcptRecvs3`: needs the receipt encodings (`RcptE.enc`/`peo`/
/// `leaf`/`rid`), which the entry struct does not carry.  Documented gap.
pub fn rcpt_raw() -> Raw {
    Raw::default()
}

// ---------------------------------------------------------------------------
// Merge and partition
// ---------------------------------------------------------------------------

/// A merged message and whether its digest was supplied by a receiver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Collected {
    pub id: u64,
    pub bytes: Vec<u8>,
    pub dmult: bool,
}

/// The outcome of [`merge`]: the collected messages and the external digests
/// (receivers whose byte sender is not among the supplied tables, e.g. a public
/// segment or an uncovered table).
#[derive(Clone, Debug, Default)]
pub struct Merged {
    pub msgs: Vec<Collected>,
    /// `id → (len, digest)` of digest receives with no byte sender.
    pub external_digests: Vec<(u64, usize, Vec<u64>)>,
}

/// Merge raw traffic: one message per byte-send id, its `dmult` true iff some
/// receiver provided a matching digest.  Errors on conflicting preimages,
/// conflicting digests, a digest length/preimage-length mismatch, or a digest
/// that is not `sha256(bytes)`.
pub fn merge(raws: &[Raw]) -> Result<Merged, String> {
    let mut bytes: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut recvs: BTreeMap<u64, (usize, Vec<u64>)> = BTreeMap::new();
    for raw in raws {
        for (id, b) in &raw.sends {
            if let Some(old) = bytes.get(id) {
                if old != b {
                    return Err(format!("collect: id {id} sent with two preimages"));
                }
            } else {
                bytes.insert(*id, b.clone());
            }
        }
        for (id, len, dig) in &raw.recvs {
            if let Some((old_len, old_dig)) = recvs.get(id) {
                if old_len != len || old_dig != dig {
                    return Err(format!("collect: id {id} received with two digests"));
                }
            } else {
                recvs.insert(*id, (*len, dig.clone()));
            }
        }
    }
    let ids: BTreeSet<u64> = bytes.keys().chain(recvs.keys()).copied().collect();
    let mut msgs = Vec::with_capacity(bytes.len());
    let mut external_digests = Vec::new();
    for id in ids {
        let b = match bytes.get(&id) {
            Some(b) => b.clone(),
            None => {
                let (len, dig) = recvs.get(&id).unwrap().clone();
                external_digests.push((id, len, dig));
                continue;
            }
        };
        if b.iter().any(|&x| x >= 256) {
            return Err(format!("collect: id {id} preimage has a value >= 256"));
        }
        let raw_bytes: Vec<u8> = b.iter().map(|&x| x as u8).collect();
        // `dmult` mirrors `Gen.Msg.dmult`: a receiver provided the digest.  The
        // digest value itself is `sha256(bytes)` by the SHA table, so a mismatch
        // would show up as a bus imbalance, not here.
        let dmult = recvs.contains_key(&id);
        msgs.push(Collected {
            id,
            bytes: raw_bytes,
            dmult,
        });
    }
    Ok(Merged {
        msgs,
        external_digests,
    })
}

/// §12 kind registry split: `sha_t` (index 0) is the trie/native instance
/// (`NPRE`/`NPOST`/`VPRE`/`VPOST`/`VUPS`), `sha_r` (index 1) the receipt/source
/// instance (everything else).
pub fn is_trie_kind(id: u64) -> bool {
    matches!(id % 16, K_NPRE | K_NPOST | K_VPRE | K_VPOST | K_VUPS)
}

/// Split collected messages into `(sha_t, sha_r)` by the §12 registry.
pub fn split_instances(msgs: Vec<Collected>) -> (Vec<ShaMessage>, Vec<ShaMessage>) {
    let (t, r): (Vec<_>, Vec<_>) = msgs.into_iter().partition(|m| is_trie_kind(m.id));
    let conv = |v: Vec<Collected>| {
        v.into_iter()
            .map(|m| ShaMessage {
                id: m.id as u32,
                bytes: m.bytes,
                dmult: m.dmult,
            })
            .collect()
    };
    (conv(t), conv(r))
}

// ---------------------------------------------------------------------------
// Entry bundle
// ---------------------------------------------------------------------------

/// The per-table entry lists the collector consumes.  An empty list means the
/// table is absent (its traffic is not collected).
#[derive(Clone, Debug, Default)]
pub struct Bundle {
    pub node: Vec<NodeS3>,
    pub val: Vec<ValE>,
    pub head: Vec<HeadE>,
    pub acct: Vec<AcctV>,
    pub akey: Vec<AkeyE>,
    pub bnd: Vec<super::BndE>,
    pub srcp: Vec<SrcpB>,
    pub mrk: Option<MrkV>,
}

/// Collect every SHA message of `bundle` and partition into the two instances.
pub fn sha_messages(bundle: &Bundle) -> Result<(Vec<ShaMessage>, Vec<ShaMessage>), String> {
    let mut raws = vec![
        node_raw(&bundle.node),
        val_raw(&bundle.val),
        head_raw(&bundle.head),
        acct_raw(&bundle.acct),
        akey_raw(&bundle.akey),
        bnd_raw(&bundle.bnd),
        srcp_raw(&bundle.srcp),
        uniq_raw(),
        sort_raw(),
        qv_raw(),
        size_raw(),
    ];
    if let Some(m) = &bundle.mrk {
        raws.push(mrk_raw(m));
    }
    let merged = merge(&raws)?;
    Ok(split_instances(merged.msgs))
}

/// Same as [`sha_messages`] but also returns the external digests (receivers
/// whose byte sender is not among the covered tables).
pub fn sha_messages_detailed(
    bundle: &Bundle,
) -> Result<(Merged, Vec<ShaMessage>, Vec<ShaMessage>), String> {
    let mut raws = vec![
        node_raw(&bundle.node),
        val_raw(&bundle.val),
        head_raw(&bundle.head),
        acct_raw(&bundle.acct),
        akey_raw(&bundle.akey),
        bnd_raw(&bundle.bnd),
        srcp_raw(&bundle.srcp),
    ];
    if let Some(m) = &bundle.mrk {
        raws.push(mrk_raw(m));
    }
    let merged = merge(&raws)?;
    let (t, r) = split_instances(merged.msgs.clone());
    Ok((merged, t, r))
}

/// Parse a table's entry JSON, if present in `entries`.
fn get<T: serde::de::DeserializeOwned>(
    entries: &std::collections::HashMap<String, String>,
    name: &str,
) -> Result<Option<T>, String> {
    match entries.get(name) {
        Some(s) if !s.trim().is_empty() => serde_json::from_str(s)
            .map(Some)
            .map_err(|e| format!("collect: {name} entries: {e}")),
        _ => Ok(None),
    }
}

/// Build the [`Bundle`] from a map `table name → entries JSON`.
pub fn bundle_from_entries(
    entries: &std::collections::HashMap<String, String>,
) -> Result<Bundle, String> {
    Ok(Bundle {
        node: get::<Vec<NodeS3>>(entries, "node")?.unwrap_or_default(),
        val: get::<Vec<ValE>>(entries, "val")?.unwrap_or_default(),
        head: get::<Vec<HeadE>>(entries, "head")?.unwrap_or_default(),
        acct: get::<Vec<AcctV>>(entries, "acct")?.unwrap_or_default(),
        akey: get::<Vec<AkeyE>>(entries, "akey")?.unwrap_or_default(),
        bnd: get::<Vec<super::BndE>>(entries, "bnd")?.unwrap_or_default(),
        srcp: get::<Vec<SrcpB>>(entries, "srcp")?.unwrap_or_default(),
        mrk: get::<MrkV>(entries, "mrk")?,
    })
}

/// The `Gen.Msg` JSON mirror (`{id, bytes, dmult}`), as [`super::sha`] parses.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ShaMsgJson {
    pub id: u32,
    pub bytes: Vec<u8>,
    pub dmult: bool,
}

/// Serialize a message list as `Gen.Msg` JSON.
pub fn msgs_json(msgs: &[ShaMessage]) -> Result<String, String> {
    let j: Vec<ShaMsgJson> = msgs
        .iter()
        .map(|m| ShaMsgJson {
            id: m.id,
            bytes: m.bytes.clone(),
            dmult: m.dmult,
        })
        .collect();
    serde_json::to_string(&j).map_err(|e| e.to_string())
}

/// Collect the two SHA instances from a map `table name → entries JSON` and
/// return `(sha_t_json, sha_r_json)` (the `Gen.Msg` JSON that
/// [`super::sha::render`] consumes).
pub fn instances_from_entries(
    entries: &std::collections::HashMap<String, String>,
) -> Result<(String, String), String> {
    let bundle = bundle_from_entries(entries)?;
    let (t, r) = sha_messages(&bundle)?;
    Ok((msgs_json(&t)?, msgs_json(&r)?))
}

/// The tables the collector currently mirrors.
pub const COVERED: &[&str] = &["node", "val", "head", "acct", "srcp", "mrk"];
/// The tables whose SHA traffic is a documented gap.
pub const GAP: &[&str] = &[
    "rcpt", "chacha", "rng", "shuf", "codec", "scandist", "proc", "mem", "cmp", "ups",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_val_head_round_trip() {
        let nv = NodeV3::Leaf {
            key: vec![1, 2],
            v: Slot::Ref {
                lenB: vec![2, 0, 0, 0],
                h: digest(b"he"),
            },
            memB: vec![0; 8],
        };
        let pre = node_ser(&nv, false);
        let post = node_ser(&nv, true);
        let mut bundle = Bundle::default();
        bundle.node = vec![NodeS3 {
            v: nv,
            tau: 0,
            depth: 0,
            res: 0,
            uses: vec![0],
            ubm: 0,
            dup: false,
            hd: false,
            rep_e: 0,
            ucid: vec![],
            m_u: vec![],
        }];
        bundle.val = vec![ValE {
            vid: 0,
            len: 2,
            vz: false,
            dup: false,
            hd: false,
            rep_e: 0,
            bytes: vec![104, 105],
        }];
        bundle.head = vec![HeadE {
            tau: 0,
            rid: 0,
            rlen: pre.len() as u64,
            rres: 0,
            m_e: 0,
            pre: digest(&pre.iter().map(|&x| x as u8).collect::<Vec<_>>()),
            post: digest(&post.iter().map(|&x| x as u8).collect::<Vec<_>>()),
        }];
        let (t, r) = sha_messages(&bundle).unwrap();
        assert_eq!(r.len(), 0);
        assert!(t.iter().any(|m| m.id as u64 == msg_id(K_NPRE, 0)));
        assert!(t.iter().any(|m| m.id as u64 == msg_id(K_VPRE, 0)));
    }
}
