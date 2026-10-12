//! The prepared public tape (`ZkFormal.NearV3.Public.preparedBytes`) — the v0
//! STARK's public vector `cb'` for `nearAirV3`.
//!
//! Mirrors `zk-formal/ZkFormal/NearV3/Public/Prepared.lean` (header + 9 blocks
//! `metadata` + `dataBytes`) and the record payloads in
//! `Public/{Source,Boundary,Body,NatRecords}.lean` + `Sched/Render.lean`
//! (`PubRecs`).  `np-lean-prep-v3`-style differential: the caller passes the
//! `Prep` structure (from `v3::prep`) and the witness overhead; `prepared_bytes`
//! returns exactly `Prep.encode`-independent `Public.preparedBytes p oh`.
//!
//! Segment layout (compile-time, `Public.preparedSegments`): 9 descriptors, header
//! length 202, counts/offsets in the header metadata.  This module produces the
//! raw bytes; the AIR's `pubSegs` reads records back out of them.

use crate::v3::prep::{Prep, SchedPub, SrcList};

/// `NearSpec.u32` little endian.
fn u32b(x: u32) -> Vec<u8> {
    x.to_le_bytes().to_vec()
}
fn u8b(x: u8) -> Vec<u8> {
    vec![x]
}
fn u64b(x: u64) -> Vec<u8> {
    x.to_le_bytes().to_vec()
}

/// `borshBytes`: u32 length then the bytes.
fn borsh(b: &[u8]) -> Vec<u8> {
    let mut v = u32b(b.len() as u32);
    v.extend_from_slice(b);
    v
}

const PREP_TAG: &[u8] = b"near-arena-prep-d0a-v0";

/// `Public.preparedBytes p overhead` = `encode (headerBytes p oh) (preparedBlocks p)`
/// = header ‖ metadata ‖ dataBytes.
pub fn prepared_bytes(p: &Prep, overhead: u32) -> Vec<u8> {
    let header = header_bytes(p, overhead);
    let blocks = prepared_blocks(p);
    encode(&header, &blocks)
}

/// `Public.headerBytes p oh` = `borshBytes prepTag ‖ p.hdr.encode ‖ u32 |body| ‖ u32 oh`.
fn header_bytes(p: &Prep, overhead: u32) -> Vec<u8> {
    let mut v = borsh(PREP_TAG);
    v.extend(p.hdr.encode());
    v.extend(u32b(p.body.len() as u32));
    v.extend(u32b(overhead));
    v
}

/// `Public.preparedBlocks p`: the nine payloads, in order.
fn prepared_blocks(p: &Prep) -> Vec<Vec<Vec<u8>>> {
    let (pubb, par, dl_send, dl_recv) = scheduler_records(p);
    vec![
        source_payload(&p.lists),
        boundary_payload(&p.bnds),
        body_payload(&p.body),
        nat_payload(&pubb),
        nat_payload(&par),
        nat_payload(&dl_send),
        nat_payload(&dl_recv),
        root_payload(0, &p.hdr.prev_state_root),
        root_payload(p.hdr.k + 1, &p.hdr.post_state_root),
    ]
}

/// `Public.encode header blocks` = `header ‖ metadata (...) blocks ‖ dataBytes blocks`.
fn encode(header: &[u8], blocks: &[Vec<Vec<u8>>]) -> Vec<u8> {
    let data_start = header.len() + 8 * blocks.len();
    let mut v = header.to_vec();
    v.extend(metadata(data_start, blocks));
    v.extend(data_bytes(blocks));
    v
}

/// Eight bytes per segment: `u32 row count ‖ u32 absolute payload offset`.
fn metadata(start: usize, blocks: &[Vec<Vec<u8>>]) -> Vec<u8> {
    let mut v = Vec::new();
    let mut s = start;
    for rs in blocks {
        v.extend(u32b(rs.len() as u32));
        v.extend(u32b(s as u32));
        s += payload_bytes(rs).len();
    }
    v
}

fn payload_bytes(rs: &[Vec<u8>]) -> Vec<u8> {
    rs.iter().flatten().copied().collect()
}

fn data_bytes(blocks: &[Vec<Vec<u8>>]) -> Vec<u8> {
    blocks.iter().flat_map(|b| payload_bytes(b)).collect()
}

// ---------------------------------------------------------------------------
// Payloads
// ---------------------------------------------------------------------------

/// `Public.sourcePayload` (`Public/Source.lean`): `[dup] ‖ root[32]` per list.
fn source_payload(lists: &[SrcList]) -> Vec<Vec<u8>> {
    (0..lists.len())
        .map(|j| {
            let dup = source_dup(lists, j);
            let mut row = vec![if dup { 1u8 } else { 0u8 }];
            row.extend_from_slice(&lists[j].root);
            row
        })
        .collect()
}

fn source_dup(lists: &[SrcList], j: usize) -> bool {
    let key = &lists[j].key;
    lists[..j].iter().any(|s| &s.key == key)
}

/// `Public.boundaryPayload`: `BND_STRIDE * |bounds|` rows of `[lo, hi, hn]`.
fn boundary_payload(bounds: &[(Option<Vec<u8>>, Option<Vec<u8>>)]) -> Vec<Vec<u8>> {
    const STRIDE: usize = 65;
    (0..STRIDE * bounds.len())
        .map(|x| {
            let b = &bounds[x / STRIDE];
            let k = x % STRIDE;
            let lo = b.0.as_ref().and_then(|s| s.get(k)).copied().unwrap_or(0);
            let hi = b.1.as_ref().and_then(|s| s.get(k)).copied().unwrap_or(0);
            let hn = if b.1.is_none() { 1 } else { 0 };
            vec![lo, hi, hn]
        })
        .collect()
}

/// `Public.bodyPayload body = (body.drop 8).map [b]` (bytes after the `u32 0`).
fn body_payload(body: &[u8]) -> Vec<Vec<u8>> {
    body.iter().skip(8).map(|&b| vec![b]).collect()
}

/// `Public.natPayload`: each row is a `List Nat` cast to bytes.
fn nat_payload(records: &[Vec<u64>]) -> Vec<Vec<u8>> {
    records
        .iter()
        .map(|r| r.iter().map(|&n| n as u8).collect())
        .collect()
}

/// `Public.rootPayload (τ, root) = [[τ] ++ root]`.
fn root_payload(tau: u64, root: &[u8]) -> Vec<Vec<u8>> {
    let mut row = vec![tau as u8];
    row.extend_from_slice(root);
    vec![row]
}

// ---------------------------------------------------------------------------
// Scheduler public records (`ZkFormal.NearV3.Sched.render`)
// ---------------------------------------------------------------------------

// Tags / part-kind bytes (`Sched/Ids.lean`).
const TAG_ASH: u64 = 2;
const TAG_KEY: u64 = 3;
const TAG_FWD: u64 = 4;
const PT_SCAN: u64 = 1;
const PT_RAW: u64 = 2;
const PT_SHD: u64 = 3;
const PT_LINK: u64 = 4;

fn b2(x: u64) -> Vec<u64> {
    vec![x % 256, x / 256 % 256]
}
fn b3(x: u64) -> Vec<u64> {
    vec![x % 256, x / 256 % 256, x / 65536 % 256]
}

/// `indexOf ids x` (first index).
fn index_of(ids: &[u64], x: u64) -> Option<usize> {
    ids.iter().position(|&y| y == x)
}

/// `tgt ids k`.
fn tgt(ids: &[u64], k: u64) -> u64 {
    let n = ids.len() as u64;
    let s = ids[(k / n) as usize];
    let r = ids[(k % n) as usize];
    index_of(ids, s).unwrap_or(0) as u64 * n + index_of(ids, r).unwrap_or(0) as u64
}

/// `srcOf ids l` (last record mapped to link `l`).
fn src_of(ids: &[u64], l: u64) -> Option<u64> {
    let count = ids.len() as u64 * ids.len() as u64;
    (0..count).filter(|&k| tgt(ids, k) == l).last()
}

fn cnt_s(n: usize, allowed: &[bool], s: usize) -> u64 {
    (0..n).filter(|&r| allowed[s * n + r]).count() as u64
}
fn cnt_r(n: usize, allowed: &[bool], r: usize) -> u64 {
    (0..n).filter(|&s| allowed[s * n + r]).count() as u64
}

fn src_fields(ids: &[u64], l: u64) -> Vec<u64> {
    let count = ids.len() as u64 * ids.len() as u64;
    let src = src_of(ids, l);
    let use_ = (0..count).any(|k| src_of(ids, k) == Some(l));
    let mut v = b2(src.unwrap_or(0));
    v.push(if src.is_some() { 1 } else { 0 });
    v.push(if use_ { 1 } else { 0 });
    v
}

fn key_recs(tau: u64, seed: &[u8]) -> Vec<Vec<u64>> {
    (0..16u64)
        .map(|k| {
            vec![
                tau,
                TAG_KEY,
                k,
                *seed.get((2 * k) as usize).unwrap_or(&0) as u64,
                *seed.get((2 * k + 1) as usize).unwrap_or(&0) as u64,
                0,
                0,
            ]
        })
        .collect()
}

fn ash_recs(tau: u64, ash: &[u8]) -> Vec<Vec<u64>> {
    (0..32u64)
        .map(|j| vec![tau, TAG_ASH, j, *ash.get(j as usize).unwrap_or(&0) as u64, 0, 0, 0])
        .collect()
}

fn par_codec(tau: u64, sp: &SchedPub) -> Vec<u64> {
    let n = sp.ids.len() as u64;
    let mut v = vec![tau, 0, n];
    v.extend(b2(n * n));
    v.extend(b3(sp.params.base));
    v.extend(b3(sp.params.max_shard_bandwidth / n.max(1)));
    v
}

fn par_scan(tau: u64, sp: &SchedPub) -> Vec<u64> {
    let n = sp.ids.len() as u64;
    let mut v = vec![tau, PT_SCAN];
    v.extend(b3(sp.params.base));
    v.extend(b3(sp.params.max_single_grant.saturating_sub(sp.params.base)));
    v.extend([n, 0, 0]);
    v
}

/// Resolve `rawOf sp.ids sp.raw` then filter to requests with a nonempty increase
/// list (`Sched.instOf`).  This is the `PubRecs.raw`.
fn resolved_raw(sp: &SchedPub) -> Vec<(u64, u64, Vec<u8>)> {
    let mut out = Vec::new();
    for (sender, brs) in &sp.raw {
        let Some(s) = index_of(&sp.ids, *sender) else { continue };
        for br in brs {
            if let Some(r) = index_of(&sp.ids, br.to_shard) {
                if !incs_of(sp, &br.bitmap).is_empty() {
                    out.push((s as u64, r as u64, br.bitmap.clone()));
                }
            }
        }
    }
    out
}

/// `render.rawRecs`: `[τ, PT_RAW] ++ bm[0..5] ++ b2 cid ++ [s, r]`.
fn raw_recs(tau: u64, raw: &[(u64, u64, Vec<u8>)]) -> Vec<Vec<u64>> {
    raw.iter()
        .enumerate()
        .map(|(cid, (s, r, bm))| {
            let mut v = vec![tau, PT_RAW];
            for i in 0..5 {
                v.push(*bm.get(i).unwrap_or(&0) as u64);
            }
            v.extend(b2(cid as u64));
            v.push(*s);
            v.push(*r);
            v
        })
        .collect()
}

/// `Sched.setBits` / `incsOf`: whether the request has any set bit under 40.
fn incs_of(_sp: &SchedPub, bm: &[u8]) -> Vec<u64> {
    (0..40u8)
        .filter(|&i| {
            let byte = *bm.get((i / 8) as usize).unwrap_or(&0);
            (byte >> (i % 8)) % 2 == 1
        })
        .map(|i| i as u64)
        .collect()
}

fn shard_recs(tau: u64, sp: &SchedPub) -> Vec<Vec<u64>> {
    let n = sp.ids.len();
    let mut out = Vec::new();
    for side in 0..2u64 {
        for x in 0..n {
            let cnt = if side == 0 {
                cnt_s(n, &sp.allowed, x)
            } else {
                cnt_r(n, &sp.allowed, x)
            };
            let budget = sp.params.max_shard_bandwidth.saturating_sub(sp.params.base * cnt);
            let mut v = vec![tau, PT_SHD, side, x as u64, cnt];
            v.extend(b3(budget));
            v.extend([n as u64, 0, 0]);
            out.push(v);
        }
    }
    out
}

fn link_recs(tau: u64, sp: &SchedPub) -> Vec<Vec<u64>> {
    let n = sp.ids.len();
    (0..n * n)
        .map(|l| {
            let mut v = vec![tau, PT_LINK];
            v.extend(src_fields(&sp.ids, l as u64));
            v.extend([0, 0]);
            v.extend(b2(l as u64));
            v.push(if sp.allowed[l] { 1 } else { 0 });
            v
        })
        .collect()
}

fn id_byte(ids: &[u64], k: u64, o: u64) -> u64 {
    let n = ids.len() as u64;
    let id = if o < 8 { ids[(k / n) as usize] } else { ids[(k % n) as usize] };
    id / 256u64.pow((o % 8) as u32) % 256
}

fn dl_recs(tau: u64, ids: &[u64]) -> Vec<Vec<u64>> {
    let count = (ids.len() * ids.len()) as u64;
    (0..count)
        .flat_map(|k| (0..16u64).map(move |o| {
            let mut v = vec![tau];
            v.extend(b2(k));
            v.push(o);
            v.push(id_byte(ids, k, o));
            v
        }))
        .collect()
}

fn fwd_recs(sp: &SchedPub, fwd: &[(u64, u64)]) -> Vec<Vec<u64>> {
    let n = sp.ids.len();
    (0..n * n)
        .map(|l| {
            let mut v = vec![0, TAG_FWD];
            v.extend(b2(l as u64));
            v.extend(b3(fwd.iter().find(|(x, _)| *x == l as u64).map(|(_, y)| *y).unwrap_or(0)));
            v
        })
        .collect()
}

/// `Sched.render (p.sched.map instOf) p.fwd` → `(pubb, par, dlSend, dlRecv)`.
fn scheduler_records(p: &Prep) -> (Vec<Vec<u64>>, Vec<Vec<u64>>, Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let ps = &p.sched;
    let inst = |tau: usize| ps.get(tau);
    let mut pubb = Vec::new();
    let mut par = Vec::new();
    for tau in 0..ps.len() {
        let sp = inst(tau).expect("sched");
        pubb.extend(key_recs(tau as u64, &sp.seed));
        pubb.extend(ash_recs(tau as u64, &sp.all_shards_hash));
        par.push(par_codec(tau as u64, sp));
        let resolved = resolved_raw(sp);
        if !resolved.is_empty() {
            par.push(par_scan(tau as u64, sp));
        }
        par.extend(raw_recs(tau as u64, &resolved));
        par.extend(shard_recs(tau as u64, sp));
        par.extend(link_recs(tau as u64, sp));
    }
    if let Some(sp0) = inst(0) {
        pubb.extend(fwd_recs(sp0, &p.fwd));
    }
    let ids = inst(0).map(|s| s.ids.clone()).unwrap_or_default();
    let dl_send = dl_recs(0, &ids);
    let dl_recv = dl_recs(ps.len() as u64, &ids);
    (pubb, par, dl_send, dl_recv)
}

// Keep `u8b`, `u64b` referenced (used by future header variants).
#[allow(dead_code)]
fn _unused() {
    let _ = u8b(0);
    let _ = u64b(0);
}
