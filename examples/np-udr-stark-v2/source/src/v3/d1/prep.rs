//! The D1 prepared statement and its public tape: the Rust twin of
//! `ZkFormal.NearV3.D1.Public.PreparedD1Defs` (`PrepD1`, `preparedBytesD1`).  The prover
//! builds it from the native run ([`super::run::D1Run`]); the verifier-side `prepD1` (Lean,
//! `ZkFormal.NearV3.D1.PrepD1`) computes the same bytes from the claim and the hint.

use crate::near::spec::{self as ns, Bytes};
use crate::v3::d0::{fwd_links, prep_claim_with};
use crate::v3::prep::Prep;
use crate::v3::public::{data_bytes, metadata, prepared_blocks};

use super::run::D1Run;

/// `TxOp`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TxOp {
    pub kind: u8,
    pub strict: u8,
    pub ok: u8,
    pub tov: u8,
    pub stage: u8,
    pub cok: u8,
    pub valid: u8,
    pub nonce: u64,
    pub bound: u128,
    pub amount: u128,
}

impl TxOp {
    /// `opLane o i` (9 bytes).
    pub fn lane(&self, i: usize) -> [u8; 9] {
        let byte = |x: u128| if i < 16 { (x >> (8 * i)) as u8 } else { 0 };
        [
            self.kind,
            self.strict,
            self.ok,
            self.tov,
            self.stage,
            self.cok,
            byte(self.nonce as u128),
            byte(self.bound),
            byte(self.amount),
        ]
    }
}

/// `PrepD1`.
#[derive(Clone, Debug)]
pub struct PrepD1 {
    pub base: Prep,
    pub m0: u64,
    pub t0: u64,
    pub o0: u64,
    pub tok0: u128,
    pub ops: Vec<TxOp>,
    /// `(w, key bytes)`
    pub walks: Vec<(u64, Bytes)>,
    pub leaves: Vec<Bytes>,
    pub rids: Vec<Bytes>,
}

/// The prepared statement of a D1 run (prover side).
pub fn prep_of_run(cb: &[u8], run: &D1Run) -> Result<PrepD1, String> {
    let pc = prep_claim_with(cb, true)?;
    let mut out = run.fwd.clone();
    out.extend(run.local_refunds.iter().cloned());
    out.extend(run.refunds.iter().cloned());
    let mut body = ns::u32b(run.w.new_txs.len() as u128);
    for t in &run.w.new_txs {
        body.extend_from_slice(&t.raw);
    }
    body.extend(ns::encode_receipts(&out));
    let fwd = fwd_links(&pc.ctx_b2, &out);
    let mut hdr = pc.hdr.clone();
    hdr.n = run.m0 + run.receipts.len() as u64;
    let base = Prep {
        hdr,
        lists: pc.lists.clone(),
        bnds: pc.bnds.clone(),
        sched: pc.sched.clone(),
        body,
        fwd,
    };
    let ops = run
        .ops
        .iter()
        .map(|o| TxOp {
            kind: o.kind,
            strict: o.strict as u8,
            ok: o.ok as u8,
            tov: o.tov as u8,
            stage: o.stage,
            cok: o.cok as u8,
            valid: o.valid as u8,
            nonce: o.nonce,
            bound: o.bound,
            amount: o.amount,
        })
        .collect();
    Ok(PrepD1 {
        base,
        m0: run.m0,
        t0: run.t0,
        o0: run.o0,
        tok0: run.tok0,
        ops,
        walks: run.walks.clone(),
        leaves: run
            .leaf_pre
            .iter()
            .map(|b| crate::near::reexec::sha256(b).to_vec())
            .collect(),
        rids: run.local_ids.clone(),
    })
}

const PREP_TAG_D1: &[u8] = b"near-arena-prep-d1a-v0";
const SYM_END: u8 = 16;

/// `walkRecs`.
pub fn walk_recs(w: u64, key: &[u8]) -> Vec<Vec<u8>> {
    let wb = [w as u8, (w >> 8) as u8, (w >> 16) as u8];
    let nibs: Vec<u8> = key.iter().flat_map(|b| [b / 16, b % 16]).collect();
    let mut out: Vec<Vec<u8>> = nibs
        .iter()
        .enumerate()
        .map(|(t, &s)| vec![wb[0], wb[1], wb[2], t as u8, s, 0])
        .collect();
    out.push(vec![wb[0], wb[1], wb[2], nibs.len() as u8, SYM_END, 1]);
    out
}

/// `preparedBlocksD1`.
pub fn blocks_d1(p: &PrepD1) -> Vec<Vec<Vec<u8>>> {
    let mut bs = prepared_blocks(&p.base);
    let o0 = (p.o0 as usize).min(p.base.body.len());
    bs.push(p.base.body[..o0].iter().skip(8).map(|&b| vec![b]).collect());
    bs.push(
        p.ops
            .iter()
            .flat_map(|o| (0..16).map(move |i| o.lane(i).to_vec()))
            .collect(),
    );
    bs.push(p.ops.iter().map(|o| vec![o.valid]).collect());
    bs.push(p.walks.iter().flat_map(|(w, k)| walk_recs(*w, k)).collect());
    bs.push(p.leaves.clone());
    bs.push(
        p.rids
            .iter()
            .flat_map(|d| d.iter().map(|&b| vec![b]))
            .collect(),
    );
    bs
}

/// `preparedBytesD1 p oh`.
pub fn prepared_bytes_d1(p: &PrepD1, overhead: u32) -> Vec<u8> {
    let mut header = ns::borsh_bytes(PREP_TAG_D1);
    header.extend(p.base.hdr.encode());
    header.extend(ns::u32b(p.base.body.len() as u128));
    header.extend(ns::u32b(overhead as u128));
    let mut ext = ns::u32b(p.m0 as u128);
    ext.extend(ns::u32b(p.t0 as u128));
    ext.extend(ns::u32b(p.o0 as u128));
    ext.extend(ns::u128b(p.tok0));
    let blocks = blocks_d1(p);
    let mut v = header.clone();
    v.extend(metadata(
        header.len() + 8 * blocks.len() + ext.len(),
        &blocks,
    ));
    v.extend(ext);
    v.extend(data_bytes(&blocks));
    v
}
