//! D1 (`nearAirV3D1`, lane v3-d1-tables): the honest 30-table trace of a D1a case.
//!
//! * [`run`]: the native D1 run (`processTxs`, local and incoming receipts) and its
//!   trie-side `Native` (AIR pre trie over the read keys);
//! * [`prep`]: the D1 prepared statement and public tape (`PreparedD1Defs`);
//! * [`tables`]: `txV3`, `akmV3`, `kibV3`, `plfV3`, `ridV3`;
//! * [`case_inputs_d1`]: every table's entries — the 25 `nearAirV3` generators fed with the
//!   D1 run (`rcptV3D1` offsets, signer accounts in `acctV3`, `akeyV3` without the keys
//!   `akmV3` owns, all leaves in `mrkV3`, local ids in `sortV3`, the D1 SHA jobs) — plus the
//!   five D1 tables.
//!
//! The D0a paths (`v3::prove::case_inputs`, `npudr v3prove`) are not changed.

pub mod ed25519;
pub mod prep;
pub mod run;
pub mod tables;
pub mod tx;

use std::collections::HashMap;

use crate::near::reexec::sha256;
use crate::near::spec::{self as ns, account_key_path};
use crate::v3::acct::AcctV;
use crate::v3::hint::{get, key_access_key, lookup_last};
use crate::v3::mrksort::{MNode, MrkV, mrk_from_levels, qbase};
use crate::v3::rcpt::D1Off;
use crate::v3::rcptfam::{self, native_refund, sort_le};
use crate::v3::{AkeyE, Tab};

use self::prep::PrepD1;
use self::run::{D1Run, K_PLF, W_LOC};
use self::tables::{AkmE, TxE};

/// `nearTablesD1` order.
pub const ORDER_D1: &[&str] = &[
    "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf",
    "codec", "scandist", "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv",
    "mrk", "sort", "tx", "akm", "kib", "plf", "rid",
];

fn nats(b: &[u8]) -> Vec<u64> {
    b.iter().map(|&x| x as u64).collect()
}

fn le_n(x: u128, n: usize) -> Vec<u64> {
    (0..n)
        .map(|i| {
            if i < 16 {
                ((x >> (8 * i)) & 0xff) as u64
            } else {
                0
            }
        })
        .collect()
}

/// The D1 hint on the wire: `u32 n ‖ borshBytes (u32 |txs| ‖ raws) ‖ borshBytes (u32 |newTxs| ‖
/// raws) ‖ borshBytes (one byte per op: stage ‖ ok << 2) ‖ borshBytes (encodeReceipts refunds)`.
pub fn hint_d1(run: &D1Run) -> Vec<u8> {
    let vec_raw = |ts: &[tx::Tx]| {
        let mut v = ns::u32b(ts.len() as u128);
        for t in ts {
            v.extend_from_slice(&t.raw);
        }
        v
    };
    let mut h = ns::u32b(run.receipts.len() as u128);
    h.extend(ns::borsh_bytes(&vec_raw(&run.w.txs)));
    h.extend(ns::borsh_bytes(&vec_raw(&run.w.new_txs)));
    let bits: Vec<u8> = run
        .ops
        .iter()
        .filter(|o| o.kind == 0)
        .map(|o| o.stage | ((o.ok as u8) << 2))
        .collect();
    h.extend(ns::borsh_bytes(&bits));
    h.extend(ns::borsh_bytes(&ns::encode_receipts(&run.refunds)));
    h
}

/// The `txV3` entries.
pub fn tx_entries(run: &D1Run) -> Vec<TxE> {
    run.ops
        .iter()
        .map(|o| {
            let a = o.acct.clone();
            TxE {
                kind: o.kind as u64,
                strict: o.strict as u64,
                ok: o.ok as u64,
                tov: o.tov as u64,
                stage: o.stage as u64,
                cok: o.cok as u64,
                valid: o.valid as u64,
                nonce: o.nonce,
                bound: o.bound,
                amount: o.amount,
                vid_a: o.vid_a,
                tp_a: o.tp_a,
                amt: a.as_ref().map_or(0, |a| a.amount),
                lk: a.as_ref().map_or(0, |a| a.locked),
                st: a.as_ref().map_or(0, |a| a.storage_usage as u64),
                vid_k: o.vid_k,
                tp_k: o.tp_k,
                kn: o.kn,
                fa: o.fa as u64,
            }
        })
        .collect()
}

/// The `akmV3` entries.
pub fn akm_entries(run: &D1Run) -> Vec<AkmE> {
    run.akm
        .iter()
        .map(|s| AkmE {
            vid: s.vid,
            bytes: s.bytes.clone(),
            tlast: s.tlast,
            post: s.post.clone(),
            u: s.u,
        })
        .collect()
}

/// The receipt side of the D1 run: `rcptV3D1`, `acctV3`, `akeyV3`, `bndV3`, `srcpV3`, `mrkV3`,
/// `sortV3` entries.
pub struct RcptD1 {
    pub rcpt: crate::v3::rcpt::RcptIn,
    pub acct: Vec<AcctV>,
    pub akey: Vec<AkeyE>,
    pub bnd: Vec<crate::v3::BndE>,
    pub srcp: Vec<crate::v3::srcp::SrcpB>,
    pub mrk: MrkV,
    pub sort: Vec<(u64, Vec<u64>)>,
}

pub fn rcpt_side(run: &D1Run, p: &PrepD1) -> Result<RcptD1, String> {
    let k = &run.k;
    let lists: Vec<Vec<(ns::Receipt, bool)>> = p
        .base
        .lists
        .iter()
        .map(|s| {
            lookup_last(&s.key, &run.w.base.entries)
                .map(|e| e.receipts.clone())
                .unwrap_or_default()
                .into_iter()
                .map(|r| {
                    let f = native_refund(run.ctx.gas_price, &r);
                    (r, f)
                })
                .collect()
        })
        .collect();
    let n = rcptfam::Native {
        own: k.h_chunk.shard_id,
        height: run.ctx.height,
        bgp: run.ctx.gas_price,
        layout: k.layout.clone(),
        sources: p.base.lists.clone(),
        entries: run.w.base.entries.clone(),
        lists,
        pre: run.pre.clone(),
        accounts: run.incoming_accounts.clone(),
        post: run.post_main.clone(),
    };
    if n.rs().len() != run.receipts.len() {
        return Err("D1: source lists do not flatten to the applied receipts".into());
    }
    let mut rc = rcptfam::rcpt_view(&n);
    let mut i = 0;
    for l in rc.lists.iter_mut() {
        for e in l.rs.iter_mut() {
            e.tprev = run.incoming_tprev[i];
            i += 1;
        }
    }
    rc.d1 = Some(D1Off {
        t0: run.t0,
        o0: run.o0,
        tok0: run.tok0,
    });
    let bnd = rcptfam::bnd_entries(&n, &rc);
    // accounts: every account an op or a receipt touches
    let vals = rcptfam::vals_of(&run.pre);
    let mut acct = vec![];
    for key in &run.acct_order {
        let i = rcptfam::value_index(&run.pre, key).ok_or("D1 acct: value index")?;
        let post = get(&run.post_main, key)
            .and_then(|b| ns::Account::decode(&b))
            .ok_or("D1 acct: post")?;
        acct.push(AcctV {
            k: i as u64,
            tlast: run.acct_last[key],
            pre: nats(vals.get(i).ok_or("D1 acct: pre")?),
            post: le_n(post.amount, 16),
        });
    }
    // access keys of gas refunds not read by a transaction
    let akm_vids: Vec<u64> = run.akm.iter().map(|s| s.vid).collect();
    let akey = rcptfam::akey_providers(&n)
        .into_iter()
        .filter(|e| !akm_vids.contains(&e.vid))
        .collect();
    // outcome tree over all leaves
    let total = run.all_leaf_pre.len() as u64;
    let mut lv: Vec<Vec<MNode>> = vec![
        run.all_leaf_pre
            .iter()
            .enumerate()
            .map(|(pos, b)| MNode {
                id: if (pos as u64) < run.m0 {
                    K_PLF + 16 * pos as u64
                } else {
                    4 + 16 * (pos as u64 - run.m0)
                },
                len: b.len() as u64,
                dig: nats(&sha256(b)),
            })
            .collect(),
    ];
    for j in 0..=run.all_leaf_pre.len() {
        let prev = &lv[j];
        let next: Vec<MNode> = (0..prev.len().div_ceil(2))
            .map(|i| {
                if 2 * i + 1 < prev.len() {
                    let b: Vec<u8> = prev[2 * i]
                        .dig
                        .iter()
                        .chain(&prev[2 * i + 1].dig)
                        .map(|&x| x as u8)
                        .collect();
                    MNode {
                        id: 6 + 16 * (qbase(total, j as u64 + 1) + i as u64),
                        len: 64,
                        dig: nats(&sha256(&b)),
                    }
                } else {
                    prev[2 * i].clone()
                }
            })
            .collect();
        lv.push(next);
    }
    let mrk = if total == 0 {
        MrkV {
            levels: lv,
            ..MrkV::default()
        }
    } else {
        MrkV {
            levels: lv.clone(),
            ..mrk_from_levels(total, &lv)
        }
    };
    let mut sort: Vec<(u64, Vec<u64>)> = run
        .local_ids
        .iter()
        .enumerate()
        .map(|(l, id)| (W_LOC + l as u64, nats(id)))
        .chain(
            run.receipts
                .iter()
                .enumerate()
                .map(|(i, r)| (i as u64, nats(&r.receipt_id))),
        )
        .collect();
    sort_le(&mut sort);
    Ok(RcptD1 {
        rcpt: rc,
        acct,
        akey,
        bnd,
        srcp: rcptfam::srcp_blocks(&n),
        mrk,
        sort,
    })
}

/// Everything the D1 prover needs for one case.
pub struct CaseD1 {
    pub run: D1Run,
    pub prep: PrepD1,
    pub tape: Vec<u8>,
    /// `txOverhead` (`PH_WOVH`)
    pub ovh: u32,
    pub hint: Vec<u8>,
    /// entries of the 25 `nearAirV3` tables (as `v3::prove::case_inputs`)
    pub entries: HashMap<String, String>,
    pub tx: Vec<TxE>,
    pub akm: Vec<AkmE>,
}

pub fn case_inputs_d1(cb: &[u8], wb: &[u8]) -> Result<CaseD1, String> {
    let run = run::d1_run(cb, wb)?;
    let p = prep::prep_of_run(cb, &run)?;
    // `txOverhead`: the transaction vectors the AIR does not see (`sizeV3`'s `OVH`)
    let ovh: usize = [&run.w.txs, &run.w.new_txs].iter().map(|v| 4 + v.iter().map(|t| t.raw.len()).sum::<usize>()).sum();
    let tape = prep::prepared_bytes_d1(&p, ovh as u32);
    let native = run.native()?;
    let js = |v: serde_json::Result<String>| v.map_err(|e| e.to_string());
    let mut entries: HashMap<String, String> = HashMap::new();
    let mut tv = crate::v3::trie::entries_of(&native, &p.base, &run.w.base.entries)?;
    // `sizeV3` reads `OVH` from the D1 tape
    tv["size"][0]["ovh"] = serde_json::json!(ovh);
    for t in ["node", "val", "head", "walk", "uniq", "ups", "size"] {
        entries.insert(
            t.into(),
            tv.get(t)
                .ok_or(format!("v3trie: no table {t}"))?
                .to_string(),
        );
    }
    let f = rcpt_side(&run, &p)?;
    for (t, s) in [
        ("rcpt", js(serde_json::to_string(&f.rcpt))?),
        ("acct", js(serde_json::to_string(&f.acct))?),
        ("akey", js(serde_json::to_string(&f.akey))?),
        ("bnd", js(serde_json::to_string(&f.bnd))?),
        ("srcp", js(serde_json::to_string(&f.srcp))?),
        ("mrk", js(serde_json::to_string(&f.mrk))?),
        ("sort", js(serde_json::to_string(&f.sort))?),
    ] {
        entries.insert(t.into(), s);
    }
    let sq = crate::v3::schedqv::derive_from(&native, &run.k, run.w.base.implicit.len(), &p.base)?;
    let blocks = js(serde_json::to_string(&sq.blocks))?;
    for t in ["codec", "scandist", "proc", "mem", "cmp"] {
        entries.insert(t.into(), blocks.clone());
    }
    let rs: Vec<&crate::v3::sched::Run> = sq.blocks.iter().map(|b| &b.run).collect();
    let (reqs, calls, insts) = crate::v3::chacha::lane(&rs);
    for (t, s) in [
        ("chacha", js(serde_json::to_string(&reqs))?),
        ("rng", js(serde_json::to_string(&calls))?),
        ("shuf", js(serde_json::to_string(&insts))?),
        ("qv", js(serde_json::to_string(&sq.qv))?),
    ] {
        entries.insert(t.into(), s);
    }
    let akm = akm_entries(&run);
    let akm_posts: Vec<(u64, Vec<u8>)> = akm
        .iter()
        .filter(|e| e.bytes.len() == 9 && e.bytes[8] == 1)
        .map(|e| {
            let mut b = e.post.clone();
            b.push(1);
            (e.vid, b)
        })
        .collect();
    let (sha_t, sha_r) = crate::v3::collect::instances_d1(&entries, &run.all_leaf_pre, &akm_posts)?;
    entries.insert("sha_t".into(), sha_t);
    entries.insert("sha_r".into(), sha_r);
    let tx = tx_entries(&run);
    // the native verdict and the table's recomputation agree
    for (i, e) in tx.iter().enumerate() {
        if e.kind == 0 && (e.ok == 1) != tables::tx_verdict(e) {
            return Err(format!("D1: op {i}: native verdict differs from txV3's"));
        }
    }
    let hint = hint_d1(&run);
    let _ = account_key_path;
    let _ = key_access_key;
    Ok(CaseD1 {
        run,
        prep: p,
        tape,
        hint,
        entries,
        tx,
        akm,
    })
}

/// The five D1 tables.
pub fn d1_tables(c: &CaseD1) -> Result<Vec<Tab>, String> {
    let keys: Vec<Vec<u8>> = c
        .prep
        .walks
        .iter()
        .flat_map(|(w, k)| prep::walk_recs(*w, k))
        .collect();
    Ok(vec![
        tables::tx_trace(&c.tx),
        tables::akm_trace(&c.akm)?,
        tables::kib_trace(&keys),
        tables::plf_trace(&c.prep.leaves),
        tables::rid_trace(&c.prep.rids),
    ])
}
