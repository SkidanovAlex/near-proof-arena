//! Honest entries of the scheduler / ChaCha / queue-value tables of `nearAirV3`
//! (8 chacha, 9 rng, 10 shuf, 11 codec, 12 scandist, 13 proc, 14 mem, 15 cmp, 22 qv)
//! from a real claim + witness: the Rust twin of `conformance/SchedEntriesV3.lean`
//! (`np-lean-sched-v3`), reusing the native execution of [`super::native`].
//!
//! **Blocks** (tables 11–15; 8–10 are their runs' lane entries, [`super::chacha::lane`]).
//! The completeness proof renders the `PriorCore` blocks `bs` built by
//! `native_allocated_blocks_run` (`Assembly/SchedulerCodecRetainedAllocation.lean`): one
//! block per scheduler call, the main chunk (`τ = 0`, `(m.ctx k, m.pre)`) then one per
//! implicit step (`(implicitCtx k e, e.pre)`).  Per block ([`block`]):
//!
//! | Rust | Lean |
//! |---|---|
//! | `sp = p.sched[τ]`, checked `= d0::sched_pub ctx` | `PreparedRun`, `schedPub ctx = some sp` |
//! | `prior = find pre keyBwState` | `readKey pre keyBwState` |
//! | `prev` ([`native::sched::decode_state`]) | `ProcActualCore.decodePrevious` |
//! | [`actual_run`] | `Gen.ActualRun.run (ProcPreparedSequence.input sp prev) τ` (`Candidates/ProcActualRun.lean`) |
//! | [`process_ev`] | `Sched.processEv` (`Sched/Model.lean`) |
//! | [`link_pass`] / [`allowances`] / [`a0_canon`] | `linkPass` / `ProcActualInput.allowances` / `a0Canon` |
//! | [`distribute_ev`] (grants) | `distributeEv` on `ProcActualInput.process`'s state |
//! | `vid` | `nativePriorIds (m.pre :: steps.pre) τ` = `priorValueId` |
//! | `fwd` (`τ = 0`: `p.fwd`) | `fwdLinks (m.ctx k) out.outgoing` (`prepBody`'s `fwd`); `[]` for missing chunks |
//!
//! The run omits `ActualRun.run`'s redundant `coreEv` cross-check (it re-runs the same
//! `processEv` on the same initial state, so it can only agree); every other check of
//! the Lean run is kept.
//!
//! **qv** (table 22): `A.qvAcc` = walks `plan pre v pres (NativeQueueIds.resolve pre v pres)`
//! and records `queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))`
//! ([`qv_entries`]; `Render/PaddedQvNative.lean`, `Assembly/QueueForest.lean`,
//! `QueuePayload.lean`, `Qv/Candidates/CombinedWalkGen.lean`).
//!
//! `npudr v3sched <case_dir> <out_dir>` writes the files of
//! `docs/logs/v3-prover-schedqv-2026-10.md` (`codec/scandist/proc/mem/cmp.json` = the block
//! list, `chacha/rng/shuf.json`, `qv.json`).

use crate::near::spec::{Bytes, PTrie, u64b};
use crate::v3::d0::{self, Stream, block_ctx, chacha_block, walk_d0};
use crate::v3::hint::{
    decode_w, find, hint_of_e, key_buffered_idx, key_bw_state, key_delayed_idx, key_groups_data,
    key_yield_idx,
};
use crate::v3::native::sched::{BwState, decode_state};
use crate::v3::native::{self, MainValues};
use crate::v3::prep::{SchedParams, SchedPub};
use crate::v3::qv::{QvIn, QvItem, QvRecIn, QvWalkIn};
use crate::v3::rcptfam::{vals_of, value_index};
use crate::v3::sched::{
    self as sc, CReq, Entry, MOp, PState, Params, Rng, RoundD, Run, SchedIn, Seg,
};

/// `T0`: process times start at `2^20` (`Sched/Ids.lean`).
const T0: u64 = 1_048_576;
/// `Proc.KSENT`.
const KSENT: u64 = 16_777_216;
const OP_READ: u64 = 1;
const OP_GRANT: u64 = 2;

fn chk(b: bool, m: &str) -> Result<(), String> {
    if b { Ok(()) } else { Err(m.to_string()) }
}

/// `a[i]!` on a `Nat` array (default 0).
fn at(a: &[u64], i: u64) -> u64 {
    a.get(i as usize).copied().unwrap_or(0)
}

/// `allowed[l]!` (default false).
fn al_at(a: &[bool], l: u64) -> bool {
    a.get(l as usize).copied().unwrap_or(false)
}

/// `indexOf ids x` (first index).
fn index_of(ids: &[u64], x: u64) -> Option<u64> {
    ids.iter().position(|&y| y == x).map(|i| i as u64)
}

// ---------------------------------------------------------------------------
// Requests and the link pass (`Sched/Model.lean`, `Sched/Spec/Conv.lean`)
// ---------------------------------------------------------------------------

/// `RawReq = (s, r, bitmap)` with shard indices.
#[derive(Clone, Debug)]
pub struct RawReq {
    pub s: u64,
    pub r: u64,
    pub bm: Vec<u8>,
}

/// `getBit bm i`.
fn get_bit(bm: &[u8], i: u64) -> bool {
    (bm.get((i / 8) as usize).copied().unwrap_or(0) >> (i % 8)) & 1 == 1
}

/// `setBits bm`: positions `< 40` of the set bits, ascending.
fn set_bits(bm: &[u8]) -> Vec<u64> {
    (0..40).filter(|&i| get_bit(bm, i)).collect()
}

/// `requestValues p`.
fn request_values(p: &SchedParams) -> Vec<u64> {
    (0..40u64)
        .map(|i| p.base + (p.max_single_grant - p.base) * (i + 1) / 40)
        .collect()
}

/// `incsOf p bm = incsFrom (requestValues p) p.base (setBits bm)` (`Nat` subtraction).
fn incs_of(p: &SchedParams, bm: &[u8]) -> Vec<u64> {
    let vals = request_values(p);
    let mut prev = p.base;
    let mut out = Vec::new();
    for c in set_bits(bm) {
        let v = at(&vals, c);
        out.push(v.saturating_sub(prev));
        prev = v;
    }
    out
}

/// `(instOf sp).raw = (rawOf sp.ids sp.raw).filter (incsOf … ≠ [])`.
fn inst_raw(sp: &SchedPub) -> Vec<RawReq> {
    let mut out = Vec::new();
    for (sender, brs) in &sp.raw {
        for br in brs {
            if let (Some(s), Some(r)) = (index_of(&sp.ids, *sender), index_of(&sp.ids, br.to_shard))
                && !incs_of(&sp.params, &br.bitmap).is_empty()
            {
                out.push(RawReq {
                    s,
                    r,
                    bm: br.bitmap.clone(),
                });
            }
        }
    }
    out
}

/// `Req` (`link`, increases).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Req {
    link: u64,
    incs: Vec<u64>,
}

/// `convRaw p n raw`.
fn conv_raw(p: &SchedParams, n: u64, raw: &[RawReq]) -> Vec<Req> {
    raw.iter()
        .filter_map(|q| {
            let incs = incs_of(p, &q.bm);
            (!incs.is_empty()).then(|| Req {
                link: q.s * n + q.r,
                incs,
            })
        })
        .collect()
}

/// `ProcActualInput.allowances ids prev`: native lookup, the last record wins.
pub(crate) fn allowances(ids: &[u64], prev: &BwState) -> Vec<u64> {
    let n = ids.len() as u64;
    let mut a = vec![0u64; (n * n) as usize];
    for &(s, r, x) in &prev.links {
        if let (Some(s), Some(r)) = (index_of(ids, s), index_of(ids, r))
            && let Some(y) = a.get_mut((s * n + r) as usize)
        {
            *y = x;
        }
    }
    a
}

/// `a0Canon n prev`: the record allowances when there are exactly `n²` records, else zeros.
pub(crate) fn a0_canon(n: u64, prev: &BwState) -> Vec<u64> {
    if prev.links.len() as u64 == n * n {
        prev.links.iter().map(|l| l.2).collect()
    } else {
        vec![0; (n * n) as usize]
    }
}

/// `LinkPass`.
#[derive(Clone, Debug)]
pub struct LinkPass {
    pub a2: Vec<u64>,
    pub g2: Vec<u64>,
    pub sb: Vec<u64>,
    pub rb: Vec<u64>,
    pub cnt_s: Vec<u64>,
    pub cnt_r: Vec<u64>,
}

/// `linkPass n p allowed a0` (closed form).
pub fn link_pass(n: u64, p: &SchedParams, allowed: &[bool], a0: &[u64]) -> LinkPass {
    let nn = n * n;
    let fair = p.max_shard_bandwidth.checked_div(n).unwrap_or(0);
    let a1 = |l: u64| (at(a0, l) + fair).min(p.max_allowance);
    let al = |l: u64| al_at(allowed, l);
    let cnt_s: Vec<u64> = (0..n)
        .map(|s| (0..n).filter(|&r| al(s * n + r)).count() as u64)
        .collect();
    let cnt_r: Vec<u64> = (0..n)
        .map(|r| (0..n).filter(|&s| al(s * n + r)).count() as u64)
        .collect();
    LinkPass {
        a2: (0..nn)
            .map(|l| {
                if al(l) {
                    a1(l).saturating_sub(p.base)
                } else {
                    a1(l)
                }
            })
            .collect(),
        g2: (0..nn).map(|l| if al(l) { p.base } else { 0 }).collect(),
        sb: cnt_s
            .iter()
            .map(|c| p.max_shard_bandwidth.saturating_sub(p.base * c))
            .collect(),
        rb: cnt_r
            .iter()
            .map(|c| p.max_shard_bandwidth.saturating_sub(p.base * c))
            .collect(),
        cnt_s,
        cnt_r,
    }
}

// ---------------------------------------------------------------------------
// processEv (`Sched/Model.lean`)
// ---------------------------------------------------------------------------

/// `Push = (ts, key, z, v)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Push {
    ts: u64,
    key: u64,
    z: u64,
    v: u64,
}

/// `Step`.
#[derive(Clone, Debug)]
struct Step {
    t: u64,
    v: u64,
    link: u64,
    inc: u64,
    last: bool,
    ok: bool,
    a_out: u64,
}

/// `Round` (`kstart` is informational in Lean and unused here).
#[derive(Clone, Debug)]
struct Round {
    key: u64,
    z: u64,
    bucket: Vec<Push>,
    shuffled: Vec<u64>,
    steps: Vec<Step>,
}

/// The process state; the RNG is the word position `k` of the run-wide stream.
#[derive(Clone, Debug)]
struct St {
    sb: Vec<u64>,
    rb: Vec<u64>,
    al: Vec<u64>,
    g: Vec<u64>,
    k: u64,
}

fn set(a: &mut [u64], i: u64, x: u64) {
    if let Some(y) = a.get_mut(i as usize) {
        *y = x;
    }
}

/// `NearSpecV3.shuffle l rng` (`rand`'s `SliceRandom::shuffle`) on the stream from `k`.
fn shuffle(l: &mut [u64], stream: &mut Stream, k: &mut u64) -> Result<(), String> {
    let n = l.len();
    let mut i = n.saturating_sub(1);
    while i >= 1 {
        let (j, k2) = d0::gen_at(stream, (i + 1) as u64, *k).ok_or("shuffle fuel")?;
        *k = k2;
        l.swap(i, j as usize);
        i -= 1;
    }
    Ok(())
}

/// `processEv n allowed reqs st0 fuel`.
fn process_ev(
    n: u64,
    allowed: &[bool],
    reqs: &[Req],
    st0: St,
    stream: &mut Stream,
    fuel: usize,
) -> Result<(St, Vec<Round>), String> {
    let r_n = reqs.len() as u64;
    let mut pend: Vec<Push> = Vec::new();
    for (i, q) in reqs.iter().enumerate() {
        if q.incs.is_empty() {
            continue;
        }
        let k = at(&st0.al, q.link);
        pend.push(Push {
            ts: i as u64,
            key: k,
            z: u64::from(k == 0),
            v: i as u64 * 64,
        });
    }
    let mut st = st0;
    let mut t = r_n;
    let mut rounds = Vec::new();
    let mut last_key: Option<(u64, u64)> = None;
    for _ in 0..fuel {
        if pend.is_empty() {
            break;
        }
        let kk = pend.iter().map(|p| p.key).max().unwrap_or(0);
        // `sortTs`: stable insertion by `ts`
        let mut bucket: Vec<Push> = pend.iter().filter(|p| p.key == kk).copied().collect();
        bucket.sort_by_key(|p| p.ts);
        let z = bucket.first().map(|p| p.z).unwrap_or(0);
        chk(bucket.iter().all(|p| p.z == z), "bucket with mixed z")?;
        chk(!(kk == 0 && z == 0), "0-round with z = 0")?;
        chk(!(kk > 0 && z != 0), "positive round with z ≠ 0")?;
        if let Some((k2, z2)) = last_key {
            chk(
                kk < k2 || (kk == 0 && k2 == 0 && z == z2 + 1),
                &format!("round order: {k2},{z2} then {kk},{z}"),
            )?;
        }
        last_key = Some((kk, z));
        pend.retain(|p| p.key != kk);
        let mut sh: Vec<u64> = bucket.iter().map(|p| p.v).collect();
        shuffle(&mut sh, stream, &mut st.k)?;
        let mut steps = Vec::new();
        for &v in &sh {
            let rid = v / 64;
            let j = v % 64;
            let q = reqs.get(rid as usize).cloned().unwrap_or(Req {
                link: 0,
                incs: vec![],
            });
            let inc = at(&q.incs, j);
            let last = j + 1 == q.incs.len() as u64;
            let (s, r) = (q.link / n, q.link % n);
            let ok = al_at(allowed, q.link) && inc <= at(&st.sb, s) && inc <= at(&st.rb, r);
            if ok {
                let (a, b, c, d) = (
                    at(&st.sb, s) - inc,
                    at(&st.rb, r) - inc,
                    at(&st.al, q.link).saturating_sub(inc),
                    at(&st.g, q.link) + inc,
                );
                set(&mut st.sb, s, a);
                set(&mut st.rb, r, b);
                set(&mut st.al, q.link, c);
                set(&mut st.g, q.link, d);
            }
            let a_out = at(&st.al, q.link);
            if ok && !last {
                chk(
                    a_out < kk || (kk == 0 && a_out == 0),
                    "re-push to a key ≥ the popped key",
                )?;
                let z2 = if a_out == 0 {
                    if kk == 0 { z + 1 } else { 1 }
                } else {
                    0
                };
                pend.push(Push {
                    ts: t,
                    key: a_out,
                    z: z2,
                    v: v + 1,
                });
            }
            steps.push(Step {
                t,
                v,
                link: q.link,
                inc,
                last,
                ok,
                a_out,
            });
            t += 1;
        }
        rounds.push(Round {
            key: kk,
            z,
            bucket,
            shuffled: sh,
            steps,
        });
    }
    chk(pend.is_empty(), "out of fuel")?;
    Ok((st, rounds))
}

/// `Rng` after `k` words of the stream from `Rng.ofSeed seed` (`rngAt key k`):
/// `ctr = ⌈k/16⌉`, `buf` = the rest of block `ctr − 1`.
fn rng_at(key: &[u64], k: u64) -> Rng {
    let ctr = k.div_ceil(16);
    let buf = if ctr == 0 {
        vec![]
    } else {
        let blk = chacha_block(key, ctr - 1);
        blk[(k - 16 * (ctr - 1)) as usize..].to_vec()
    };
    Rng {
        key: key.to_vec(),
        ctr,
        buf,
    }
}

/// `leWords seed`.
fn le_words(seed: &[u8]) -> Vec<u64> {
    seed.chunks_exact(4)
        .map(|c| c[0] as u64 + 256 * c[1] as u64 + 65536 * c[2] as u64 + 16_777_216 * c[3] as u64)
        .collect()
}

/// `Gen.Input` (`ProcPreparedSequence.input sp prev`).
pub(crate) struct Input<'a> {
    pub ids: &'a [u64],
    pub p: &'a SchedParams,
    pub allowed: &'a [bool],
    pub raw: Vec<RawReq>,
    pub seed: &'a [u8],
    pub prev: &'a BwState,
}

fn params_of(p: &SchedParams) -> Params {
    Params {
        base: p.base,
        max_shard_bandwidth: p.max_shard_bandwidth,
        max_single_grant: p.max_single_grant,
        max_receipt_size: p.max_receipt_size,
        max_allowance: p.max_allowance,
    }
}

/// `Gen.ActualRun.run I tau` (without the redundant `coreEv` cross-check).
pub(crate) fn actual_run(inp: &Input, tau: u64) -> Result<Run, String> {
    let n = inp.ids.len() as u64;
    let p = inp.p;
    let nn = n * n;
    let lp = link_pass(n, p, inp.allowed, &allowances(inp.ids, inp.prev));
    let al = |l: u64| al_at(inp.allowed, l);
    // converted requests
    let mut conv: Vec<CReq> = Vec::new();
    for q in &inp.raw {
        let bits = set_bits(&q.bm);
        if bits.is_empty() {
            continue;
        }
        chk(q.bm.len() == 5, "bitmap length ≠ 5")?;
        chk(q.s < n && q.r < n, "shard index")?;
        let link = q.s * n + q.r;
        conv.push(CReq {
            cid: conv.len() as u64,
            s: q.s,
            r: q.r,
            link,
            bm: q.bm.iter().map(|&x| x as u64).collect(),
            bits,
            incs: incs_of(p, &q.bm),
            key: at(&lp.a2, link),
        });
    }
    let reqs = conv_raw(p, n, &inp.raw);
    chk(
        reqs == conv
            .iter()
            .map(|c| Req {
                link: c.link,
                incs: c.incs.clone(),
            })
            .collect::<Vec<_>>(),
        "convRaw differs",
    )?;
    let r_n = conv.len() as u64;
    chk(r_n < 65536, "too many requests")?;
    let key = le_words(inp.seed);
    let mut stream = Stream::of_seed(inp.seed);
    let st0 = St {
        sb: lp.sb.clone(),
        rb: lp.rb.clone(),
        al: lp.a2.clone(),
        g: lp.g2.clone(),
        k: 0,
    };
    let fuel = 1 + reqs.iter().map(|q| q.incs.len()).sum::<usize>();
    let (st_f, mrounds) = process_ev(n, inp.allowed, &reqs, st0, &mut stream, fuel)?;
    chk(key.len() == 8, "seed length")?;
    // replay
    let (mut sb, mut rb, mut aa, mut gg) =
        (lp.sb.clone(), lp.rb.clone(), lp.a2.clone(), lp.g2.clone());
    let mut ops_l: Vec<Vec<MOp>> = vec![vec![]; nn as usize];
    let mut ops_s: Vec<Vec<MOp>> = vec![vec![]; n as usize];
    let mut ops_r: Vec<Vec<MOp>> = vec![vec![]; n as usize];
    let mop = |t, op, vin, v, wp, w, inc, ok, c, sf| MOp {
        t,
        op,
        vin,
        v,
        wp,
        w,
        inc,
        ok,
        c,
        sf,
    };
    for c in &conv {
        let (v, w) = (at(&aa, c.link), at(&gg, c.link));
        if let Some(o) = ops_l.get_mut(c.link as usize) {
            o.push(mop(c.cid + 1, OP_READ, v, v, w, w, 0, false, false, false));
        }
    }
    let ts_of = |t: u64| if t < r_n { t } else { T0 + (t - r_n) };
    let mut pushes: Vec<(u64, u64, u64, u64)> = conv
        .iter()
        .map(|c| (c.cid, c.key, u64::from(c.key == 0), c.cid * 64))
        .collect();
    let mut buckets_all: Vec<(u64, u64, u64, u64)> = Vec::new();
    let mut t_cur = T0;
    let mut kpos = 0u64;
    let mut kq = KSENT;
    let mut zq = 0u64;
    let mut used: Vec<Vec<bool>> = conv.iter().map(|c| vec![false; c.incs.len()]).collect();
    let mut rounds: Vec<RoundD> = Vec::new();
    let mut gidx = 0u64;
    for rd in &mrounds {
        let l = rd.bucket.len() as u64;
        chk((1..16384).contains(&l), "bucket size")?;
        // `replayShuffle key kpos vals`
        let mut sh: Vec<u64> = rd.bucket.iter().map(|b| b.v).collect();
        let mut kend = kpos;
        for i in 0..l.saturating_sub(1) {
            let q = l - 1 - i;
            let (j, k2) = d0::gen_at(&mut stream, q + 1, kend).ok_or("genAt fuel")?;
            // `swapAt l q j` (a no-op out of range)
            if (j as usize) < sh.len() {
                sh.swap(q as usize, j as usize);
            }
            kend = k2;
        }
        chk(sh == rd.shuffled, "shuffle replay differs")?;
        chk(rd.steps.len() as u64 == l, "steps ≠ bucket")?;
        for b in &rd.bucket {
            chk(b.key == rd.key && b.z == rd.z, "bucket push key/z")?;
            buckets_all.push((ts_of(b.ts), b.key, b.z, b.v));
        }
        let mut ents: Vec<Entry> = Vec::new();
        for x in 0..l {
            let st = &rd.steps[x as usize];
            chk(st.t == r_n + gidx, "model time")?;
            let t = t_cur + x;
            let e = sh[x as usize];
            let (cid, j) = (e / 64, e % 64);
            chk(cid < r_n, "entry cid")?;
            let c = &conv[cid as usize];
            chk(j < c.incs.len() as u64, "entry j")?;
            used[cid as usize][j as usize] = true;
            let inc = c.incs[j as usize];
            let rem = c.incs.len() as u64 - j - 1;
            let (s, r, lk) = (c.s, c.r, c.link);
            let (sb_in, rb_in, al_in, w_in) = (at(&sb, s), at(&rb, r), at(&aa, lk), at(&gg, lk));
            let (c_s, c_r, c_l) = (inc <= sb_in, inc <= rb_in, al(lk));
            let ok = c_s && c_r && c_l;
            let sb_out = if ok { sb_in - inc } else { sb_in };
            let rb_out = if ok { rb_in - inc } else { rb_in };
            let al_out = if ok { al_in.saturating_sub(inc) } else { al_in };
            let w_out = if ok { w_in + inc } else { w_in };
            set(&mut sb, s, sb_out);
            set(&mut rb, r, rb_out);
            set(&mut aa, lk, al_out);
            set(&mut gg, lk, w_out);
            let sf_l = inc <= al_in;
            if let Some(o) = ops_s.get_mut(s as usize) {
                o.push(mop(t, OP_GRANT, sb_in, sb_out, 0, 0, inc, ok, c_s, c_s));
            }
            if let Some(o) = ops_r.get_mut(r as usize) {
                o.push(mop(t, OP_GRANT, rb_in, rb_out, 0, 0, inc, ok, c_r, c_r));
            }
            if let Some(o) = ops_l.get_mut(lk as usize) {
                o.push(mop(
                    t, OP_GRANT, al_in, al_out, w_in, w_out, inc, ok, c_l, sf_l,
                ));
            }
            chk(
                st.v == e
                    && st.link == lk
                    && st.inc == inc
                    && st.last == (rem == 0)
                    && st.ok == ok
                    && st.a_out == al_out,
                "step differs from processEv",
            )?;
            let push = ok && rem != 0;
            let zn = if al_out == 0 { rd.z + 1 } else { 0 };
            if push {
                pushes.push((t, al_out, zn, e + 1));
            }
            let bx = &rd.bucket[x as usize];
            ents.push(Entry {
                x,
                ts: ts_of(bx.ts),
                ein: bx.v,
                eout: e,
                inc,
                rem,
                s,
                r,
                link: lk,
                sb_in,
                sb_out,
                rb_in,
                rb_out,
                al_in,
                al_out,
                c_s,
                c_r,
                c_l,
                ok,
                push,
                zn,
            });
            gidx += 1;
        }
        rounds.push(RoundD {
            k: rd.key,
            z: rd.z,
            t: t_cur,
            lr: l,
            kst: kpos,
            kend,
            kq,
            zq,
            entries: ents,
        });
        t_cur += l;
        kpos = kend;
        kq = rd.key;
        zq = rd.z;
    }
    // every push is popped exactly once
    pushes.sort();
    buckets_all.sort();
    chk(pushes == buckets_all, "push log ≠ buckets")?;
    chk(
        sb == st_f.sb && rb == st_f.rb && aa == st_f.al && gg == st_f.g,
        "final state differs",
    )?;
    chk(kpos == st_f.k, "final RNG position differs")?;
    // memory segments
    let mut segs: Vec<Seg> = Vec::new();
    for l in 0..nn {
        let b = al(l);
        segs.push(Seg {
            addr: tau * 16384 + l,
            is_l: true,
            al: b,
            vin0: u64::from(b),
            v0: at(&lp.a2, l),
            w0: at(&lp.g2, l),
            ops: std::mem::take(&mut ops_l[l as usize]),
        });
    }
    for s in 0..n {
        segs.push(Seg {
            addr: tau * 16384 + 4096 + s,
            is_l: false,
            al: false,
            vin0: 0,
            v0: at(&lp.sb, s),
            w0: 0,
            ops: std::mem::take(&mut ops_s[s as usize]),
        });
    }
    for r in 0..n {
        segs.push(Seg {
            addr: tau * 16384 + 2 * 4096 + r,
            is_l: false,
            al: false,
            vin0: 0,
            v0: at(&lp.rb, r),
            w0: 0,
            ops: std::mem::take(&mut ops_r[r as usize]),
        });
    }
    // comparator messages
    let cmp_of = |x: u64, y: u64| (x, y, u64::from(y <= x));
    let mut cmps: Vec<(u64, u64, u64)> = Vec::new();
    for g in &segs {
        let mut tp = 0u64;
        for o in &g.ops {
            chk(tp < o.t, "memory times not increasing")?;
            cmps.push(cmp_of(o.t, tp + 1));
            if o.op == OP_GRANT {
                cmps.push(cmp_of(o.vin, o.inc));
            }
            tp = o.t;
        }
    }
    for rd in &rounds {
        if rd.k != 0 {
            chk(rd.k < rd.kq, "round keys not decreasing")?;
            cmps.push(cmp_of(rd.kq, rd.k + 1));
        }
        let es = &rd.entries;
        for i in 0..es.len() {
            let cx = if i + 1 == es.len() {
                rd.t
            } else {
                es[i + 1].ts
            };
            chk(es[i].ts < cx, "bucket ts order")?;
            cmps.push(cmp_of(cx, es[i].ts + 1));
        }
    }
    chk(
        cmps.iter().all(|&(x, y, _)| x < 1 << 29 && y < 1 << 29),
        "comparison operand ≥ 2^29",
    )?;
    let d = p.max_single_grant.saturating_sub(p.base);
    chk(p.base < 1 << 24 && d < 1 << 24, "params ≥ 2^24")?;
    Ok(Run {
        tau,
        n,
        base: p.base,
        d,
        seed: inp.seed.iter().map(|&x| x as u64).collect(),
        key: key.clone(),
        a2: lp.a2.clone(),
        conv,
        used,
        rounds,
        segs,
        cmps,
        kfin: kpos,
        fin: PState {
            sb: st_f.sb,
            rb: st_f.rb,
            al: st_f.al,
            g: st_f.g,
            rng: rng_at(&key, st_f.k),
        },
    })
}

/// `distributeEv n allowed sb rb cntS cntR`: the grid grants (`break` = error).
pub fn distribute_ev(
    n: u64,
    allowed: &[bool],
    sb: &[u64],
    rb: &[u64],
    cnt_s: &[u64],
    cnt_r: &[u64],
) -> Result<Vec<u64>, String> {
    let avg = |links: u64, left: u64| left.checked_div(links).unwrap_or(0);
    let sord = sc::sort_by_key(|s| avg(at(cnt_s, s), at(sb, s)), n);
    let rord = sc::sort_by_key(|r| avg(at(cnt_r, r), at(rb, r)), n);
    let mut ri: Vec<(u64, u64)> = (0..n).map(|r| (at(cnt_r, r), at(rb, r))).collect();
    let mut g = vec![0u64; (n * n) as usize];
    for &s in &sord {
        let mut se = (at(cnt_s, s), at(sb, s));
        for &r in &rord {
            let l = s * n + r;
            if al_at(allowed, l) {
                let re = ri[r as usize];
                chk(se.0 != 0 && re.0 != 0, "distribute break")?;
                let gb = (se.1 / se.0).min(re.1 / re.0);
                g[l as usize] = gb;
                se = (se.0 - 1, se.1 - gb);
                ri[r as usize] = (re.0 - 1, re.1 - gb);
            }
        }
    }
    Ok(g)
}

// ---------------------------------------------------------------------------
// The blocks
// ---------------------------------------------------------------------------

/// `forestLookupVid before = |forestBytes before|`.
fn forest_vid(before: &[&PTrie]) -> u64 {
    before.iter().map(|t| vals_of(t).len() as u64).sum()
}

/// `nativePriorIds trees τ = priorValueId (trees.take τ) trees[τ]`.
fn prior_vid(trees: &[&PTrie], tau: usize) -> u64 {
    match value_index(trees[tau], &key_bw_state()) {
        None => 0,
        Some(i) => forest_vid(&trees[..tau]) + i as u64,
    }
}

/// One `PriorCore` block (`native_main_block` / `native_missing_block`), as `SchedIn`.
fn block(
    sp_tau: Option<&SchedPub>,
    sp_ctx: Option<SchedPub>,
    pre: &PTrie,
    trees: &[&PTrie],
    tau: usize,
    fwd: Vec<(u64, u64)>,
) -> Result<SchedIn, String> {
    let sp = sp_tau.ok_or_else(|| format!("block {tau}: no prepared scheduler instance"))?;
    chk(
        sp_ctx.as_ref() == Some(sp),
        &format!("block {tau}: schedPub ctx ≠ p.sched[τ]"),
    )?;
    let prior = find(pre, &key_bw_state())
        .ok_or_else(|| "invalid: MissingTrieValue (bandwidth scheduler state)".to_string())?;
    let prev = match &prior {
        None => BwState {
            links: vec![],
            sanity_hash: vec![0u8; 32],
        },
        Some(b) => {
            decode_state(b).ok_or_else(|| format!("block {tau}: prior state does not decode"))?
        }
    };
    let inp = Input {
        ids: &sp.ids,
        p: &sp.params,
        allowed: &sp.allowed,
        raw: inst_raw(sp),
        seed: &sp.seed,
        prev: &prev,
    };
    let run = actual_run(&inp, tau as u64).map_err(|e| format!("block {tau}: {e}"))?;
    let n = sp.ids.len() as u64;
    let lp = link_pass(n, &sp.params, &sp.allowed, &allowances(&sp.ids, &prev));
    let gd = distribute_ev(
        n,
        &sp.allowed,
        &run.fin.sb,
        &run.fin.rb,
        &lp.cnt_s,
        &lp.cnt_r,
    )
    .map_err(|e| format!("block {tau}: {e}"))?;
    // The `SchedIn` view keeps the prior state as `a0 = a0Canon n prev` + the sanity hash and
    // rebuilds it canonically (record `l` = link `l`); tables 11–15 read the prior state
    // through `a0Canon` and `allowances ids prev`, so the view is exact iff the rebuild has
    // the same `allowances` (the `np-lean-sched-v3` summary check).  Refuse otherwise.
    let a0 = a0_canon(run.n, &prev);
    if prior.is_some() {
        let nn = sp.ids.len();
        let rebuilt = BwState {
            links: (0..a0.len())
                .map(|l| (sp.ids[l / nn], sp.ids[l % nn], a0[l]))
                .collect(),
            sanity_hash: prev.sanity_hash.clone(),
        };
        chk(
            allowances(&sp.ids, &rebuilt) == allowances(&sp.ids, &prev),
            &format!(
                "block {tau}: prior state is not canonical (the SchedIn view cannot carry it)"
            ),
        )?;
    }
    Ok(SchedIn {
        ids: sp.ids.clone(),
        allowed: sp.allowed.clone(),
        params: params_of(&sp.params),
        present: prior.is_some(),
        vid: prior_vid(trees, tau),
        gb: gd,
        fwd,
        ash: sp.all_shards_hash.iter().map(|&x| x as u64).collect(),
        a0,
        prev_hash: prev.sanity_hash.iter().map(|&x| x as u64).collect(),
        run,
    })
}

// ---------------------------------------------------------------------------
// qv (table 22)
// ---------------------------------------------------------------------------

/// `ParseMode`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Mode {
    Empty,
    Buffered,
    Raw,
}

/// `ReadRequest` (key nibbles, value, mode).
struct ReadReq {
    key: Vec<u8>,
    value: Option<Bytes>,
    mode: Mode,
}

/// `pre.find key` with an undetermined path read as absent (`getD none`).
fn find_or_none(t: &PTrie, key: &[u8]) -> Option<Bytes> {
    find(t, key).unwrap_or(None)
}

/// `mainRequests pre v`.
fn main_requests(pre: &PTrie, v: &MainValues) -> Vec<ReadReq> {
    let mut rs = vec![
        ReadReq {
            key: key_delayed_idx(),
            value: v.delayed.clone(),
            mode: Mode::Empty,
        },
        ReadReq {
            key: key_buffered_idx(),
            value: v.buffered.clone(),
            mode: Mode::Buffered,
        },
        ReadReq {
            key: key_yield_idx(),
            value: v.yielded.clone(),
            mode: Mode::Empty,
        },
    ];
    for &s in &v.shards {
        rs.push(ReadReq {
            key: key_groups_data(s),
            value: find_or_none(pre, &key_groups_data(s)),
            mode: Mode::Raw,
        });
    }
    rs
}

/// `missingRequest pre`.
fn missing_request(pre: &PTrie) -> ReadReq {
    ReadReq {
        key: key_delayed_idx(),
        value: find_or_none(pre, &key_delayed_idx()),
        mode: Mode::Raw,
    }
}

/// `queueUsers pre rs i`.
fn queue_users(pre: &PTrie, rs: &[ReadReq], i: usize) -> u64 {
    rs.iter()
        .filter(|r| value_index(pre, &r.key) == Some(i))
        .count() as u64
}

/// `queuePayload mode bytes` as a `QvRecIn` payload (`rkind`, `index`, `entries`, `bytes`).
fn payload(mode: &Mode, bytes: &[u8], rec: &mut QvRecIn) {
    let nat = |b: &[u8]| b.iter().map(|&x| x as u64).collect::<Vec<u64>>();
    match mode {
        Mode::Empty => {
            rec.rkind = 0;
            rec.index = nat(&bytes[..bytes.len().min(8)]);
        }
        Mode::Buffered => {
            rec.rkind = 1;
            // `pVec "shard_buffers" bufferEntryParser bytes` (trailing bytes ignored),
            // `.error → .buffer []`
            let rd = |at: usize| -> Option<u64> {
                Some(u64::from_le_bytes(bytes.get(at..at + 8)?.try_into().ok()?))
            };
            let parsed = (|| -> Option<Vec<QvItem>> {
                let n = u32::from_le_bytes(bytes.get(0..4)?.try_into().ok()?) as usize;
                let mut out = Vec::new();
                for i in 0..n {
                    let at0 = 4 + 24 * i;
                    let (s, f, _) = (rd(at0)?, rd(at0 + 8)?, rd(at0 + 16)?);
                    out.push(QvItem {
                        shard: nat(&u64b(s as u128)),
                        index: nat(&u64b(f as u128)),
                    });
                }
                Some(out)
            })();
            rec.entries = parsed.unwrap_or_default();
        }
        Mode::Raw => {
            rec.rkind = 2;
            rec.bytes = nat(bytes);
        }
    }
}

/// The qv entries: `{walks = plan pre v pres resolve, records = queueRecords …}`.
pub fn qv_entries(pre: &PTrie, v: &MainValues, pres: &[&PTrie]) -> QvIn {
    let nat = |b: &[u8]| b.iter().map(|&x| x as u64).collect::<Vec<u64>>();
    // `queueInputs pre v pres`
    let mut inputs: Vec<(&PTrie, Vec<ReadReq>)> = vec![(pre, main_requests(pre, v))];
    for t in pres {
        inputs.push((t, vec![missing_request(t)]));
    }
    let trees: Vec<&PTrie> = inputs.iter().map(|x| x.0).collect();
    // `NativeQueueIds.resolve pre v pres tau slot`
    let resolve = |tau: usize, slot: usize| -> (u64, u64) {
        let Some((tree, rs)) = inputs.get(tau) else {
            return (0, 0);
        };
        let key: &[u8] = rs.get(slot).map(|r| r.key.as_slice()).unwrap_or(&[]);
        match value_index(tree, key) {
            Some(i) => (
                forest_vid(&trees[..tau]) + i as u64,
                queue_users(tree, &rs[..slot.min(rs.len())], i),
            ),
            None => (0, 0),
        }
    };
    let k = pres.len();
    let ns = v.shards.len();
    let mut walks = Vec::new();
    let main_walk = |code: u64, shard: u64, slot: usize, value: Option<Bytes>| {
        let last = slot + 1 == 3 + ns;
        let (vid, users) = resolve(0, slot);
        QvWalkIn {
            code,
            shard,
            tau: 0,
            slot: slot as u64,
            count: ns as u64,
            value: value.map(|b| nat(&b)),
            vid,
            users,
            last_main: last,
            fin: last && k == 0,
        }
    };
    walks.push(main_walk(0, 0, 0, v.delayed.clone()));
    walks.push(main_walk(1, 0, 1, v.buffered.clone()));
    walks.push(main_walk(2, 0, 2, v.yielded.clone()));
    for (i, &s) in v.shards.iter().enumerate() {
        walks.push(main_walk(
            3,
            s,
            3 + i,
            find_or_none(pre, &key_groups_data(s)),
        ));
    }
    for (i, t) in pres.iter().enumerate() {
        let (vid, users) = resolve(i + 1, 0);
        walks.push(QvWalkIn {
            code: 0,
            shard: 0,
            tau: i as u64 + 1,
            slot: 0,
            count: 0,
            value: missing_request(t).value.map(|b| nat(&b)),
            vid,
            users,
            last_main: false,
            fin: i + 1 == k,
        });
    }
    // `queueForestProviders 0 0 inputs`, `queueRecords`
    let mut records = Vec::new();
    let mut base = 0u64;
    for (tau, (tree, rs)) in inputs.iter().enumerate() {
        let vals = vals_of(tree);
        for (i, b) in vals.iter().enumerate() {
            let reps: Vec<&ReadReq> = rs
                .iter()
                .filter(|r| value_index(tree, &r.key) == Some(i))
                .collect();
            let Some(first) = reps.first() else { continue };
            let mut rec = QvRecIn {
                rkind: 0,
                vid: base + i as u64,
                tau: tau as u64,
                users: reps.len() as u64,
                index: vec![],
                entries: vec![],
                bytes: vec![],
            };
            payload(&first.mode, b, &mut rec);
            records.push(rec);
        }
        base += vals.len() as u64;
    }
    QvIn { walks, records }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

/// The honest entries of tables 8–15 and 22.
pub struct SchedQv {
    /// tables 11–15: one block per scheduler call
    pub blocks: Vec<SchedIn>,
    /// table 22
    pub qv: QvIn,
}

/// `npudr v3sched`: the entries from a claim + witness.
pub fn derive(cb: &[u8], wb: &[u8]) -> Result<SchedQv, String> {
    let n = native::native_of(cb, wb)?;
    let k = walk_d0(cb)?;
    let w = decode_w(wb)?;
    let hint = hint_of_e(cb, wb)?;
    let p = d0::prep(cb, &hint)?;
    let b2 = k.blks.get(k.b2i).ok_or("walk: B2")?;
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("walk: prev B2")?;
    let own = k.h_chunk.shard_id;
    let gl = k.slot_b2.gas_limit;
    let mut ctxs = vec![block_ctx(
        &k.layout,
        own,
        gl,
        b2,
        prev_b2.hdr.next_gas_price,
    )];
    for b in k.implicit_blks.iter().take(w.implicit.len()) {
        ctxs.push(block_ctx(&k.layout, own, gl, b, b.hdr.next_gas_price));
    }
    let mut trees: Vec<&PTrie> = vec![&n.pre];
    trees.extend(n.steps.iter().map(|s| &s.pre));
    chk(trees.len() == ctxs.len(), "implicit step count")?;
    let mut blocks = Vec::new();
    for (tau, (ctx, pre)) in ctxs.iter().zip(&trees).enumerate() {
        let sp_ctx = d0::sched_pub(
            &ctx.layout.shard_ids,
            &ctx.statuses,
            &ctx.requests,
            &ctx.prev_block_hash,
        );
        let fwd = if tau == 0 { p.fwd.clone() } else { vec![] };
        blocks.push(block(p.sched.get(tau), sp_ctx, pre, &trees, tau, fwd)?);
    }
    let v = crate::v3::walks::main_values(&n)?;
    let qv = qv_entries(&n.pre, &v, &trees[1..]);
    Ok(SchedQv { blocks, qv })
}

/// Re-derive a block's run and grid grants from its input fields (the sampler
/// differential, `npudr v3sched --rerun`): ids, params, allowed, the raw requests
/// `(s, r, bm)` of `run.conv` (requests without a set bit never reach a run), seed
/// `run.seed`, and the canonical prior state (`a0`, `prev_hash`; `State.initial` when
/// absent).  The output keeps every other field of `b`.
pub fn rerun(b: &SchedIn) -> Result<SchedIn, String> {
    let n = b.ids.len();
    let prev = if b.present {
        BwState {
            links: (0..b.a0.len())
                .map(|l| {
                    (
                        at(&b.ids, (l / n) as u64),
                        at(&b.ids, (l % n) as u64),
                        b.a0[l],
                    )
                })
                .collect(),
            sanity_hash: b.prev_hash.iter().map(|&x| x as u8).collect(),
        }
    } else {
        BwState {
            links: vec![],
            sanity_hash: vec![0u8; 32],
        }
    };
    let sp = SchedParams {
        base: b.params.base,
        max_shard_bandwidth: b.params.max_shard_bandwidth,
        max_single_grant: b.params.max_single_grant,
        max_receipt_size: b.params.max_receipt_size,
        max_allowance: b.params.max_allowance,
    };
    let seed: Vec<u8> = b.run.seed.iter().map(|&x| x as u8).collect();
    let raw: Vec<RawReq> = b
        .run
        .conv
        .iter()
        .map(|c| RawReq {
            s: c.s,
            r: c.r,
            bm: c.bm.iter().map(|&x| x as u8).collect(),
        })
        .collect();
    let inp = Input {
        ids: &b.ids,
        p: &sp,
        allowed: &b.allowed,
        raw,
        seed: &seed,
        prev: &prev,
    };
    let run = actual_run(&inp, b.run.tau)?;
    let lp = link_pass(n as u64, &sp, &b.allowed, &allowances(&b.ids, &prev));
    let gb = distribute_ev(
        n as u64,
        &b.allowed,
        &run.fin.sb,
        &run.fin.rb,
        &lp.cnt_s,
        &lp.cnt_r,
    )?;
    Ok(SchedIn {
        run,
        gb,
        ..b.clone()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rng_after_k_words() {
        let key: Vec<u64> = (1..=8).collect();
        assert_eq!(rng_at(&key, 0).ctr, 0);
        assert!(rng_at(&key, 0).buf.is_empty());
        let r = rng_at(&key, 1);
        assert_eq!((r.ctr, r.buf.len()), (1, 15));
        assert_eq!(r.buf[0], chacha_block(&key, 0)[1]);
        let r = rng_at(&key, 16);
        assert_eq!((r.ctr, r.buf.len()), (1, 0));
        let r = rng_at(&key, 17);
        assert_eq!((r.ctr, r.buf.len()), (2, 15));
    }

    #[test]
    fn incs_skip_unset() {
        let p = SchedParams {
            base: 100,
            max_shard_bandwidth: 4_500_000,
            max_single_grant: 4100,
            max_receipt_size: 0,
            max_allowance: 4_500_000,
        };
        // values: 100 + 4000 (i + 1) / 40 = 200, 300, …; bits 0 and 2
        assert_eq!(incs_of(&p, &[0b101, 0, 0, 0, 0]), vec![100, 200]);
        assert!(incs_of(&p, &[0; 5]).is_empty());
    }

    #[test]
    fn distribute_splits_evenly() {
        // 2 shards, all links allowed, budgets 10 / 10
        let g = distribute_ev(2, &[true; 4], &[10, 10], &[10, 10], &[2, 2], &[2, 2]).unwrap();
        assert_eq!(g, vec![5, 5, 5, 5]);
        assert!(distribute_ev(1, &[true], &[1], &[1], &[0], &[1]).is_err());
    }
}
