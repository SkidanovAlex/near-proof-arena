//! Receipt-side table entries from a real claim + witness: the Rust twin of the
//! accepted receipt-side renders (`Assembly/RenderV3RcptAccepted.lean`,
//! `RenderV3RcptSide.lean` `A.rcptRenders`, `RenderV3RcptSha.lean` `mrkAcc`,
//! `Render/CompleteV3.lean` table 24), so that `npudr` builds tables 16–20, 23,
//! 24 and the receipt SHA family without any Lean dump.
//!
//! From `cb`/`wb` it re-runs the native preprocessing (`walkD0`, `decodeW`,
//! `appliedReceipts`, the main pre-trie `m.pre = partialTrie … (mainKeys …)`,
//! `hintOf`, `prepD0`) and the receipt ledger (`TransferV1.applyReceipt` /
//! `applySystemReceipt` in order, `RcptSkeleton.nativeDepositLedger`), then:
//!
//! | output | Lean (accepted render) |
//! |---|---|
//! | `rcpt` ([`RcptIn`]) | `AcceptedV3.rcptInput`, read as the list view `nativeRcptLists` (`ListBlock.view (rcptTraceNative pub x)`) + native routing interval, see [`rcpt_view`] |
//! | `acct` | `AcceptedV3.accts` = `nativeAccountViews m.pre oldPost rs` |
//! | `akey` | `AcceptedV3.akeys` = `NativeAccessKeyProviders.providers m.pre rs` |
//! | `bnd` | `AcceptedV3.bnds` = `boundaryEntries (boundedIntervals L own) (physicalBoundaryKeys tN 0)` |
//! | `srcp` | `AcceptedV3.ddBlocks` = `DedupCompile.blocks p.lists w.entries` + `rep = sourceRepeated` |
//! | `mrk` | `mrkAcc`: `n`, `levels = mrkLevels m.result.outcomes` (and the `MrkV` of those levels) |
//! | `sort` | `sortRenderV3 … A.rcptInput.lists`: `NativeSortIds.sorted rs` |
//!
//! **The receipt view** (`RcptE`, `Rcpt/Extract/V/Of.lean` `rcptOf`) is read by
//! Lean from the rows of the native receipt trace; here every field is the
//! native value the row constructors write (`completeReceiptConstants`,
//! `completeReceiptAux`, `depositFinalAux`, `nativeDigests`):
//! `kslot` = `nativeAccountId` (`accountSlot`: the receiver account's
//! `valueIndex` in `m.pre`), `tprev` = `depositPlanPrevious`
//! (`latestReceiverVersion`), `bef`/`lk`/`st`/`aft` = the `Seg` bytes of
//! `nativeDepositData` (account read by the ledger), `ge` (`nativePriceConstants`),
//! `sys`/`ee` (`systemConstants`/`systemIdentityConstants`), `gv`/`gs`/`sx`
//! (`systemAux`), `rfid` (`refundDigests`: `gasRefundReceipt … nativeSurplus`),
//! `peoh` (`outcomeDigests`: `sha256 (nativeOutcome ctx r).partialEncode`),
//! `burnt` / `ramt` (`nativeOutcome.tokensBurnt` / the refund amount),
//! `akf`/`akk` (`keyAux`: `NativeReceiptAccessIds.accessId`), `aku`
//! (`NativeAccessKeyRanks.rankAux`), `q` (`nativeRoutingConstants`:
//! `nativeRoutingIndex`), `rlk` (the routing frame `frameOf` rows with
//! `gBd = equalLower ∨ equalUpper`; `u` = the native `uB`, i.e. `0`, as the
//! view is read before `counterPatch`), `iv` = `nativeRoutingInterval`.
//!
//! **Deviation notes (not mechanised; covered by the differential
//! `conformance/run-v2.d/rcptfam.sh` against `np-lean-rcptfam-v3`).**
//! * The ledger runs on `m.pre`, not on the post-`schedStep` trie Lean's
//!   `RcptInput.steps` uses: `schedStep` upserts only `keyBwState = [0, 15]`,
//!   which no receipt reads (same argument as `hint.rs`, `PTrie.find_upsert_other`).
//! * `valsOf oldPost` at an account's value index is the receiver's final
//!   account bytes (`oldPost` = `m.pre` with one `set` per applied receipt of the
//!   final bytes).
//! * Lean's `checkD0a` is not re-run here; on a non-accepted pair the outputs are
//!   whatever the native functions produce (or an error).

use crate::near::reexec::sha256;
use crate::near::spec::{
    self as ns, Account, Bytes, Outcome, PTrie, Receipt, Slot, account_key_path,
    gas_refund_receipt, params, u64b, u128b,
};
use crate::v3::collect::{K_LEAF, K_MRK, msg_id};
use crate::v3::d0::{self, Layout, block_ctx, lex_le, own_intervals, walk_d0};
use crate::v3::hint::{
    Acc, ProofEntry, applied_receipts, apply_receipt, apply_system_receipt, buffered_shards,
    decode_w, find, get, hint_of_e, key_access_key, key_buffered_idx, lookup_last, main_keys,
    partial_trie,
};
use crate::v3::mrksort::{MNode, MrkV, mrk_from_levels, qbase};
use crate::v3::prep::SrcList;
use crate::v3::rcpt::{Iv, ListV3, RcptE, RcptIn, Rlk};
use crate::v3::srcp::{SrcpB, SrcpItem};
use crate::v3::{AkeyE, BndE, acct::AcctV};

fn nats(b: &[u8]) -> Vec<u64> {
    b.iter().map(|&x| x as u64).collect()
}

/// `leBytes n x` as naturals (`x` truncated to `n` bytes).
fn le_n(x: u128, n: usize) -> Vec<u64> {
    nats(&u128b(x)[..n])
}

// ---------------------------------------------------------------------------
// Partial-trie value ordinals (`NearSpecV3.valsOf`, `Assembly/ValueIndex.lean`)
// ---------------------------------------------------------------------------

fn slot_val(s: &Slot) -> Option<&Bytes> {
    match s {
        Slot::Val(v) => Some(v),
        Slot::Ref(..) => None,
    }
}

/// `valsOf t`: the revealed values in pre-order (`occs t` then `ownVals`).
pub fn vals_of(t: &PTrie) -> Vec<Bytes> {
    let mut out = Vec::new();
    vals_into(t, &mut out);
    out
}

fn vals_into(t: &PTrie, out: &mut Vec<Bytes>) {
    match t {
        PTrie::Hash(_) => {}
        PTrie::Leaf(_, s, _) => out.extend(slot_val(s).cloned()),
        PTrie::Ext(_, c, _) => vals_into(c, out),
        PTrie::Branch(v, cs, _) => {
            out.extend(v.as_ref().and_then(slot_val).cloned());
            for c in cs.iter().flatten() {
                vals_into(c, out);
            }
        }
    }
}

fn vals_len(t: &PTrie) -> usize {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(_, s, _) => slot_val(s).is_some() as usize,
        PTrie::Ext(_, c, _) => vals_len(c),
        PTrie::Branch(v, cs, _) => {
            v.as_ref().and_then(slot_val).is_some() as usize
                + cs.iter().flatten().map(vals_len).sum::<usize>()
        }
    }
}

/// `valueIndex t key`: the ordinal of `key`'s revealed value in `valsOf t`.
pub fn value_index(t: &PTrie, key: &[u8]) -> Option<usize> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, s, _) => (k.as_slice() == key && slot_val(s).is_some()).then_some(0),
        PTrie::Ext(k, c, _) => {
            if key.starts_with(k) {
                value_index(c, &key[k.len()..])
            } else {
                None
            }
        }
        PTrie::Branch(v, cs, _) => match key.split_first() {
            None => v.as_ref().and_then(slot_val).map(|_| 0),
            Some((&n, rest)) => {
                // `kidValueIndex cs n rest`, offset by the node's own value
                let own = v.as_ref().and_then(slot_val).is_some() as usize;
                let n = n as usize;
                let c = cs.get(n)?.as_ref()?;
                let before: usize = cs[..n].iter().flatten().map(vals_len).sum();
                value_index(c, rest).map(|i| own + before + i)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Receipt-level native functions (`RcptNativeFlags`, `RcptNativeOutcomes`,
// `RcptSystemIdentity`, `RcptSystemFrame`, `RoutingSelection`)
// ---------------------------------------------------------------------------

fn is_sys(r: &Receipt) -> bool {
    r.predecessor_id == ns::SYSTEM
}

/// `nativeSurplus ctx r = G · (gasPrice − min gasPrice ctx.gasPrice)`.
fn native_surplus(bgp: u128, r: &Receipt) -> u128 {
    params::G.wrapping_mul(r.gas_price - r.gas_price.min(bgp))
}

/// `nativeRefund ctx r`.
pub fn native_refund(bgp: u128, r: &Receipt) -> bool {
    !is_sys(r) && native_surplus(bgp, r) != 0
}

/// `systemEqual r`.
fn system_equal(r: &Receipt) -> bool {
    is_sys(r) && r.signer_id == r.receiver_id
}

/// `systemMismatch r`.
fn system_mismatch(r: &Receipt) -> bool {
    is_sys(r) && !system_equal(r) && r.signer_id.len() == r.receiver_id.len()
}

/// `firstMismatch as bs`.
fn first_mismatch(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b).take_while(|(x, y)| x == y).count()
}

/// `systemLookup r i`.
fn system_lookup(r: &Receipt, i: usize) -> bool {
    system_equal(r) || (system_mismatch(r) && i == first_mismatch(&r.signer_id, &r.receiver_id))
}

/// `nativeOutcome ctx r`.
pub fn native_outcome(height: u64, bgp: u128, r: &Receipt) -> Outcome {
    let refund = native_refund(bgp, r);
    Outcome {
        id: r.receipt_id.clone(),
        receipt_ids: if refund {
            vec![gas_refund_receipt(r, height as u128, native_surplus(bgp, r)).receipt_id]
        } else {
            vec![]
        },
        gas_burnt: params::G,
        tokens_burnt: if is_sys(r) {
            0
        } else {
            params::G.wrapping_mul(r.gas_price.min(bgp))
        },
        executor_id: r.receiver_id.clone(),
    }
}

/// `inInterval a iv`.
fn in_interval(a: &[u8], iv: &(Option<Bytes>, Option<Bytes>)) -> bool {
    iv.0.as_ref().is_none_or(|lo| lex_le(lo, a)) && iv.1.as_ref().is_none_or(|hi| !lex_le(hi, a))
}

/// `boundedIntervals l own = ownIntervals (boundedLayout l) own`.
pub fn bounded_intervals(l: &Layout, own: u64) -> Vec<(Option<Bytes>, Option<Bytes>)> {
    let bl = Layout {
        boundaries: l
            .boundaries
            .iter()
            .take(l.shard_ids.len())
            .cloned()
            .collect(),
        ..l.clone()
    };
    own_intervals(&bl, own)
}

/// `nativeRoutingIndex k r = (selectInterval k.L own r.receiverId).getD 0`.
fn routing_index(bounds: &[(Option<Bytes>, Option<Bytes>)], acct: &[u8]) -> usize {
    bounds
        .iter()
        .position(|iv| in_interval(acct, iv))
        .unwrap_or(0)
}

/// `samePrefix a b n`.
fn same_prefix(a: &[u8], b: &[u8], n: usize) -> bool {
    (0..n).all(|i| a.get(i).copied().unwrap_or(0) == b.get(i).copied().unwrap_or(0))
}

fn get_d(b: &[u8], i: usize) -> u64 {
    b.get(i).copied().unwrap_or(0) as u64
}

// ---------------------------------------------------------------------------
// Native run
// ---------------------------------------------------------------------------

/// The native objects the receipt side is made of.
pub struct Native {
    pub own: u64,
    pub height: u64,
    pub bgp: u128,
    pub layout: Layout,
    /// `p.lists` (the prepared source lists, applied order)
    pub sources: Vec<SrcList>,
    pub entries: Vec<ProofEntry>,
    /// `sourceInputLists ctx p.lists w.entries`: `(receipt, refund flag)`
    pub lists: Vec<Vec<(Receipt, bool)>>,
    /// `m.pre`
    pub pre: PTrie,
    /// the receiver account each receipt reads (`depositPlanAccount steps`)
    pub accounts: Vec<Account>,
    /// the trie after the last receipt (account values = `valsOf oldPost`)
    pub post: PTrie,
}

impl Native {
    pub fn rs(&self) -> Vec<&Receipt> {
        self.lists.iter().flatten().map(|x| &x.0).collect()
    }
}

/// Re-run the native preprocessing and the receipt ledger of `cb`/`wb`.
pub fn native(cb: &[u8], wb: &[u8]) -> Result<Native, String> {
    let k = walk_d0(cb)?;
    let w = decode_w(wb)?;
    let b2 = k.blks.get(k.b2i).ok_or("walk: B2")?;
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("walk: prev B2")?;
    let own = k.h_chunk.shard_id;
    let ctx = block_ctx(
        &k.layout,
        own,
        k.slot_b2.gas_limit,
        b2,
        prev_b2.hdr.next_gas_price,
    );
    let applied = applied_receipts(&k, &w);
    let root = &k.slot_b2.prev_state_root;
    let t0 = partial_trie(&w.main.values, root, &[key_buffered_idx()]);
    let bv = find(&t0, &key_buffered_idx()).ok_or("missing buffered index")?;
    let bshards = buffered_shards(bv.as_deref())?;
    let pre = partial_trie(&w.main.values, root, &main_keys(&applied, &bshards));
    let hint = hint_of_e(cb, wb)?;
    let p = d0::prep(cb, &hint)?;
    let lists: Vec<Vec<(Receipt, bool)>> = p
        .lists
        .iter()
        .map(|s| {
            lookup_last(&s.key, &w.entries)
                .map(|e| e.receipts.clone())
                .unwrap_or_default()
                .into_iter()
                .map(|r| {
                    let f = native_refund(ctx.gas_price, &r);
                    (r, f)
                })
                .collect()
        })
        .collect();
    let rs: Vec<&Receipt> = lists.iter().flatten().map(|x| &x.0).collect();
    if rs.len() != applied.len() || rs.iter().zip(&applied).any(|(a, b)| *a != b) {
        return Err("source lists do not flatten to the applied receipts".into());
    }
    // the deposit ledger
    let mut acc = Acc {
        trie: pre.clone(),
        refunds: vec![],
        tokens_burnt: 0,
    };
    let mut accounts = Vec::with_capacity(rs.len());
    for (i, r) in rs.iter().enumerate() {
        let a = get(&acc.trie, &account_key_path(&r.receiver_id))
            .and_then(|b| Account::decode(&b))
            .ok_or_else(|| format!("receipt {i}: receiver account unreadable"))?;
        accounts.push(a);
        let ok = if is_sys(r) {
            apply_system_receipt(&mut acc, r)
        } else {
            apply_receipt(ctx.height, ctx.gas_price, &mut acc, r)
        };
        if !ok {
            return Err(format!("receipt {i}: native application failed"));
        }
    }
    Ok(Native {
        own,
        height: ctx.height,
        bgp: ctx.gas_price,
        layout: k.layout.clone(),
        sources: p.lists.clone(),
        entries: w.entries.clone(),
        lists,
        pre,
        accounts,
        post: acc.trie,
    })
}

// ---------------------------------------------------------------------------
// Table 16: the receipt view
// ---------------------------------------------------------------------------

/// The `rlk` rows of one receipt: receiver positions `0 … |v|` (`|v|` = the
/// first `RID` row) whose routing frame has `gBd = 1`, without the rank `u`.
fn routing_rows(v: &[u8], iv: &(Option<Bytes>, Option<Bytes>)) -> Vec<(u64, u64, u64, u64)> {
    let lo = iv.0.clone().unwrap_or_default();
    let hi = iv.1.clone().unwrap_or_default();
    let hn = iv.1.is_none();
    (0..=v.len())
        .filter(|&k| same_prefix(v, &lo, k) || (!hn && same_prefix(v, &hi, k)))
        .map(|k| (k as u64, get_d(&lo, k), get_d(&hi, k), hn as u64))
        .collect()
}

/// The honest `rcptV3` input ([`RcptIn`]): the list view of
/// `AcceptedV3.rcptInput` (see the module docs for each field).
pub fn rcpt_view(n: &Native) -> RcptIn {
    let rs = n.rs();
    let bounds = bounded_intervals(&n.layout, n.own);
    let akp: Vec<Vec<u8>> = rs
        .iter()
        .map(|r| account_key_path(&r.receiver_id))
        .collect();
    let choice: Vec<Option<usize>> = rs
        .iter()
        .map(|r| {
            system_equal(r)
                .then(|| value_index(&n.pre, &key_access_key(&r.receiver_id, &r.signer_pk)))
                .flatten()
        })
        .collect();
    let mut gi = 0usize;
    let mut lists = Vec::with_capacity(n.lists.len());
    for l in &n.lists {
        let mut out = Vec::with_capacity(l.len());
        for (r, refund) in l {
            let i = gi;
            gi += 1;
            let a = &n.accounts[i];
            let sys = is_sys(r);
            let surplus = native_surplus(n.bgp, r);
            let o = native_outcome(n.height, n.bgp, r);
            let access = value_index(&n.pre, &key_access_key(&r.receiver_id, &r.signer_pk));
            let q = routing_index(&bounds, &r.receiver_id);
            let iv = bounds.get(q).cloned().unwrap_or((None, None));
            // `u` is the native trace's `uB` (no frame writes it: `0`); the
            // installed render's `uB` is `counterPatch … physicalBoundaryRank`,
            // which `rcpt.rs` recomputes on every row
            let rlk: Vec<Rlk> = routing_rows(&r.receiver_id, &iv)
                .into_iter()
                .map(|(pos, lo, hi, hn)| Rlk {
                    pos,
                    lo,
                    hi,
                    hn,
                    u: 0,
                })
                .collect();
            let tprev = (0..i)
                .rev()
                .find(|&j| rs[j].receiver_id == r.receiver_id)
                .map_or(0, |j| j as u64 + 1);
            let aku_i = access.unwrap_or(0);
            let aku = choice[..i].iter().filter(|c| **c == Some(aku_i)).count() as u64;
            let mut st = le_n(a.storage_usage, 8);
            st.resize(16, 0);
            out.push(RcptE {
                p: nats(&r.predecessor_id),
                v: nats(&r.receiver_id),
                s: nats(&r.signer_id),
                rid: nats(&r.receipt_id),
                kt: r.signer_pk.tag as u64,
                pk: nats(&r.signer_pk.data),
                gp: le_n(r.gas_price, 16),
                dep: le_n(r.deposit, 16),
                hr: *refund,
                ge: n.bgp <= r.gas_price,
                kslot: value_index(&n.pre, &akp[i]).unwrap_or(0) as u64,
                tprev,
                bef: le_n(a.amount, 16),
                lk: le_n(a.locked, 16),
                st,
                aft: le_n(a.amount.wrapping_add(r.deposit), 16),
                burnt: le_n(o.tokens_burnt, 16),
                ramt: le_n(if *refund { surplus } else { 0 }, 16),
                rfid: if *refund {
                    nats(&o.receipt_ids[0])
                } else {
                    vec![0; 32]
                },
                peoh: nats(&sha256(&o.partial_encode())),
                sys,
                ee: system_equal(r),
                gv: (0..r.receiver_id.len())
                    .map(|k| system_lookup(r, k))
                    .collect(),
                gs: (0..r.signer_id.len())
                    .map(|k| system_lookup(r, k))
                    .collect(),
                sx: (0..r.signer_id.len())
                    .map(|k| get_d(&r.receiver_id, k))
                    .collect(),
                akf: access.is_none() as u64,
                akk: access.unwrap_or(0) as u64,
                aku,
                q: q as u64,
                rlk,
                iv: Some(Iv {
                    lo: iv.0.as_deref().map(nats),
                    hi: iv.1.as_deref().map(nats),
                }),
            });
        }
        lists.push(ListV3 {
            n0: (l.len() % 256) as u64,
            n1: (l.len() / 256 % 256) as u64,
            rs: out,
        });
    }
    RcptIn {
        lists,
        own: n.own,
        height: n.height,
        bgp: n.bgp,
    }
}

// ---------------------------------------------------------------------------
// Tables 17, 18, 19, 20, 23, 24
// ---------------------------------------------------------------------------

/// `distinctTouched ks`: the last occurrence of every key, in order.
fn distinct_touched(ks: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    for (i, k) in ks.iter().enumerate() {
        if !ks[i + 1..].contains(k) {
            out.push(k.clone());
        }
    }
    out
}

/// `nativeAccountViews m.pre oldPost rs` (`closingAccountView` per distinct
/// touched key: value index, closing version, pre bytes, post amount).
pub fn acct_views(n: &Native) -> Result<Vec<AcctV>, String> {
    let keys: Vec<Vec<u8>> = n
        .rs()
        .iter()
        .map(|r| account_key_path(&r.receiver_id))
        .collect();
    let vals = vals_of(&n.pre);
    distinct_touched(&keys)
        .iter()
        .map(|key| {
            let i = value_index(&n.pre, key).ok_or("account view: no value index")?;
            let before = vals.get(i).ok_or("account view: no pre value")?;
            let after = get(&n.post, key).ok_or("account view: no post value")?;
            let a = Account::decode(&after).ok_or("account view: post undecodable")?;
            let tlast = keys
                .iter()
                .rposition(|k| k == key)
                .map_or(0, |j| j as u64 + 1);
            Ok(AcctV {
                k: i as u64,
                tlast,
                pre: nats(before),
                post: le_n(a.amount, 16),
            })
        })
        .collect()
}

/// `NativeAccessKeyProviders.providers m.pre rs`.
pub fn akey_providers(n: &Native) -> Vec<AkeyE> {
    let sel: Vec<usize> = n
        .rs()
        .iter()
        .filter(|r| system_equal(r))
        .filter_map(|r| value_index(&n.pre, &key_access_key(&r.receiver_id, &r.signer_pk)))
        .collect();
    let vals = vals_of(&n.pre);
    let mut dedup: Vec<usize> = Vec::new();
    for &i in &sel {
        if !dedup.contains(&i) {
            dedup.push(i);
        }
    }
    dedup
        .into_iter()
        .map(|i| AkeyE {
            vid: i as u64,
            u: sel.iter().filter(|&&j| j == i).count() as u64,
            bytes: vals.get(i).map(|b| nats(b)).unwrap_or_default(),
        })
        .collect()
}

/// `boundaryEntries (boundedIntervals L own) keys` with the physical boundary
/// keys `[65q + pos, lo, hi, hn]` of the view's `rlk` rows.
pub fn bnd_entries(n: &Native, rc: &RcptIn) -> Vec<BndE> {
    let bounds = bounded_intervals(&n.layout, n.own);
    let keys: Vec<[u64; 4]> = rc
        .lists
        .iter()
        .flat_map(|l| &l.rs)
        .flat_map(|x| {
            x.rlk
                .iter()
                .map(move |k| [65 * x.q + k.pos, k.lo, k.hi, k.hn])
        })
        .collect();
    (0..65 * bounds.len())
        .map(|x| {
            let b = &bounds[x / 65];
            let k = x % 65;
            let lo = get_d(b.0.as_deref().unwrap_or(&[]), k);
            let hi = get_d(b.1.as_deref().unwrap_or(&[]), k);
            let hn = b.1.is_none() as u64;
            let key = [x as u64, lo, hi, hn];
            BndE {
                x: x as u64,
                lo,
                hi,
                hn,
                u: keys.iter().filter(|kk| **kk == key).count() as u64,
            }
        })
        .collect()
}

/// `Public.sourceDup sources j`.
fn source_dup(s: &[SrcList], j: usize) -> bool {
    s[..j].iter().any(|x| x.key == s[j].key)
}

/// `sourceRepeated sources j`.
fn source_repeated(s: &[SrcList], j: usize) -> bool {
    s.iter().filter(|x| x.key == s[j].key).count() >= 2
}

/// `proofItems q len acc path`.
fn proof_items(mut q: u64, mut len: u64, mut acc: Vec<u8>, path: &[(Bytes, u8)]) -> Vec<SrcpItem> {
    let mut out = Vec::with_capacity(path.len());
    for (sib, dir) in path {
        out.push(SrcpItem {
            q: q + 1,
            dir: *dir != 0,
            sib: nats(sib),
            acc: nats(&acc),
            pq: q,
            pl: len,
        });
        // `proofHashStep`
        let mut b = Vec::with_capacity(64);
        if *dir == 0 {
            b.extend_from_slice(sib);
            b.extend_from_slice(&acc);
        } else {
            b.extend_from_slice(&acc);
            b.extend_from_slice(sib);
        }
        acc = sha256(&b).to_vec();
        q += 1;
        len = 64;
    }
    out
}

/// `DedupCompile.blocks p.lists w.entries`, each with `rep = sourceRepeated`.
pub fn srcp_blocks(n: &Native) -> Vec<SrcpB> {
    let s = &n.sources;
    let empty = ProofEntry {
        key: vec![],
        receipts: vec![],
        from_shard: 0,
        to_shard: 0,
        path: vec![],
    };
    let entry = |j: usize| lookup_last(&s[j].key, &n.entries).unwrap_or(&empty);
    let mut q = 1u64; // `nextQ j = 1 + Σ_{i<j} messageWeight i`
    (0..s.len())
        .map(|j| {
            let e = entry(j);
            let dup = source_dup(s, j);
            let mut raw = u64b(e.to_shard as u128);
            raw.extend(ns::encode_receipts(&e.receipts));
            let leaf = sha256(&raw);
            let b = SrcpB {
                j: j as u64,
                l: raw.len() as u64,
                dup,
                root: nats(&s[j].root),
                qe: q + e.path.len() as u64,
                le: if e.path.is_empty() { 32 } else { 64 },
                ql: q,
                leaf: nats(&leaf),
                path: proof_items(q, 32, sha256(&leaf).to_vec(), &e.path),
                rep: source_repeated(s, j),
            };
            if !dup {
                q += 1 + e.path.len() as u64;
            }
            b
        })
        .collect()
}

/// `outcomePreimages os` of the native outcomes (`u32 2 ++ id ++ sha256 peo`).
fn outcome_leaves(n: &Native) -> Vec<Vec<u8>> {
    n.rs()
        .iter()
        .map(|r| {
            let o = native_outcome(n.height, n.bgp, r);
            let mut b = ns::u32b(2);
            b.extend_from_slice(&o.id);
            b.extend_from_slice(&sha256(&o.partial_encode()));
            b
        })
        .collect()
}

/// `levelTable (outcomePreimages os)` (`MerkleShaJobs.levelsFromLeaves`, levels
/// `0 … n + 1`).
pub fn mrk_levels(leaves: &[Vec<u8>]) -> Vec<Vec<MNode>> {
    let n = leaves.len() as u64;
    let mut lv: Vec<Vec<MNode>> = vec![
        leaves
            .iter()
            .enumerate()
            .map(|(r, b)| MNode {
                id: msg_id(K_LEAF, r as u64),
                len: b.len() as u64,
                dig: nats(&sha256(b)),
            })
            .collect(),
    ];
    for j in 0..=leaves.len() {
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
                        id: msg_id(K_MRK, qbase(n, j as u64 + 1) + i as u64),
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
    lv
}

/// Table 23's input: the `MrkV` of the native outcome tree, with its levels.
pub fn mrk_view(n: &Native) -> MrkV {
    let leaves = outcome_leaves(n);
    let lv = mrk_levels(&leaves);
    let num = leaves.len() as u64;
    if num == 0 {
        return MrkV {
            levels: lv,
            ..MrkV::default()
        };
    }
    MrkV {
        levels: lv.clone(),
        ..mrk_from_levels(num, &lv)
    }
}

/// `NativeSortIds.sorted rs`: `(index, id)` stably sorted by the id as a
/// little-endian natural (`foldr insertSorted`).
pub fn sort_ids(n: &Native) -> Vec<(u64, Vec<u64>)> {
    let mut v: Vec<(u64, Vec<u64>)> = n
        .rs()
        .iter()
        .enumerate()
        .map(|(i, r)| (i as u64, nats(&r.receipt_id)))
        .collect();
    sort_le(&mut v);
    v
}

/// Stable sort of `(index, id)` pairs by the id as a little-endian natural
/// (`leVal`; `foldr insertSorted` keeps equal ids in input order).
fn sort_le(v: &mut [(u64, Vec<u64>)]) {
    let sig = |x: &[u64]| x.iter().rposition(|&b| b != 0).map_or(0, |i| i + 1);
    v.sort_by(|a, b| {
        let (la, lb) = (sig(&a.1), sig(&b.1));
        la.cmp(&lb)
            .then_with(|| a.1[..la].iter().rev().cmp(b.1[..lb].iter().rev()))
    });
}

/// All receipt-side entries of a real claim + witness.
pub struct RcptFam {
    pub rcpt: RcptIn,
    pub acct: Vec<AcctV>,
    pub akey: Vec<AkeyE>,
    pub bnd: Vec<BndE>,
    pub srcp: Vec<SrcpB>,
    pub mrk: MrkV,
    pub sort: Vec<(u64, Vec<u64>)>,
}

pub fn rcpt_family(cb: &[u8], wb: &[u8]) -> Result<RcptFam, String> {
    let n = native(cb, wb)?;
    let rcpt = rcpt_view(&n);
    let bnd = bnd_entries(&n, &rcpt);
    Ok(RcptFam {
        acct: acct_views(&n)?,
        akey: akey_providers(&n),
        srcp: srcp_blocks(&n),
        mrk: mrk_view(&n),
        sort: sort_ids(&n),
        bnd,
        rcpt,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinct_touched_keeps_last() {
        let k = |x: u8| vec![x];
        assert_eq!(
            distinct_touched(&[k(1), k(2), k(1), k(3), k(2)]),
            vec![k(1), k(3), k(2)]
        );
    }

    #[test]
    fn sort_is_stable_le() {
        let mut s: Vec<(u64, Vec<u64>)> = [vec![1u64, 0], vec![0, 1], vec![2, 0, 0], vec![1]]
            .into_iter()
            .enumerate()
            .map(|(i, x)| (i as u64, x))
            .collect();
        sort_le(&mut s);
        assert_eq!(s.iter().map(|x| x.0).collect::<Vec<_>>(), vec![0, 3, 2, 1]);
    }

    #[test]
    fn routing_rows_prefixes() {
        let iv = (Some(b"s4".to_vec()), None);
        let r = routing_rows(b"s4a07", &iv);
        assert_eq!(r, vec![(0, 115, 0, 1), (1, 52, 0, 1), (2, 0, 0, 1)]);
    }
}
