//! The state-dependent part of the bandwidth scheduler run (`prims.sched`), as far
//! as the new `0x0f` state value: the Rust twin of `Scheduler.runCore`
//! (`spec/lean/v3/NearSpecV3/PrepD0.lean`) applied to `Scheduler.pubOf`
//! ([`crate::v3::d0::sched_pub`]); `prims.sched = Scheduler.run … =
//! (pubOf …).bind (runCore · prev)` (`Scheduler.run_eq_core`).
//!
//! Only `Output.state` is computed.  `distribute` (`BandwidthScheduler.lean`) only
//! adds link grants (`grantMore`) and never fails, so it is skipped; the grants
//! themselves are not tracked (`tryGrant`'s success does not read them).
//!
//! | Rust | Lean (`NearSpecV3.Scheduler`, `BandwidthScheduler.lean` / `PrepD0.lean`) |
//! |---|---|
//! | [`decode_state`] | `NearSpec.Bandwidth.State.decode` (`NearSpec/Bandwidth.lean`) |
//! | [`encode_state`] | `NearSpec.Bandwidth.State.encode` |
//! | `get_bit` / `increases` | `getBit` / `increases` |
//! | `convert_raw` | `convertRaw` (`convertRequestV`) |
//! | `try_grant` | `tryGrant` (without `grantMore`) |
//! | `bucket_push` / `process_bucket` / `process_loop` | `bucketPush` / `processBucket` / `processLoop` / `processRequests` |
//! | `shuffle` | `NearSpecV3.shuffle` (`ChaCha20.lean`) on a run-wide `Rng` |
//! | [`run_core_state`] | `runCore` (`.state` only) |

use crate::near::reexec::sha256;
use crate::near::spec::{Bytes, u32b, u64b};
use crate::v3::d0::{Stream, gen_at, index_of};
use crate::v3::prep::{BandwidthRequest, SchedPub};

/// `u64Max`.
const U64_MAX: u128 = u64::MAX as u128;

/// `NearSpec.Bandwidth.State` (`links` as `(sender, receiver, allowance)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BwState {
    pub links: Vec<(u64, u64, u64)>,
    pub sanity_hash: Bytes,
}

/// `State.initial = ⟨[], zeroHash⟩`.
fn initial_state() -> BwState {
    BwState {
        links: vec![],
        sanity_hash: vec![0u8; 32],
    }
}

fn rd_u64(b: &[u8], at: &mut usize) -> Option<u64> {
    let x = b.get(*at..*at + 8)?;
    *at += 8;
    Some(u64::from_le_bytes(x.try_into().ok()?))
}

/// `State.decode` (strict borsh: tag 0, `u32` count, links, 32-byte hash, no trailing bytes).
pub(crate) fn decode_state(b: &[u8]) -> Option<BwState> {
    if *b.first()? != 0 {
        return None;
    }
    let n = u32::from_le_bytes(b.get(1..5)?.try_into().ok()?);
    let mut at = 5usize;
    let mut links = Vec::new();
    // `readMany readLink n`: fails at the first truncated link
    for _ in 0..n {
        let s = rd_u64(b, &mut at)?;
        let r = rd_u64(b, &mut at)?;
        let a = rd_u64(b, &mut at)?;
        links.push((s, r, a));
    }
    let h = b.get(at..at + 32)?.to_vec();
    if at + 32 != b.len() {
        return None;
    }
    Some(BwState {
        links,
        sanity_hash: h,
    })
}

/// `State.encode = [0] ++ u32 |links| ++ links ++ sanityHash`.
pub(crate) fn encode_state(s: &BwState) -> Bytes {
    let mut v = vec![0u8];
    v.extend(u32b(s.links.len() as u128));
    for &(a, b, c) in &s.links {
        v.extend(u64b(a as u128));
        v.extend(u64b(b as u128));
        v.extend(u64b(c as u128));
    }
    v.extend_from_slice(&s.sanity_hash);
    v
}

/// `getBit bm i`: bit `i % 8` (Lsb0) of byte `i / 8`, default 0.
fn get_bit(bm: &[u8], i: usize) -> bool {
    (bm.get(i / 8).copied().unwrap_or(0) >> (i % 8)) & 1 == 1
}

/// `increases vals bm 0 vals cur`.
fn increases(vals: &[u64], bm: &[u8], mut cur: u64) -> Vec<u64> {
    let mut out = Vec::new();
    for (i, &v) in vals.iter().enumerate() {
        if get_bit(bm, i) && cur < v {
            out.push(v - cur);
            cur = v;
        }
    }
    out
}

/// `Req`.
#[derive(Clone, Debug)]
struct Req {
    link: usize,
    incs: Vec<u64>,
}

/// `convertRaw vals base ids raw` (`convertRequestV` per request, `filterMap`).
fn convert_raw(
    vals: &[u64],
    base: u64,
    ids: &[u64],
    raw: &[(u64, Vec<BandwidthRequest>)],
) -> Vec<Req> {
    let mut out = Vec::new();
    for (sender, brs) in raw {
        for br in brs {
            let (Some(s), Some(r)) = (index_of(ids, *sender), index_of(ids, br.to_shard)) else {
                continue;
            };
            let incs = increases(vals, &br.bitmap, base);
            if !incs.is_empty() {
                out.push(Req {
                    link: s * ids.len() + r,
                    incs,
                });
            }
        }
    }
    out
}

/// `St` without `granted`; `rng` is the word cursor `k` into the run-wide ChaCha20
/// stream (`Rng.nextU32` consumes the stream's words in order).
struct St {
    sender_budget: Vec<u64>,
    receiver_budget: Vec<u64>,
    allowance: Vec<u64>,
    stream: Stream,
    k: u64,
}

impl St {
    /// `st.allowance[l]!` (out of range = `default` = 0).
    fn allow(&self, l: usize) -> u64 {
        self.allowance.get(l).copied().unwrap_or(0)
    }
}

/// `tryGrant n allowed st l bw` (the success flag; `grantMore` omitted).
fn try_grant(n: usize, allowed: &[bool], st: &mut St, l: usize, bw: u64) -> bool {
    if !allowed.get(l).copied().unwrap_or(false) {
        return false;
    }
    let (s, r) = (l / n, l % n);
    let sb = st.sender_budget.get(s).copied().unwrap_or(0);
    let rb = st.receiver_budget.get(r).copied().unwrap_or(0);
    if sb < bw || rb < bw {
        return false;
    }
    // `Array.set!` is a no-op out of range
    if let Some(x) = st.sender_budget.get_mut(s) {
        *x = sb - bw;
    }
    if let Some(x) = st.receiver_budget.get_mut(r) {
        *x = rb - bw;
    }
    let a = st.allow(l).saturating_sub(bw);
    if let Some(x) = st.allowance.get_mut(l) {
        *x = a;
    }
    true
}

/// `bucketPush k q bk` (ascending keys; an equal key appends to its bucket).
fn bucket_push(k: u64, q: Req, bk: &mut Vec<(u64, Vec<Req>)>) {
    match bk.iter().position(|(k2, _)| k <= *k2) {
        Some(i) if bk[i].0 == k => bk[i].1.push(q),
        Some(i) => bk.insert(i, (k, vec![q])),
        None => bk.push((k, vec![q])),
    }
}

/// `shuffle l st.rng`: `rand` `SliceRandom::shuffle` continuing the run-wide stream.
fn shuffle<T>(l: &mut [T], st: &mut St) -> bool {
    let n = l.len();
    if n == 0 {
        return true;
    }
    let mut i = n - 1;
    while i >= 1 {
        match gen_at(&mut st.stream, (i + 1) as u64, st.k) {
            Some((j, k2)) => {
                st.k = k2;
                l.swap(i, j as usize);
            }
            None => return false,
        }
        i -= 1;
    }
    true
}

/// `processBucket n allowed qs (st, bk)`.
fn process_bucket(
    n: usize,
    allowed: &[bool],
    qs: Vec<Req>,
    st: &mut St,
    bk: &mut Vec<(u64, Vec<Req>)>,
) {
    for q in qs {
        let Some((&inc, rest)) = q.incs.split_first() else {
            continue;
        };
        let ok = try_grant(n, allowed, st, q.link, inc);
        if ok && !rest.is_empty() {
            let k = st.allow(q.link);
            bucket_push(
                k,
                Req {
                    link: q.link,
                    incs: rest.to_vec(),
                },
                bk,
            );
        }
    }
}

/// `processRequests n allowed st reqs` (`processLoop` with fuel `1 + Σ |incs|`).
fn process_requests(n: usize, allowed: &[bool], st: &mut St, reqs: Vec<Req>) -> bool {
    let mut fuel: usize = 1 + reqs.iter().map(|q| q.incs.len()).sum::<usize>();
    let mut bk: Vec<(u64, Vec<Req>)> = Vec::new();
    for q in reqs {
        let k = st.allow(q.link);
        bucket_push(k, q, &mut bk);
    }
    loop {
        let Some((_, mut qs)) = bk.pop() else {
            return true;
        };
        if fuel == 0 {
            return false;
        }
        fuel -= 1;
        if !shuffle(&mut qs, st) {
            return false;
        }
        process_bucket(n, allowed, qs, st, &mut bk);
    }
}

/// `(runCore pub prevState).map (·.state)`: the new `0x0f` value.
pub(crate) fn run_core_state(p: &SchedPub, prev_state: Option<&[u8]>) -> Option<Bytes> {
    let prev = match prev_state {
        None => initial_state(),
        Some(b) => decode_state(b)?,
    };
    let ids = &p.ids;
    let n = ids.len();
    let links = n * n;
    let pr = &p.params;
    let mut allow0 = vec![0u64; links];
    for &(s, r, a) in &prev.links {
        if let (Some(s), Some(r)) = (index_of(ids, s), index_of(ids, r)) {
            allow0[s * n + r] = a;
        }
    }
    let reqs = convert_raw(&p.values, pr.base, ids, &p.raw);
    let mut st = St {
        sender_budget: vec![pr.max_shard_bandwidth; n],
        receiver_budget: vec![pr.max_shard_bandwidth; n],
        allowance: allow0,
        stream: Stream::of_seed(&p.seed),
        k: 0,
    };
    // `increase_allowances` (`n = 0` is excluded by `pubOf`)
    let fair = pr.max_shard_bandwidth as u128 / n.max(1) as u128;
    for a in st.allowance.iter_mut() {
        *a = (*a as u128 + fair)
            .min(U64_MAX)
            .min(pr.max_allowance as u128) as u64;
    }
    // `grant_base_bandwidth`
    for l in 0..links {
        try_grant(n, &p.allowed, &mut st, l, pr.base);
    }
    if !process_requests(n, &p.allowed, &mut st, reqs) {
        return None;
    }
    // (`distribute` only adds grants)
    let sid = |i: usize| ids.get(i).copied().unwrap_or(0);
    let new_links = (0..links)
        .map(|l| (sid(l / n), sid(l % n), st.allowance[l]))
        .collect();
    let mut hin = prev.sanity_hash.clone();
    hin.extend_from_slice(&p.all_shards_hash);
    Some(encode_state(&BwState {
        links: new_links,
        sanity_hash: sha256(&hin).to_vec(),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn state_codec_round_trip() {
        let s = BwState {
            links: vec![(1, 2, 3), (4, 5, 6)],
            sanity_hash: vec![7u8; 32],
        };
        let b = encode_state(&s);
        assert_eq!(decode_state(&b), Some(s));
        let mut t = b.clone();
        t.push(0);
        assert_eq!(decode_state(&t), None);
        assert_eq!(decode_state(&b[..b.len() - 1]), None);
    }

    #[test]
    fn increases_skip_non_increasing() {
        // bits 0 and 2 set; values 10, 20, 30 from cur 5
        assert_eq!(increases(&[10, 20, 30], &[0b101], 5), vec![5, 20]);
        assert_eq!(increases(&[10, 20, 30], &[0b001], 15), Vec::<u64>::new());
    }
}

#[cfg(test)]
mod run_tests {
    use super::*;
    use crate::v3::prep::SchedParams;

    /// One shard, no requests: `increase_allowances` to `max_allowance`, then the base
    /// grant on the (allowed) self link.
    #[test]
    fn one_shard_no_requests() {
        let p = SchedPub {
            ids: vec![3],
            params: SchedParams {
                base: 100_000,
                max_shard_bandwidth: 4_500_000,
                max_single_grant: 4_194_304,
                max_receipt_size: 4_194_304,
                max_allowance: 4_500_000,
            },
            allowed: vec![true],
            raw: vec![],
            values: vec![],
            seed: vec![0; 32],
            all_shards_hash: vec![9; 32],
        };
        let s = decode_state(&run_core_state(&p, None).unwrap()).unwrap();
        assert_eq!(s.links, vec![(3, 3, 4_400_000)]);
        let mut h = vec![0u8; 32];
        h.extend([9u8; 32]);
        assert_eq!(s.sanity_hash, sha256(&h).to_vec());
        assert!(run_core_state(&p, Some(&[1])).is_none());
    }
}
