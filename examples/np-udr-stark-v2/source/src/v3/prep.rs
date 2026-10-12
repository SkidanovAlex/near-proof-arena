//! The `prepD0` / `Hint` byte codec (part 3 of the v2 prover), mirroring
//! `spec/lean/v3/NearSpecV3/PrepD0.lean` and
//! `zk-formal/ZkFormal/NearV3/Assembly/HintCodec.lean`.
//!
//! The v2 verifier splits a proof into a clear `Hint` (`u32 n ‖ borshBytes body`)
//! and the STARK proof; the STARK's public input is the *prepared statement*
//! `Prep.encode` (tag `"near-arena-prep-d0a-v0"`).  This module implements the
//! byte codecs (`Hint`, `PrepHdr`, `SrcList`, `SchedPub`, `Prep`) and the
//! refund-body codec (`decode_body` / `body_of`), so that a real
//! `(claim.bin, hint)` can be turned into the prepared public bytes.
//!
//! `conformance/PrepV3.lean` (`np-lean-prep-v3`) computes a real
//! `p := NearSpecV3.prepD0 cb (hintOf cb wb)` and dumps `hint`, `prep`,
//! `refunds_enc` and `prep_json`; `npudr prep-encode` re-encodes `prep_json` and
//! must reproduce `prep` byte for byte, and the `Hint`/body codecs round-trip.
//!
//! `prepClaim` / `prepBody` are **not** ported here: `prepBody` needs D0
//! execution (`applyNewChunk`), out of scope.  The `prep-encode` path consumes
//! the Lean-prepared structure and only re-encodes it.

use serde::Deserialize;

use crate::near::reexec::spec::account_id_valid;
use crate::near::spec::{
    self as ns, Bytes, Receipt, borsh_bytes, encode_receipts, u16b, u32b, u64b, u128b,
};

// ---------------------------------------------------------------------------
// `Bytes` helpers (`NearSpec.{leN,u8,u16,u32,u64,u128,borshBytes,concatAll}`,
// `NearSpecV3.{encList,encOpt}`)
// ---------------------------------------------------------------------------

/// `stateShard`-independent little-endian helpers, as in `near::spec` but with
/// the `u8` and list combinators of the v3 encoders.
pub fn u8b(x: u128) -> Bytes {
    ns::le_n(1, x)
}
/// `concatAll`: concatenate a list of byte strings.
pub fn concat_all(parts: &[Bytes]) -> Bytes {
    let mut v = Vec::with_capacity(parts.iter().map(Vec::len).sum());
    for p in parts {
        v.extend_from_slice(p);
    }
    v
}
/// `encList f l = u32 l.length ‖ concatAll (l.map f)`.
pub fn enc_list<T>(f: impl Fn(&T) -> Bytes, l: &[T]) -> Bytes {
    let mut v = u32b(l.len() as u128);
    for x in l {
        v.extend(f(x));
    }
    v
}
/// `encOpt f = [0] | [1] ‖ f a`.
pub fn enc_opt<T>(f: impl Fn(&T) -> Bytes, o: &Option<T>) -> Bytes {
    match o {
        None => vec![0],
        Some(a) => {
            let mut v = vec![1];
            v.extend(f(a));
            v
        }
    }
}

// ---------------------------------------------------------------------------
// Hint (`Assembly/HintCodec.lean`)
// ---------------------------------------------------------------------------

/// `NearSpecV3.Hint { n, body }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hint {
    pub n: u64,
    pub body: Bytes,
}

impl Hint {
    /// `Hint.empty = ⟨0, u32 0 ‖ u32 0⟩`.
    pub fn empty() -> Hint {
        let mut body = u32b(0);
        body.extend(u32b(0));
        Hint { n: 0, body }
    }
    /// `Hint.encode = u32 n ‖ borshBytes body`.
    pub fn encode(&self) -> Bytes {
        let mut v = u32b(self.n as u128);
        v.extend(borsh_bytes(&self.body));
        v
    }
    /// `Hint.decode`, consuming all input.
    pub fn decode(bs: &[u8]) -> Result<Hint, String> {
        let mut r = crate::near::reexec::wire::Reader::new(bs);
        let n = r.u32("hint.n").map_err(|e| e.to_string())?;
        let body = r.bytes("hint.body").map_err(|e| e.to_string())?.to_vec();
        r.finish().map_err(|e| e.to_string())?;
        Ok(Hint { n: n as u64, body })
    }
}

// ---------------------------------------------------------------------------
// Refund body codec (`pRefund` / `decodeBody` / `bodyOf`)
// ---------------------------------------------------------------------------

/// `bodyOf refunds = u32 0 ‖ encodeReceipts refunds`.
pub fn body_of(refunds: &[Receipt]) -> Bytes {
    let mut v = u32b(0);
    v.extend(encode_receipts(refunds));
    v
}

/// One `pRefund` receipt: predecessor `system`, any valid receiver
/// (`AccountId.valid`), `ReceiptEnum::Action` with one `Transfer`, no data
/// dependencies, ED25519/SECP256K1 signer key.  `Err` on any other shape.
fn read_refund(r: &mut crate::near::reexec::wire::Reader<'_>) -> Result<Receipt, String> {
    let err = |m: &str| m.to_string();
    let predecessor_id = r
        .bytes("refund predecessor_id")
        .map_err(|e| e.to_string())?
        .to_vec();
    if !account_id_valid(&predecessor_id) {
        return Err(err(
            "invalid hint: refund predecessor is not a valid account id",
        ));
    }
    if predecessor_id != ns::SYSTEM {
        return Err(err("invalid hint: refund predecessor is not system"));
    }
    let receiver_id = r
        .bytes("refund receiver_id")
        .map_err(|e| e.to_string())?
        .to_vec();
    if !account_id_valid(&receiver_id) {
        return Err(err(
            "invalid hint: refund receiver is not a valid account id",
        ));
    }
    let receipt_id = r
        .hash("refund receipt_id")
        .map_err(|e| e.to_string())?
        .to_vec();
    if r.u8("refund ReceiptEnum tag").map_err(|e| e.to_string())? != 0 {
        return Err(err("invalid hint: refund ReceiptEnum is not Action(0)"));
    }
    let signer_id = r
        .bytes("refund signer_id")
        .map_err(|e| e.to_string())?
        .to_vec();
    if !account_id_valid(&signer_id) {
        return Err(err("invalid hint: refund signer is not a valid account id"));
    }
    let tag = r.u8("refund signer key type").map_err(|e| e.to_string())?;
    let klen = match tag {
        0 => 32usize,
        1 => 64,
        2 => return Err(err("invalid hint: refund ML-DSA signer key")),
        _ => return Err(err("invalid hint: refund unknown signer key type")),
    };
    let data = r
        .take(klen, "refund signer key")
        .map_err(|e| e.to_string())?
        .to_vec();
    let gas_price = r.u128("refund gas_price").map_err(|e| e.to_string())?;
    if r.u32("refund output_data_receivers")
        .map_err(|e| e.to_string())?
        != 0
    {
        return Err(err("invalid hint: refund output_data_receivers"));
    }
    if r.u32("refund input_data_ids").map_err(|e| e.to_string())? != 0 {
        return Err(err("invalid hint: refund input_data_ids"));
    }
    if r.u32("refund actions").map_err(|e| e.to_string())? != 1 {
        return Err(err("invalid hint: refund is not exactly one action"));
    }
    if r.u8("refund action tag").map_err(|e| e.to_string())? != 3 {
        return Err(err("invalid hint: refund action is not Transfer(3)"));
    }
    let deposit = r.u128("refund deposit").map_err(|e| e.to_string())?;
    Ok(Receipt {
        predecessor_id,
        receiver_id,
        receipt_id,
        signer_id,
        signer_pk: ns::PublicKey { tag, data },
        gas_price,
        deposit,
    })
}

/// Parse `Vec<refund receipt>` (`u32` count then the receipts), return the list
/// and the unread suffix.
pub fn decode_receipts(b: &[u8]) -> Result<(Vec<Receipt>, usize), String> {
    let mut r = crate::near::reexec::wire::Reader::new(b);
    let n = r.u32("refunds count").map_err(|e| e.to_string())? as usize;
    let mut rs = Vec::with_capacity(n.min(1 << 16));
    for _ in 0..n {
        rs.push(read_refund(&mut r)?);
    }
    Ok((rs, r.pos))
}

/// `decodeBody b = u32 0 ‖ Vec<pRefund>` with no trailing bytes.
pub fn decode_body(b: &[u8]) -> Result<Vec<Receipt>, String> {
    let mut r = crate::near::reexec::wire::Reader::new(b);
    if r.u32("body transactions").map_err(|e| e.to_string())? != 0 {
        return Err("invalid hint: body transactions".into());
    }
    let at = r.pos;
    let (rs, used) = decode_receipts(&b[at..])?;
    if at + used != b.len() {
        return Err("invalid hint: trailing bytes in body".into());
    }
    Ok(rs)
}

// ---------------------------------------------------------------------------
// Prepared statement (`PrepHdr`, `SrcList`, `SchedPub`, `Prep`)
// ---------------------------------------------------------------------------

/// `NearSpecV3.Scheduler.BandwidthRequest { toShard, bitmap }` (5-byte bitmap).
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct BandwidthRequest {
    #[serde(rename = "toShard")]
    pub to_shard: u64,
    pub bitmap: Vec<u8>,
}

/// `NearSpecV3.Scheduler.Params`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct SchedParams {
    pub base: u64,
    #[serde(rename = "maxShardBandwidth")]
    pub max_shard_bandwidth: u64,
    #[serde(rename = "maxSingleGrant")]
    pub max_single_grant: u64,
    #[serde(rename = "maxReceiptSize")]
    pub max_receipt_size: u64,
    #[serde(rename = "maxAllowance")]
    pub max_allowance: u64,
}

/// `NearSpecV3.Scheduler.SchedPub`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct SchedPub {
    pub ids: Vec<u64>,
    pub params: SchedParams,
    pub allowed: Vec<bool>,
    pub raw: Vec<(u64, Vec<BandwidthRequest>)>,
    pub values: Vec<u64>,
    pub seed: Vec<u8>,
    #[serde(rename = "allShardsHash")]
    pub all_shards_hash: Vec<u8>,
}

impl SchedPub {
    /// `Scheduler.SchedPub.encode`.
    pub fn encode(&self) -> Bytes {
        let mut v = enc_list(|x: &u64| u64b(*x as u128), &self.ids);
        v.extend(u64b(self.params.base as u128));
        v.extend(u64b(self.params.max_shard_bandwidth as u128));
        v.extend(u64b(self.params.max_single_grant as u128));
        v.extend(u64b(self.params.max_receipt_size as u128));
        v.extend(u64b(self.params.max_allowance as u128));
        v.extend(enc_list(
            |b: &bool| u8b(if *b { 1 } else { 0 }),
            &self.allowed,
        ));
        v.extend(enc_list(
            |(sender, brs): &(u64, Vec<BandwidthRequest>)| {
                let mut w = u64b(*sender as u128);
                w.extend(enc_list(
                    |b: &BandwidthRequest| {
                        let mut x = u16b(b.to_shard as u128);
                        x.extend_from_slice(&b.bitmap);
                        x
                    },
                    brs,
                ));
                w
            },
            &self.raw,
        ));
        v.extend(enc_list(|x: &u64| u64b(*x as u128), &self.values));
        v.extend_from_slice(&self.seed);
        v.extend_from_slice(&self.all_shards_hash);
        v
    }
}

/// `NearSpecV3.PrepHdr`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct PrepHdr {
    #[serde(rename = "K")]
    pub k: u64,
    pub n: u64,
    pub own: u64,
    #[serde(rename = "ownIdx")]
    pub own_idx: u64,
    #[serde(rename = "numShards")]
    pub num_shards: u64,
    pub height: u64,
    #[serde(rename = "gasPrice")]
    pub gas_price: u128,
    #[serde(rename = "gasLimit")]
    pub gas_limit: u64,
    #[serde(rename = "prevStateRoot")]
    pub prev_state_root: Vec<u8>,
    #[serde(rename = "postStateRoot")]
    pub post_state_root: Vec<u8>,
    #[serde(rename = "outcomeRoot")]
    pub outcome_root: Vec<u8>,
    #[serde(rename = "balanceBurnt")]
    pub balance_burnt: u128,
}

impl PrepHdr {
    /// `PrepHdr.encode`.
    pub fn encode(&self) -> Bytes {
        let mut v = u32b(self.k as u128);
        v.extend(u32b(self.n as u128));
        v.extend(u64b(self.own as u128));
        v.extend(u32b(self.own_idx as u128));
        v.extend(u32b(self.num_shards as u128));
        v.extend(u64b(self.height as u128));
        v.extend(u128b(self.gas_price));
        v.extend(u64b(self.gas_limit as u128));
        v.extend_from_slice(&self.prev_state_root);
        v.extend_from_slice(&self.post_state_root);
        v.extend_from_slice(&self.outcome_root);
        v.extend(u128b(self.balance_burnt));
        v
    }
}

/// `NearSpecV3.SrcList`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct SrcList {
    pub key: Vec<u8>,
    #[serde(rename = "fromShard")]
    pub from_shard: u64,
    pub root: Vec<u8>,
}

impl SrcList {
    /// `SrcList.encode`.
    pub fn encode(&self) -> Bytes {
        let mut v = self.key.clone();
        v.extend(u64b(self.from_shard as u128));
        v.extend_from_slice(&self.root);
        v
    }
}

/// `"near-arena-prep-d0a-v0"`.
pub const PREP_TAG: &[u8] = b"near-arena-prep-d0a-v0";

/// `NearSpecV3.Prep`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Prep {
    pub hdr: PrepHdr,
    pub lists: Vec<SrcList>,
    pub bnds: Vec<(Option<Vec<u8>>, Option<Vec<u8>>)>,
    pub sched: Vec<SchedPub>,
    pub body: Vec<u8>,
    pub fwd: Vec<(u64, u64)>,
}

impl Prep {
    /// Parse a Lean `np-lean-prep-v3` `prep_json` dump.
    pub fn from_json(s: &str) -> Result<Prep, String> {
        serde_json::from_str(s).map_err(|e| e.to_string())
    }

    /// `Prep.encode`.
    pub fn encode(&self) -> Bytes {
        let mut v = borsh_bytes(PREP_TAG);
        v.extend(self.hdr.encode());
        v.extend(enc_list(|s: &SrcList| s.encode(), &self.lists));
        v.extend(enc_list(
            |(lo, hi): &(Option<Vec<u8>>, Option<Vec<u8>>)| {
                let mut w = enc_opt(|b: &Vec<u8>| borsh_bytes(b), lo);
                w.extend(enc_opt(|b: &Vec<u8>| borsh_bytes(b), hi));
                w
            },
            &self.bnds,
        ));
        v.extend(enc_list(|s: &SchedPub| s.encode(), &self.sched));
        v.extend(borsh_bytes(&self.body));
        v.extend(enc_list(
            |(s, t): &(u64, u64)| {
                let mut w = u64b(*s as u128);
                w.extend(u64b(*t as u128));
                w
            },
            &self.fwd,
        ));
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refund() -> Receipt {
        Receipt {
            predecessor_id: b"system".to_vec(),
            receiver_id: b"alice.near".to_vec(),
            receipt_id: vec![7u8; 32],
            signer_id: b"alice.near".to_vec(),
            signer_pk: ns::PublicKey {
                tag: 0,
                data: vec![9u8; 32],
            },
            gas_price: 0,
            deposit: 12345,
        }
    }

    #[test]
    fn hint_round_trips() {
        for body in [Hint::empty().body, vec![], vec![1, 2, 3, 255]] {
            let h = Hint { n: 7, body };
            assert_eq!(Hint::decode(&h.encode()).unwrap(), h);
        }
        // trailing byte rejected
        let mut e = Hint {
            n: 1,
            body: vec![1],
        }
        .encode();
        e.push(0);
        assert!(Hint::decode(&e).is_err());
    }

    #[test]
    fn body_round_trips() {
        for rs in [vec![], vec![refund()], vec![refund(), refund()]] {
            let b = body_of(&rs);
            assert_eq!(decode_body(&b).unwrap(), rs);
        }
    }

    #[test]
    fn body_rejects_non_refund() {
        // non-zero transaction count
        assert!(decode_body(&u32b(1)).is_err());
        // predecessor != system
        let mut r = refund();
        r.predecessor_id = b"bob.near".to_vec();
        assert!(decode_body(&body_of(&[r])).is_err());
        // trailing bytes
        let mut b = body_of(&[refund()]);
        b.push(0);
        assert!(decode_body(&b).is_err());
    }

    #[test]
    fn enc_combinators_match_lean() {
        assert_eq!(concat_all(&[vec![1, 2], vec![], vec![3]]), vec![1, 2, 3]);
        assert_eq!(enc_list(|x: &u64| u64b(*x as u128), &[1, 2]), {
            let mut v = u32b(2);
            v.extend(u64b(1));
            v.extend(u64b(2));
            v
        });
        assert_eq!(enc_opt(|b: &Vec<u8>| borsh_bytes(b), &None), vec![0]);
        assert_eq!(
            enc_opt(|b: &Vec<u8>| borsh_bytes(b), &Some(vec![9])),
            vec![1, 1, 0, 0, 0, 9]
        );
    }
}
