//! Transfer transactions (domain D1): the Rust twin of `NearSpecV3.TxD1`
//! (`spec/lean/v3/NearSpecV3/TxD1.lean`): `pTxD1`, `Tx.sizeOk` / `valid`, `txCost`,
//! `decodeAccessKey` (with `utf8Ok`), `encodeFullAccessKey`, `verifyAndCharge`.

use crate::near::reexec::sha256;
use crate::near::reexec::wire::Reader;
use crate::near::spec::{Account, Bytes, PublicKey, u64b};
use crate::v3::d0::{
    is_eth_implicit, is_near_deterministic, is_near_implicit, mapw, p_account_id, p_public_key,
};

pub mod params {
    pub const NAR_SEND: u128 = 108_059_500_000;
    pub const NAR_EXEC: u128 = 108_059_500_000;
    pub const TRANSFER_SEND: u128 = 115_123_062_500;
    pub const TRANSFER_EXEC: u128 = 115_123_062_500;
    pub const CREATE_ACCOUNT_SEND: u128 = 500_000_000_000;
    pub const CREATE_ACCOUNT_EXEC: u128 = 7_200_000_000_000;
    pub const ADD_FULL_ACCESS_KEY_SEND: u128 = 101_765_125_000;
    pub const ADD_FULL_ACCESS_KEY_EXEC: u128 = 101_765_125_000;
    pub const MIN_GAS_PURCHASE_PRICE: u128 = 1_000_000_000;
    pub const MAX_TRANSACTION_SIZE: usize = 1_572_864;
    pub const NONCE_RANGE_MULTIPLIER: u128 = 1_000_000;
    pub const STORAGE_AMOUNT_PER_BYTE: u128 = 10_000_000_000_000_000_000;
    pub const ZERO_BALANCE_STORAGE_LIMIT: u128 = 770;
}

/// `Tx` (decoded D1 transaction).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tx {
    pub raw: Bytes,
    pub body: Bytes,
    pub signer_id: Bytes,
    pub pk: Bytes,
    pub nonce: u64,
    pub receiver_id: Bytes,
    pub block_hash: Bytes,
    pub deposit: u128,
    pub strict: bool,
    pub sig: Bytes,
}

impl Tx {
    pub fn hash(&self) -> Bytes {
        sha256(&self.body).to_vec()
    }
    pub fn pk_key(&self) -> PublicKey {
        PublicKey {
            tag: 0,
            data: self.pk.clone(),
        }
    }
    /// `Tx.sizeOk`.
    pub fn size_ok(&self) -> bool {
        self.body.len() + 65 <= params::MAX_TRANSACTION_SIZE
    }
    /// `Tx.valid = sizeOk ∧ Ed25519.verify pk sig hash`.
    pub fn valid(&self) -> bool {
        self.size_ok() && super::ed25519::verify(&self.pk, &self.sig, &self.hash())
    }
}

fn e<T>(m: &str) -> Result<T, String> {
    Err(m.to_string())
}

/// `pTxD1` at `r` (`bs` = the reader's buffer, for the raw / body slices).
pub fn p_tx_d1(r: &mut Reader, bs: &[u8]) -> Result<Tx, String> {
    let start = r.pos;
    let u1 = *bs.get(start).ok_or("decode: transaction version")?;
    let u2 = *bs.get(start + 1).ok_or("decode: transaction version")?;
    let v1 = if u2 == 0 {
        false
    } else if u1 == 1 {
        r.pos += 1;
        true
    } else {
        return e("decode: invalid transaction version tag");
    };
    let signer_id = p_account_id(r, "signer_id")?;
    let pk = p_public_key(r, "tx public_key")?;
    if pk.tag != 0 {
        return e("out of domain (w.tx_shape): non-ED25519 transaction key");
    }
    let nonce = if v1 {
        match mapw(r.u8("TransactionNonce tag"))? {
            0 => mapw(r.u64("nonce"))?,
            1 => return e("out of domain (w.tx_shape): gas-key nonce"),
            _ => return e("decode: TransactionNonce tag"),
        }
    } else {
        mapw(r.u64("nonce"))?
    };
    let receiver_id = p_account_id(r, "receiver_id")?;
    let block_hash = mapw(r.hash("block_hash"))?.to_vec();
    if mapw(r.u32("actions"))? != 1 {
        return e("out of domain (w.tx_shape): not exactly one action");
    }
    if mapw(r.u8("action tag"))? != 3 {
        return e("out of domain (w.tx_shape): action is not Transfer(3)");
    }
    let deposit = mapw(r.u128("deposit"))?;
    let strict = if v1 {
        match mapw(r.u8("NonceMode"))? {
            0 => false,
            1 => true,
            _ => return e("decode: NonceMode tag"),
        }
    } else {
        false
    };
    let body = bs[start..r.pos].to_vec();
    let st = mapw(r.u8("signature type"))?;
    if st != 0 {
        return e(if st == 1 || st == 2 {
            "out of domain (w.tx_shape): non-ED25519 signature"
        } else {
            "decode: unknown signature tag"
        });
    }
    let sig = mapw(r.take(64, "ed25519 signature"))?.to_vec();
    if sig[63] / 32 != 0 {
        return e("decode: ed25519 signature high bits");
    }
    Ok(Tx {
        raw: bs[start..r.pos].to_vec(),
        body,
        signer_id,
        pk: pk.data,
        nonce,
        receiver_id,
        block_hash,
        deposit,
        strict,
        sig,
    })
}

fn transfer_send_fee(recv: &[u8]) -> u128 {
    use params::*;
    if is_near_implicit(recv) {
        TRANSFER_SEND + CREATE_ACCOUNT_SEND + ADD_FULL_ACCESS_KEY_SEND
    } else if is_eth_implicit(recv) || is_near_deterministic(recv) {
        TRANSFER_SEND + CREATE_ACCOUNT_SEND
    } else {
        TRANSFER_SEND
    }
}

fn transfer_exec_fee(recv: &[u8]) -> u128 {
    use params::*;
    if is_near_implicit(recv) {
        TRANSFER_EXEC + CREATE_ACCOUNT_EXEC + ADD_FULL_ACCESS_KEY_EXEC
    } else if is_eth_implicit(recv) || is_near_deterministic(recv) {
        TRANSFER_EXEC + CREATE_ACCOUNT_EXEC
    } else {
        TRANSFER_EXEC
    }
}

/// `TxCost`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TxCost {
    pub gas_burnt: u128,
    pub receipt_gas_price: u128,
    pub burnt_amount: u128,
    pub total_cost: u128,
}

/// `txCost t gasPrice` (`None` ⇔ overflow; `Nat` arithmetic, any value `≥ 2^128` is an
/// overflow, so the checked `u128` operations give the same verdict).
pub fn tx_cost(t: &Tx, gas_price: u128) -> Option<TxCost> {
    let burnt = params::NAR_SEND + transfer_send_fee(&t.receiver_id);
    let remaining = params::NAR_EXEC + transfer_exec_fee(&t.receiver_id);
    if burnt >= 1 << 64 || remaining >= 1 << 64 {
        return None;
    }
    let burnt_amount = gas_price.checked_mul(burnt)?;
    let rgp = gas_price.max(params::MIN_GAS_PURCHASE_PRICE);
    let rem_amount = rgp.checked_mul(remaining)?;
    let gas_cost = burnt_amount.checked_add(rem_amount)?;
    let total = gas_cost.checked_add(t.deposit)?;
    Some(TxCost {
        gas_burnt: burnt,
        receipt_gas_price: rgp,
        burnt_amount,
        total_cost: total,
    })
}

/// `Perm`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Perm {
    FullAccess,
    FunctionCall,
    GasKey,
}

/// `utf8Ok`.
pub fn utf8_ok(s: &[u8]) -> bool {
    let cont = |b: u8| (0x80..=0xBF).contains(&b);
    let mut i = 0;
    while i < s.len() {
        let x = s[i];
        if x < 0x80 {
            i += 1;
        } else if (0xC2..=0xDF).contains(&x) {
            if i + 1 >= s.len() || !cont(s[i + 1]) {
                return false;
            }
            i += 2;
        } else if (0xE0..=0xEF).contains(&x) {
            if i + 2 >= s.len() {
                return false;
            }
            let lo = if x == 0xE0 { 0xA0 } else { 0x80 };
            let hi = if x == 0xED { 0x9F } else { 0xBF };
            if !((lo..=hi).contains(&s[i + 1]) && cont(s[i + 2])) {
                return false;
            }
            i += 3;
        } else if (0xF0..=0xF4).contains(&x) {
            if i + 3 >= s.len() {
                return false;
            }
            let lo = if x == 0xF0 { 0x90 } else { 0x80 };
            let hi = if x == 0xF4 { 0x8F } else { 0xBF };
            if !((lo..=hi).contains(&s[i + 1]) && cont(s[i + 2]) && cont(s[i + 3])) {
                return false;
            }
            i += 4;
        } else {
            return false;
        }
    }
    true
}

struct Cur<'a> {
    b: &'a [u8],
    p: usize,
}

impl Cur<'_> {
    fn take(&mut self, n: usize) -> Option<&[u8]> {
        let s = self.b.get(self.p..self.p.checked_add(n)?)?;
        self.p += n;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        self.take(1).map(|s| s[0])
    }
    fn u32(&mut self) -> Option<u64> {
        self.take(4)
            .map(|s| u32::from_le_bytes(s.try_into().unwrap()) as u64)
    }
    fn string(&mut self) -> Option<()> {
        let n = self.u32()? as usize;
        utf8_ok(self.take(n)?).then_some(())
    }
    fn fc_perm(&mut self) -> Option<()> {
        match self.u8()? {
            0 => {}
            1 => {
                self.take(16)?;
            }
            _ => return None,
        }
        self.string()?;
        let k = self.u32()?;
        for _ in 0..k {
            self.string()?;
        }
        Some(())
    }
}

/// `decodeAccessKey` (`(nonce, perm)`; trailing bytes rejected).
pub fn decode_access_key(b: &[u8]) -> Option<(u64, Perm)> {
    let mut c = Cur { b, p: 0 };
    let n = u64::from_le_bytes(c.take(8)?.try_into().unwrap());
    let perm = match c.u8()? {
        0 => {
            c.fc_perm()?;
            Perm::FunctionCall
        }
        1 => Perm::FullAccess,
        2 => {
            c.take(18)?;
            c.fc_perm()?;
            Perm::GasKey
        }
        3 => {
            c.take(18)?;
            Perm::GasKey
        }
        _ => return None,
    };
    (c.p == b.len()).then_some((n, perm))
}

/// `encodeFullAccessKey nonce = u64 nonce ‖ [1]`.
pub fn encode_full_access_key(nonce: u64) -> Bytes {
    let mut v = u64b(nonce as u128);
    v.push(1);
    v
}

/// `min (height · 10⁶) (2⁶⁴ − 1)`.
pub fn nonce_bound(height: u64) -> u128 {
    (height as u128 * params::NONCE_RANGE_MULTIPLIER).min(u64::MAX as u128)
}

/// `verifyAndCharge a k t c height`: the new amount on success.
pub fn verify_and_charge(
    a: &Account,
    k: (u64, Perm),
    t: &Tx,
    c: &TxCost,
    height: u64,
) -> Option<u128> {
    let (kn, perm) = k;
    if perm == Perm::GasKey {
        return None;
    }
    let nonce_ok = (if t.strict {
        (kn as u128) + 1 < (1u128 << 64) && t.nonce as u128 == kn as u128 + 1
    } else {
        t.nonce > kn
    }) && (t.nonce as u128) < nonce_bound(height);
    if !nonce_ok || a.amount < c.total_cost {
        return None;
    }
    let new_amount = a.amount - c.total_cost;
    // the allowance check is irrelevant: a function-call key fails below anyway
    let required = params::STORAGE_AMOUNT_PER_BYTE.checked_mul(a.storage_usage)?;
    let tot = new_amount.checked_add(a.locked)?;
    if !(tot >= required || a.storage_usage <= params::ZERO_BALANCE_STORAGE_LIMIT) {
        return None;
    }
    match perm {
        Perm::FunctionCall => None,
        _ => Some(new_amount),
    }
}
