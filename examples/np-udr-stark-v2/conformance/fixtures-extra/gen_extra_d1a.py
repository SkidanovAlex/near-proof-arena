#!/usr/bin/env python3
"""Extra D1a fixtures for the np-udr-stark-v2 prover differentials (lane v3-d1-a7b).

`r5`: the plan §5 R-5 counterexample (docs/zk-formal/V3-D1-PHASE2.md): a D1a statement on which
`checkD1`'s A7ᴰ¹ measure (main pre trie over `mainKeys ++ txKeys`, every transaction's keys) is
larger than what the phase-1 AIR walked (the keys the run reads), by exactly the bytes of a
value that only an *unread* key reveals:

* the main pre-state gets two accounts A = X‖"a1" and B = X‖"b1" whose AccountV1 values are
  byte-identical to the existing account X's (X: a revealed account of the case's own shard);
  both leaves hang below X's (now a branch with X's value), so their leaf nodes are identical
  too (same key suffix, same value);
* three transactions are appended (the base has none): t1 signed by A (`tx_valid` 1, valid
  Ed25519 signature; A has no access key: a candidate that reads A's account, stage 1, fails),
  t2 signed by B (`tx_valid` 0: never read, never walked by the phase-1 AIR), t3 signed by
  C = X‖"b2" (`tx_valid` 1, valid signature; C has no account: its absence walk ends at B's leaf,
  absent by key).  All three fail: no gas, no receipt, no write; three failed outcome leaves.

`checkD1` reveals B's value (B's key is in `txKeys`, B's leaf is on t3's read path, and the store
holds the value's hash because A's value is the same bytes); the phase-1 AIR did not.  B is never
written, so its value is counted in the pre and in the post trie: Δ = 2 · 72.

Hash discipline (as gen_extra_d0a.py / oracle/tools/d1a_mutants_v3.py): B2 = blocks[0] own slot
`prev_state_root` and `tx_root` (its chunk hash = witness entry key re-keyed), blocks[0]
`chunk_headers_root` and hash, the endorsed chunk's `prev_block_hash`; then the main transition's
`post_state_root`, the endorsed chunk's `prev_state_root` and `prev_outcome_root` are fixed
point-wise with the independent Python D1 checker (oracle/tools/spec_check_v3_d1.py), which must
end with `ok`.  Deterministic (keys from fixed seeds).

usage: gen_extra_d1a.py r5 --base CASE_DIR --out OUT_DIR
"""
import argparse
import hashlib
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "oracle", "tools"))
import spec_check_v3_d1a as d1a  # noqa: E402  (installs the recording trie)
import d1a_mutants_v3 as M  # noqa: E402
from v3lib.prim import R, PartialTrie, merklize, nibbles, account_type  # noqa: E402
from v3lib import ed25519  # noqa: E402
sys.path.insert(0, HERE)
import trie_edit  # noqa: E402
from gen_extra_d0a import reachable, restrict  # noqa: E402

s3, d1, d0a = d1a.s3, d1a.d1, d1a.d0a
PREV_OUTCOME_ROOT = slice(65, 97)


def sha(b):
    return hashlib.sha256(b).digest()


def u32(x):
    return struct.pack('<I', x)


# ---------------------------------------------------------------- witness with the main transition
class Witness(M.Witness):
    """d1a_mutants_v3.Witness, with the main transition split out of `head`."""

    def __init__(self, wb):
        super().__init__(wb)
        r = R(wb)
        r.bytes()
        sw = r.bytes()
        r = R(sw)
        r.u8(); r.hash(); r.u8()
        s3.read_inner(r)
        r.u64(); s3.read_signature(r)
        t_off = r.i
        bh = r.hash()
        assert r.u8() == 0
        vals = r.vec(r.bytes)
        post = r.hash()
        assert bytes(self.head[t_off:]) == sw[t_off:r.i]
        self.head = self.head[:t_off]
        self.main = dict(bh=bh, values=vals, post=post)

    def encode(self):
        m = self.main
        tr = (m['bh'] + b'\x00' + u32(len(m['values'])) + b''.join(u32(len(v)) + v for v in m['values']) +
              m['post'])
        head = self.head
        self.head = bytearray(bytes(head) + tr)
        try:
            return super().encode()
        finally:
            self.head = head


def set_endorsed(c, w, sl, val):
    c.b[c.inner_off + sl.start:c.inner_off + sl.stop] = val
    w.head[w.inner_off + sl.start:w.inner_off + sl.stop] = val


# ---------------------------------------------------------------- transactions
def keypair(seed):
    h = hashlib.sha512(seed).digest()
    a = int.from_bytes(h[:32], 'little')
    a &= (1 << 254) - 8
    a |= 1 << 254
    pk = ed25519._compress(ed25519._mul(a, ed25519.BASE))
    return a, h[32:], pk


def transfer(signer, seed, recv, block_hash, nonce=1, deposit=1):
    """A v0 SignedTransaction (one Transfer action), signed with the seed's ED25519 key."""
    a, prefix, pk = keypair(seed)
    body = (u32(len(signer)) + signer + b'\x00' + pk + struct.pack('<Q', nonce) + u32(len(recv)) + recv +
            block_hash + u32(1) + b'\x03' + deposit.to_bytes(16, 'little'))
    sig = ed25519.sign_with_scalar(a, prefix, pk, sha(body))
    assert ed25519.verify(pk, sig, sha(body))
    return body + b'\x00' + sig, pk


# ---------------------------------------------------------------- the Python fixed point
def py_run(cb, wb):
    """D1 checker verdict, the main transition's computed post root, the last outcome root."""
    roots, merk = [], []
    fin, mr = s3.finalize, d1.merkle_root_of_hashes

    def fin2(trie, overlay):
        x = fin(trie, overlay)
        roots.append(x)
        return x

    def mr2(hs):
        x = mr(hs)
        merk.append(x)
        return x
    s3.finalize, d1.merkle_root_of_hashes = fin2, mr2
    try:
        d1.check_case_inner(cb, wb)
        v = "ok"
    except Exception as e:  # noqa: BLE001
        v = "%s: %s" % (type(e).__name__, e)
    finally:
        s3.finalize, d1.merkle_root_of_hashes = fin, mr
    return v, roots, merk


def fixpoint(c, w, log):
    for _ in range(8):
        cb, wb = bytes(c.b), w.encode()
        v, roots, merk = py_run(cb, wb)
        if v == "ok":
            return cb, wb
        log.append(v)
        if "main transition post_state_root mismatch" in v:
            w.main['post'] = roots[0]
        elif "InvalidStateRoot" in v:
            set_endorsed(c, w, M.PREV_STATE_ROOT, roots[-1])
        elif "InvalidOutcomesProof" in v:
            set_endorsed(c, w, PREV_OUTCOME_ROOT, merk[-1])
        else:
            raise SystemExit("python checker: %s" % v)
    raise SystemExit("no fixed point: %s" % log)


def measures(case):
    """(verdict, reason, unfold over mainKeys ++ txKeys, unfold over the read keys only)."""
    d0a._TRIES.clear()
    d0a._RNGS.clear()
    verdict, reason = d1.check_case(case)
    tries = list(d0a._TRIES)
    if verdict != "accept":
        return verdict, reason, None, None
    read_only = d0a.unfold_bytes(tries)
    v = d1a.check_case(case)
    return v[0], v[1], v[2], read_only


# ---------------------------------------------------------------- r5
def r5(base, out):
    cb = open(os.path.join(base, "claim.bin"), "rb").read()
    wb = open(os.path.join(base, "witness.bin"), "rb").read()
    c, w = M.Claim(cb), Witness(wb)
    if w.txs:
        raise SystemExit("r5: base must have no transactions")
    idx = M.own_index(c)
    if not M.b2_is_block0(c, idx)[0]:
        raise SystemExit("r5: B2 is not blocks[0]")
    cl = s3.decode_claim(cb)
    if len(cl['apply_facts']) != 1:
        raise SystemExit("r5: base has implicit transitions")
    H = s3.decode_inner_bytes(cl['chunk_inner'])
    L = s3.decode_layout(cl['epochs'][0]['layout_raw'])
    inner = M.Claim(cb).slot_inner(0, idx)
    root = bytes(inner[M.PREV_STATE_ROOT])
    store = {sha(v): v for v in w.main['values']}
    # X: the first (by key) revealed AccountV1 of the own shard such that A, B, C route there too
    # and every key the run reads stays determined after the insertion (A's access key, C's
    # account)
    pk_a = keypair(b"near-arena/r5/A")[2]
    X = None
    for k, vr in sorted(trie_edit.leaves(trie_edit.load(store, root)), key=lambda kv: kv[0]):
        if len(k) % 2 or k[:2] != [0, 0] or vr[0] != 72 or vr[1] not in store:
            continue
        xid = bytes(16 * k[i] + k[i + 1] for i in range(2, len(k), 2))
        ids = [xid, xid + b"a1", xid + b"b1", xid + b"b2"]
        if not all(account_type(i) == 'named' and s3.account_to_shard(L, i) == H.shard_id for i in ids):
            continue
        kx = (b"\x00" + xid).hex()
        ops = ["put:%s=@%s" % ((b"\x00" + ids[1]).hex(), kx), "put:%s=@%s" % ((b"\x00" + ids[2]).hex(), kx)]
        try:
            nr, ne, _ = trie_edit.apply_ops(store, root, ops)
            st = dict(store)
            st.update(ne)
            t = PartialTrie(list(st.values()), nr)
            for key in [b"\x00" + ids[1], b"\x00" + ids[3], b"\x02" + ids[1] + b"\x02\x00" + pk_a]:
                t.get(key)
        except Exception:  # noqa: BLE001
            continue
        X, new_root, new_entries = xid, nr, ne
        break
    if X is None:
        raise SystemExit("r5: no suitable account X")
    A, B, Cc = X + b"a1", X + b"b1", X + b"b2"
    store.update(new_entries)
    w.main['values'] = restrict(w.main['values'], store, reachable(store, new_root))
    # the three transactions
    bh = bytes(c.b[c.inner_off + 1:c.inner_off + 33])
    t1, pk_a = transfer(A, b"near-arena/r5/A", X, bh)
    t2, pk_b = transfer(B, b"near-arena/r5/B", X, bh)
    t3, pk_c = transfer(Cc, b"near-arena/r5/C", X, bh)
    w.txs = [t1, t2, t3]
    c.set_tx_valid([1, 0, 1])
    old = M.chunk_hash(inner)
    inner[M.TX_ROOT] = merklize(w.txs)
    inner[M.PREV_STATE_ROOT] = new_root
    c.set_slot_inner(0, idx, inner)
    if M.rekey(w, old, M.chunk_hash(inner)) != 1:
        raise SystemExit("r5: own-slot witness entry not found")
    h = c.fix_block0()
    w.set_inner_prev_hash(h)
    log = []
    cbo, wbo = fixpoint(c, w, log)
    od = os.path.join(out, "r5-ab-identical")
    os.makedirs(od, exist_ok=True)
    open(os.path.join(od, "claim.bin"), "wb").write(cbo)
    open(os.path.join(od, "witness.bin"), "wb").write(wbo)
    verdict, reason, unfold, read_only = measures(od)
    vlen = len(store[trie_edit.get_vref(trie_edit.load(store, new_root), nibbles(b"\x00" + B))[1]])
    meta = {
        "case": "r5-ab-identical", "kind": "extra_d1a", "family": "r5.unread_key_reveals_value",
        "base": os.path.relpath(os.path.normpath(base), REPO),
        "expected_verdict_d1a": "accept", "expected_rel_d1": True,
        "construction": "examples/np-udr-stark-v2/conformance/fixtures-extra/gen_extra_d1a.py r5 "
                        "(see its docstring; hashes restored, Python fixed point)",
        "accounts": {"X": X.decode(), "A": A.decode(), "B": B.decode(), "C": Cc.decode()},
        "public_keys": {"A": pk_a.hex(), "B": pk_b.hex(), "C": pk_c.hex()},
        "transactions": [
            {"i": 0, "signer": "A", "tx_valid": 1, "role": "candidate, reads A's account, no access key (stage 1), fails"},
            {"i": 1, "signer": "B", "tx_valid": 0, "role": "not a candidate: B's keys only in txKeys (unread)"},
            {"i": 2, "signer": "C", "tx_valid": 1, "role": "candidate, C absent: absence walk ends at B's leaf"}],
        "python_fixpoint_log": log,
        "claim_sha256": sha(cbo).hex(), "witness_sha256": sha(wbo).hex(),
        "python_d1a": {"verdict": verdict, "reason": reason, "unfold": unfold},
        "unfold_read_keys_only": read_only,
        "unfold_delta": None if unfold is None else unfold - read_only,
        "b_value_len": vlen,
        "nearcore": "not judged (the mutated blocks are not in its store)",
    }
    open(os.path.join(od, "meta.json"), "w").write(json.dumps(meta, indent=1) + "\n")
    print(json.dumps({"case": od, "verdict": verdict, "unfold": unfold, "read_only": read_only,
                      "delta": meta["unfold_delta"], "b_value_len": vlen}))
    if verdict != "accept" or unfold - read_only != 2 * vlen:
        raise SystemExit("r5: unexpected measures")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("op", choices=["r5"])
    ap.add_argument("--base", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    r5(a.base, a.out)


if __name__ == "__main__":
    main()
