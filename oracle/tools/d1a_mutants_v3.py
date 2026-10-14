#!/usr/bin/env python3
"""Constructed D1a boundary mutants (spec/near-chunk-validation-d1a.md §4), derived from accepted
D1 cases by byte surgery that restores every hash the relation checks.

Families (each on a base case whose segment starts at B2 = blocks[0], i.e. no implicit
transition, accepted by the D1a checkers):

* `w.tx_count_at_bound` / `w.tx_count_over` (T1): the witness's `transactions` is padded with
  copies of its last transaction to exactly NT0 = 4,096 / NT0 + 1 = 4,097 entries, and the
  claim's `tx_valid` with copies of its last flag. Copies have the hash of an earlier
  transaction, so `process_transactions` skips them (`UniqueChunkTransactions`, PV 85: no
  outcome, no read, no write); their keys are those of the copied transaction, so the tries and
  every measure but `tx_count` are unchanged. B2's own-slot `tx_root` is recomputed over the
  padded list, hence its chunk hash (the key of its source-proof entry), B2's
  `chunk_headers_root` and hash, and the endorsed chunk's `prev_block_hash` (claim and witness).
  `RelD1` holds by construction; expected `accept` at the bound and `out_of_domain`
  (`w.tx_count`) over it.
* `w.path_depth_at_bound` / `w.path_depth_over` (A10ᴰ¹): as the D0a oracle's path mutants
  (oracle/v3-d0a/src/pathmut.rs), on the D1 witness: the first new source chunk of B2 whose
  proof is in the witness gets deterministic synthetic Merkle siblings up to exactly Dp0 = 32 /
  33 items; its `prev_outgoing_receipts_root`, chunk hash (entry key), B2's
  `chunk_headers_root` and hash and the endorsed `prev_block_hash` are recomputed.
* `w.empty_pre_state`: B2's own-slot `prev_state_root` set to 0^32 (nearcore's empty-trie
  root), hashes restored as above: not in RelD1 (Lean `checkD1` reads BufferedReceiptIndices
  from an unrevealed root), expected `reject`.

Each mutant is checked here with the Python D1a checker (must give the expected verdict) and
written to OUT/<base>-<family>/{claim.bin, witness.bin, meta.json}; meta.json carries
`expected_verdict_d1a`, `expected_reason_d1a`, `expected_rel_d1` and the provenance.

usage: d1a_mutants_v3.py --out DIR [--families F,...] [--limit K] BASE_CASE_DIR...
"""
import argparse
import hashlib
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d1a as d1a  # noqa: E402
from v3lib.prim import R, compute_root_from_path, merklize  # noqa: E402

s3 = d1a.s3
d1 = d1a.d1
NT0 = d1a.NT0
DP0 = d1a.DP0
TAG = b"near-arena/v3-d1a/w.path_depth/synthetic-sibling"
# chunk inner byte offsets (V4/V5, spec_check_v3.read_inner)
PREV_BLOCK_HASH = slice(1, 33)
PREV_STATE_ROOT = slice(33, 65)
ENCODED_MERKLE_ROOT = slice(97, 129)
PREV_OUTGOING_ROOT = slice(185, 217)
TX_ROOT = slice(217, 249)
CHUNK_HEADERS_ROOT = slice(64, 96)  # in the block's inner_rest


def sha(b):
    return hashlib.sha256(b).digest()


def chunk_hash(inner):
    return sha(sha(bytes(inner)) + bytes(inner[ENCODED_MERKLE_ROOT]))


class Claim:
    """claim.bin with the byte offsets of the fields the mutants edit."""

    def __init__(self, b):
        self.b = bytearray(b)
        r = R(b)
        r.bytes(); r.bytes(); r.u32(); r.bytes(); r.hash()
        n = r.u32()
        self.inner_off = r.i
        r.i += n
        self.blocks = []
        for _ in range(r.u32()):
            blk = {}
            r.u8()
            blk['prev_off'] = r.i
            r.hash()
            n = r.u32(); blk['lite'] = (r.i, n); r.i += n
            n = r.u32(); blk['rest'] = (r.i, n); r.i += n
            slots = []
            for _ in range(r.u32()):
                n = r.u32(); off = r.i; r.i += n
                slots.append((off, n, r.u64()))
            blk['slots'] = slots
            self.blocks.append(blk)
        c = s3.decode_claim(b)
        self.tx_valid = c['tx_valid']
        assert c['genesis_chunk_extra'] is None
        self.tail_len = 4 + len(self.tx_valid) + 1
        assert bytes(self.b[-self.tail_len:]) == struct.pack('<I', len(self.tx_valid)) + bytes(self.tx_valid) + b'\x00'

    def inner(self):
        n = struct.unpack('<I', self.b[self.inner_off - 4:self.inner_off])[0]
        return self.b[self.inner_off:self.inner_off + n]

    def slot_inner(self, bi, j):
        off, n, _ = self.blocks[bi]['slots'][j]
        return self.b[off:off + n]

    def set_slot_inner(self, bi, j, inner):
        off, n, _ = self.blocks[bi]['slots'][j]
        assert len(inner) == n
        self.b[off:off + n] = inner

    def block_hash(self, bi):
        blk = self.blocks[bi]
        lo, ln = blk['lite']
        ro, rn = blk['rest']
        prev = bytes(self.b[blk['prev_off']:blk['prev_off'] + 32])
        return sha(sha(sha(bytes(self.b[lo:lo + ln])) + sha(bytes(self.b[ro:ro + rn]))) + prev)

    def fix_block0(self):
        """chunk_headers_root of blocks[0] from its slots, then the endorsed prev_block_hash."""
        blk = self.blocks[0]
        leaves = [chunk_hash(self.b[o:o + n]) + struct.pack('<Q', hi) for o, n, hi in blk['slots']]
        ro, _ = blk['rest']
        self.b[ro + CHUNK_HEADERS_ROOT.start:ro + CHUNK_HEADERS_ROOT.stop] = merklize(leaves)
        h = self.block_hash(0)
        self.b[self.inner_off + PREV_BLOCK_HASH.start:self.inner_off + PREV_BLOCK_HASH.stop] = h
        return h

    def set_tx_valid(self, flags):
        self.b = self.b[:-self.tail_len] + struct.pack('<I', len(flags)) + bytes(flags) + b'\x00'
        self.tx_valid = list(flags)
        self.tail_len = 4 + len(flags) + 1


class Witness:
    """witness.bin (format id ‖ state witness ‖ codes) split into editable sections."""

    def __init__(self, wb):
        r = R(wb)
        self.fmt = r.bytes()
        sw = r.bytes()
        self.codes = wb[r.i:]
        r = R(sw)
        r.u8(); r.hash()
        assert r.u8() == 2
        self.inner_off = r.i
        s3.read_inner(r)
        r.u64(); s3.read_signature(r)
        s3.read_transition(r)
        self.head = bytearray(sw[:r.i])
        self.entries = []  # [key, receipts_raw, from, to, path]
        for _ in range(r.u32()):
            key = r.hash()
            st = r.i
            rs = r.vec(lambda: s3.read_receipt(r))
            raw = sw[st:r.i]
            fr, to = r.u64(), r.u64()
            path = []
            for _ in range(r.u32()):
                path.append((r.hash(), r.u8()))
            self.entries.append([key, raw, fr, to, path, rs])
        self.arh = r.hash()
        st = r.i
        self.txs = [t.raw for t in r.vec(lambda: d1.read_tx(r))]
        self.rest = sw[r.i:]

    def set_inner_prev_hash(self, h):
        self.head[self.inner_off + PREV_BLOCK_HASH.start:self.inner_off + PREV_BLOCK_HASH.stop] = h

    def set_inner(self, inner):
        self.head[self.inner_off:self.inner_off + len(inner)] = inner

    def encode(self):
        sw = bytes(self.head) + struct.pack('<I', len(self.entries))
        for key, raw, fr, to, path, _rs in self.entries:
            sw += key + raw + struct.pack('<QQI', fr, to, len(path))
            sw += b''.join(h + bytes([d]) for h, d in path)
        sw += self.arh + struct.pack('<I', len(self.txs)) + b''.join(self.txs) + self.rest
        return struct.pack('<I', len(self.fmt)) + self.fmt + struct.pack('<I', len(sw)) + sw + self.codes


def own_index(c):
    cl = s3.decode_claim(bytes(c.b))
    H = s3.decode_inner_bytes(cl['chunk_inner'])
    L = s3.decode_layout(cl['epochs'][0]['layout_raw'])
    return L.index[H.shard_id]


def b2_is_block0(c, idx):
    lite = s3.decode_inner_lite(bytes(c.b[c.blocks[0]['lite'][0]:c.blocks[0]['lite'][0] + c.blocks[0]['lite'][1]]))
    return c.blocks[0]['slots'][idx][2] == lite['height'], lite['height']


def rekey(w, old, new):
    n = 0
    for e in w.entries:
        if e[0] == old:
            e[0] = new
            n += 1
    return n


def finish(c, w):
    h = c.fix_block0()
    w.set_inner_prev_hash(h)
    assert bytes(c.inner()) == bytes(w.head[w.inner_off:w.inner_off + len(c.inner())])
    return bytes(c.b), w.encode()


def mut_tx_count(cb, wb, n_target):
    c, w = Claim(cb), Witness(wb)
    if not w.txs or len(w.txs) > n_target:
        return None
    idx = own_index(c)
    new, _ = b2_is_block0(c, idx)
    if not new:
        return None
    w.txs = w.txs + [w.txs[-1]] * (n_target - len(w.txs))
    c.set_tx_valid(c.tx_valid + [c.tx_valid[-1]] * (n_target - len(c.tx_valid)))
    inner = c.slot_inner(0, idx)
    old = chunk_hash(inner)
    inner[TX_ROOT] = merklize(w.txs)
    c.set_slot_inner(0, idx, inner)
    rekey(w, old, chunk_hash(inner))
    return finish(c, w)


def synthetic(i):
    return (sha(TAG + struct.pack('<Q', i)), 0 if i % 2 == 0 else 1)


def mut_path_depth(cb, wb, depth):
    c, w = Claim(cb), Witness(wb)
    _, height = b2_is_block0(c, own_index(c))
    if not b2_is_block0(c, own_index(c))[0]:
        return None
    for j, (o, n, hi) in enumerate(c.blocks[0]['slots']):
        if hi != height:
            continue
        inner = c.slot_inner(0, j)
        key = chunk_hash(inner)
        ents = [e for e in w.entries if e[0] == key]
        if not ents:
            continue
        e = ents[-1]
        if len(e[4]) > depth:
            continue
        leaf = sha(sha(struct.pack('<Q', e[3]) + e[1]))
        if compute_root_from_path(e[4], leaf) != bytes(inner[PREV_OUTGOING_ROOT]):
            return None
        e[4] = e[4] + [synthetic(i) for i in range(len(e[4]), depth)]
        inner[PREV_OUTGOING_ROOT] = compute_root_from_path(e[4], leaf)
        c.set_slot_inner(0, j, inner)
        rekey(w, key, chunk_hash(inner))
        return finish(c, w)
    return None


def mut_empty_pre(cb, wb):
    c, w = Claim(cb), Witness(wb)
    idx = own_index(c)
    if not b2_is_block0(c, idx)[0]:
        return None
    inner = c.slot_inner(0, idx)
    old = chunk_hash(inner)
    inner[PREV_STATE_ROOT] = bytes(32)
    c.set_slot_inner(0, idx, inner)
    rekey(w, old, chunk_hash(inner))
    return finish(c, w)


FAMILIES = {
    "w.tx_count_at_bound": (lambda cb, wb: mut_tx_count(cb, wb, NT0), "accept", None),
    "w.tx_count_over": (lambda cb, wb: mut_tx_count(cb, wb, NT0 + 1), "out_of_domain", "w.tx_count"),
    "w.path_depth_at_bound": (lambda cb, wb: mut_path_depth(cb, wb, DP0), "accept", None),
    "w.path_depth_over": (lambda cb, wb: mut_path_depth(cb, wb, DP0 + 1), "out_of_domain", "w.path_depth"),
    "w.empty_pre_state": (mut_empty_pre, "reject", None),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--families", default=",".join(FAMILIES))
    ap.add_argument("--limit", type=int, default=0, help="at most K mutants per family (0 = all)")
    ap.add_argument("bases", nargs="+")
    a = ap.parse_args()
    fams = a.families.split(",")
    made = {f: 0 for f in fams}
    for base in a.bases:
        cb = open(os.path.join(base, "claim.bin"), "rb").read()
        wb = open(os.path.join(base, "witness.bin"), "rb").read()
        if d1a.check_case(base)[0] != "accept":
            continue
        for f in fams:
            if a.limit and made[f] >= a.limit:
                continue
            fn, ev, er = FAMILIES[f]
            r = fn(cb, wb)
            if r is None:
                continue
            name = os.path.basename(os.path.normpath(base)) + "-" + f
            od = os.path.join(a.out, name)
            os.makedirs(od, exist_ok=True)
            open(os.path.join(od, "claim.bin"), "wb").write(r[0])
            open(os.path.join(od, "witness.bin"), "wb").write(r[1])
            v = d1a.check_case(od)
            ok = v[0] == ev and (er is None or er in v[1].split(","))
            meta = {"case": name, "kind": "mutant_d1a", "family": f, "base": os.path.normpath(base),
                    "expected_verdict_d1a": ev, "expected_reason_d1a": er,
                    "expected_rel_d1": f != "w.empty_pre_state",
                    "construction": "oracle/tools/d1a_mutants_v3.py (hashes restored; see its docstring)",
                    "claim_sha256": sha(r[0]).hex(), "witness_sha256": sha(r[1]).hex(),
                    "python_d1a": {"verdict": v[0], "reason": v[1], "unfold": v[2], "tx_count": v[5],
                                   "max_path_depth": v[4]}}
            open(os.path.join(od, "meta.json"), "w").write(json.dumps(meta, indent=1) + "\n")
            print(json.dumps({"case": od, "family": f, "python": v[0], "reason": v[1], "ok": ok}))
            sys.stdout.flush()
            if not ok:
                raise SystemExit("mutant %s: Python D1a says %s (%s), expected %s" % (od, v[0], v[1], ev))
            made[f] += 1
    print(json.dumps(made), file=sys.stderr)


if __name__ == "__main__":
    main()
