#!/usr/bin/env python3
"""Independent Python checker for domain D1a of near/pv86/chunk-validation/v0
(spec/near-chunk-validation-d1a.md): RelD1a = RelD1 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧
A12 ∧ T1, each D0a amendment restated over the D1 witness and the D1 run.

Runs the D1 checker (spec_check_v3_d1.py, unmodified) with the D0a checker's recording trie and
counting ChaCha20 RNG (spec_check_v3_d0a.py, unmodified: importing it installs both into the D0
machinery the D1 checker shares; this module installs the recording trie into the D1 checker
as well), rejects an empty main pre-state (root 0^32: not in RelD1, as Lean `checkD1`, whose
`partialTrie` has no empty-trie case) and, on an accepting case, checks the amendments:
  A1  c.gas_limit        chunk gas_limit of B2's own-shard slot <= 10^15 (claim only)
  A2  w.proof_routing    every receipt of every used source receipt proof routes to the shard
  C0f e.sched_canonical  every 0x0f value read (main pre-state, each implicit pre-state) is
                         absent or V1 with exactly the layout's n^2 links, sender-major
  A7  w.unfolded         unfold_bytes <= B (default B0 = 2,000,000): the D0a measure (unfolded
                         pre tries + unfolded native post tries) over the tries of the D1 run.
                         The main pre trie's keys are the keys the D1 checker reads PLUS the
                         signer-account and access-key keys of EVERY transaction of the witness
                         (Lean `txKeys w.txs`: `checkD1` builds its main partial trie over them,
                         read or not); the main post trie is the D1 checker's (transaction
                         writes, local and incoming receipts, scheduler).
  A8  c.bw_requests      distinct to_shard per chunk slot of every block (claim only)
  A9  e.chacha_words     scheduler runs of all applied transitions draw <= W (W0 = 770,000)
                         ChaCha20 words (counting RNG installed by spec_check_v3_d0a)
  A10 w.path_depth       every used source proof's Merkle path has <= D (Dp0 = 32) items
  A12 c.layout_wf        len(boundary_accounts) + 1 == len(shard_ids) (claim only)
  T1  w.tx_count         the witness's `transactions` has <= N (NT0 = 4,096) entries,
                         duplicates and expired ones included

Violations are reported joined by "," in the order A1, A2, C0f, A7, A8, A9, A10, A12, T1 (the
order of the Lean checkD1a checks; Lean reports only the first failing one).

usage: spec_check_v3_d1a.py [--bound B] [--words-bound W] [--depth-bound D] [--tx-bound N] CASE_DIR...
       one JSON line per case: case, verdict, reason, unfold, chacha_words, max_path_depth,
       tx_count (the measures are null unless the D1 checker accepts; tx_count is reported
       whenever the witness decodes)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d0a as d0a  # noqa: E402  (installs RecTrie / CountingRng into spec_check_v3)
import spec_check_v3_d1 as d1  # noqa: E402
from v3lib.prim import PartialTrie, R, nibbles, ZERO32  # noqa: E402

s3 = d0a.d0
B0, W0, DP0 = d0a.B0, d0a.W0, d0a.DP0
NT0 = 4096
MAX_GAS_LIMIT = d0a.MAX_GAS_LIMIT

# the D1 checker imported PartialTrie from v3lib.prim directly: record its tries too
d1.PartialTrie = d0a.RecTrie
assert s3.PartialTrie is d0a.RecTrie


def decode_witness_d1(witness_b):
    wr = R(witness_b)
    wr.bytes()
    return d1.decode_state_witness_d1(wr.bytes())


def tx_keys(W):
    """Lean `txKeys w.txs`: signer account and (signer, ED25519 key) access key of every
    transaction, in witness order."""
    out = []
    for t in W['txs']:
        out.append(bytes([d1.COL_ACCOUNT]) + t.signer)
        out.append(bytes([d1.COL_ACCESS_KEY]) + t.signer + bytes([d1.COL_ACCESS_KEY]) + bytes([0]) + t.pk)
    return out


def amendments(claim_b, W):
    """Violated A1 / A2 / Canon0f of an accepted (RelD1) case, and the A10 depth (as
    spec_check_v3_d0a.amendments, on the D1 witness)."""
    c = s3.decode_claim(claim_b)
    H = s3.decode_inner_bytes(c['chunk_inner'])
    L = s3.decode_layout(c['epochs'][0]['layout_raw'])
    idx = L.index[H.shard_id]
    blocks = c['blocks']
    for b in blocks:
        b.height = s3.decode_inner_lite(b.lite_raw)['height']
        b.slots = []
        for raw, hi in b.slots_raw:
            s = s3.Slot()
            s.inner = s3.decode_inner_bytes(raw)
            s.height_included = hi
            b.slots.append(s)
    new = [b.slots[idx].height_included == b.height for b in blocks]
    b2i = new.index(True)
    stop = new.index(True, b2i + 1)
    v = []
    own_slot = blocks[b2i].slots[idx]
    if own_slot.inner.gas_limit > MAX_GAS_LIMIT:
        v.append("c.gas_limit")
    routed = True
    depth = 0
    for S in blocks[b2i:stop]:
        for s in S.slots:
            if s.height_included != S.height:
                continue
            receipts, _from, _to, path = W['proofs'][s.inner.chunk_hash]
            depth = max(depth, len(path))
            if any(s3.account_to_shard(L, x.recv) != H.shard_id for x in receipts):
                routed = False
    if not routed:
        v.append("w.proof_routing")
    key = bytes([s3.COL_BW_STATE])
    # plain (non-recording) tries: these reads are not part of the run
    reads = [PartialTrie(W['main']['base_state'], own_slot.inner.prev_state_root).get(key)]
    root = W['main']['post_state_root']
    for T in W['implicit']:
        reads.append(PartialTrie(T['base_state'], root).get(key))
        root = T['post_state_root']
    if not all(d0a.canonical(L, x) for x in reads):
        v.append("e.sched_canonical")
    return v, depth


def check_case(d, bound=B0, words_bound=W0, depth_bound=DP0, tx_bound=NT0):
    """(verdict, reason, unfold_bytes, chacha_words, max_path_depth, tx_count)."""
    d0a._TRIES.clear()
    d0a._RNGS.clear()
    verdict, reason = d1.check_case(d)
    tries = list(d0a._TRIES)
    words = sum(r.words for r in d0a._RNGS)
    try:
        cb = open(os.path.join(d, "claim.bin"), "rb").read()
        wb = open(os.path.join(d, "witness.bin"), "rb").read()
    except OSError as e:
        return "reject", "cannot read case: %s" % e, None, None, None, None
    try:
        W = decode_witness_d1(wb)
        ntx = len(W['txs'])
    except Exception:
        W, ntx = None, None
    # Empty main pre-state: not in RelD1 (Lean `checkD1` reads BufferedReceiptIndices from
    # `partialTrie ws prev_state_root …`; the zero root is an unrevealed `.hash` there, so the
    # read fails after the claim-level checks). The D1 checker treats the zero root as nearcore's
    # empty trie; its main pre trie is the first trie it builds (after the same claim-level
    # checks), so any verdict reached with that trie built becomes this reject (as D0a).
    if tries and tries[0].pre_root == ZERO32 and verdict != "reject":
        return ("reject", "invalid: MissingTrieValue (BufferedReceiptIndices): empty main pre-state",
                None, None, None, ntx)
    if verdict != "accept":
        return verdict, reason, None, None, None, ntx
    try:
        v, depth = amendments(cb, W)
        main = tries[0]
        main.keys.update(tx_keys(W))
        u = d0a.unfold_bytes(tries)
        if not d0a.a8_ok(cb):
            v8 = True
        else:
            v8 = False
        a12 = d0a.a12_ok(cb)
    except Exception as e:  # a bug in this checker
        print("spec_check_v3_d1a: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e), None, None, None, ntx
    if u > bound:
        v.append("w.unfolded")
    if v8:
        v.append("c.bw_requests")
    if words > words_bound:
        v.append("e.chacha_words")
    if depth > depth_bound:
        v.append("w.path_depth")
    if not a12:
        v.append("c.layout_wf")
    if ntx > tx_bound:
        v.append("w.tx_count")
    if v:
        return "out_of_domain", ",".join(v), u, words, depth, ntx
    return "accept", "ok", u, words, depth, ntx


def main():
    args = sys.argv[1:]
    bounds = {"--bound": B0, "--words-bound": W0, "--depth-bound": DP0, "--tx-bound": NT0}
    while args[:1] and args[0] in bounds:
        bounds[args[0]], args = int(args[1]), args[2:]
    for d in args:
        v, reason, u, k, p, n = check_case(d, bounds["--bound"], bounds["--words-bound"],
                                           bounds["--depth-bound"], bounds["--tx-bound"])
        print(json.dumps(dict(case=d, verdict=v, reason=reason, unfold=u, chacha_words=k,
                              max_path_depth=p, tx_count=n)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
