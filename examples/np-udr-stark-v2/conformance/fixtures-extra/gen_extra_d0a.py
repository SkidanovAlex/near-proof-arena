#!/usr/bin/env python3
"""Extra D0a fixtures for the np-udr-stark-v2 prover differentials (lane v3-prover-fixtures).

The public D0a fixtures (`oracle/fixtures/v3/public-d0a/d0`, nearcore chaingen seed 4243) never
repeat a source key and never read an empty value.  This tool derives new claims + witnesses from
them by structural surgery, recomputing every hash the relation checks, so that the prover's
duplicate-source and zero-length-value paths run on real (accepted) statements:

* `dup` operations (`--dup DSTBLK:DSTSLOT=SRCBLK:SRCSLOT`, block indices into `claim.blocks`,
  0 = newest): the chunk inner of a new source slot is copied over another new source slot (whose
  height_included is kept).  Both slots must carry proofs with no receipts.  The copied slot has
  the same chunk hash, `from_shard` and `prev_outgoing_receipts_root` as the original, so the
  repeat is *consistent* (public dup byte 1, `Public.sourceDupByte`).  The replaced slot's old
  witness entry stays as the extra, unused entry that `RelD0` requires per duplicate (spec v0a
  §2.5; `oracle/tools/dupkey_v3.py` is the 2-copy, same-block special case of this).
* empty-value operations.  `applyNewChunk` reads `BufferedReceiptGroupsQueueData(S)`
  (trie key 0x10 ‖ u64 S) of every shard `S` listed in `BufferedReceiptIndices` (0x0d) with
  `readKey` and ignores the value; it is the only D0 read whose value may be empty (account and
  access-key values must decode, queue indices must be 16 bytes or absent, the scheduler state
  must decode).  A present empty value there is a zero-length value record of the native forest
  (VPRE job of length 0, `vz` row).
  - `--groups S=empty|HEX,...`: overwrite the groups data of shards already listed by the base;
  - `--buffered S[=HEX|=absent],...`: the base has no indices; insert indices listing `S` with
    empty queues (first = next = 7) and set each groups value (default: empty; `absent` = not
    inserted, a proven-absent read).

After the surgery the claim/witness hash discipline is restored: changed slots ->
`chunk_headers_root`; the own slot's `prev_state_root` (pre-state change) -> its chunk hash and
the witness entry key; block hashes down to `blocks[0]` -> the endorsed chunk's
`prev_block_hash` (claim and witness header); then the post-state roots (main transition,
implicit transitions with their base_state re-recorded along keys 0x07/0x0f, the endorsed
chunk's `prev_state_root`) are fixed point-wise with the independent Python reference checker
(`oracle/tools/spec_check_v3.py`), which must end with verdict ok.  Acceptance is then decided by
the proved Lean `checkD0a B0` (`nearspec-v3-check-d0a`), see README.md.

usage: gen_extra_d0a.py --base CASE_DIR --out OUT_DIR [--dup ...]... [--buffered ...] [--note TXT]
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
import spec_check_v3 as d0  # noqa: E402
import spec_check_v3_d0a as d0a  # noqa: E402
from v3lib import sched as v3sched  # noqa: E402
from v3lib.prim import R, PartialTrie, decode_node, nibbles  # noqa: E402
sys.path.insert(0, HERE)
import trie_edit  # noqa: E402

ZERO32 = bytes(32)


def sha(b):
    return hashlib.sha256(b).digest()


def u32(x):
    return struct.pack('<I', x)


def u64(x):
    return struct.pack('<Q', x)


def bstr(b):
    return u32(len(b)) + b


# ---------------------------------------------------------------- claim
def parse_claim(b):
    r = R(b)
    r.bytes(); r.bytes(); r.u32(); r.bytes(); r.hash()
    ci_start = r.i
    r.bytes()
    ci_end = r.i
    blocks = []
    for _ in range(r.u32()):
        v = r.u8(); ph = r.hash(); lite = r.bytes(); rest = r.bytes()
        slots = [[r.bytes(), r.u64()] for _ in range(r.u32())]
        blocks.append(dict(v=v, ph=ph, lite=lite, rest=rest, slots=slots))
    return dict(prefix=b[:ci_start], inner=b[ci_start + 4:ci_end], blocks=blocks, tail=b[r.i:])


def enc_claim(c):
    out = c['prefix'] + bstr(c['inner']) + u32(len(c['blocks']))
    for x in c['blocks']:
        out += bytes([x['v']]) + x['ph'] + bstr(x['lite']) + bstr(x['rest']) + u32(len(x['slots']))
        for s, h in x['slots']:
            out += bstr(s) + u64(h)
    return out + c['tail']


def merkle(hashes):
    if not hashes:
        return bytes(32)
    while len(hashes) > 1:
        nxt = [sha(hashes[i] + hashes[i + 1]) for i in range(0, len(hashes) - 1, 2)]
        if len(hashes) % 2:
            nxt.append(hashes[-1])
        hashes = nxt
    return hashes[0]


def bhash(x):
    return sha(sha(sha(x['lite']) + sha(x['rest'])) + x['ph'])


def chunk_hash(inner):
    return sha(sha(inner) + inner[97:129])


def height(x):
    return d0.decode_inner_lite(x['lite'])['height']


def bw_span(inner):
    """Byte span of the tagged `BandwidthRequests` inside a chunk inner (V4/V5)."""
    r = R(inner)
    if r.u8() not in (3, 4):
        raise SystemExit("--bw: unsupported chunk inner version")
    for _ in range(4):
        r.hash()
    for _ in range(5):
        r.u64()
    r.u128(); r.hash(); r.hash()
    r.vec(lambda: d0.read_validator_stake(r))
    d0.read_congestion(r)
    a = r.i
    d0.read_bw_requests(r)
    return a, r.i


def set_bw(inner, reqs):
    a, b = bw_span(inner)
    return inner[:a] + b'\x00' + u32(len(reqs)) + b''.join(struct.pack('<H', t) + bm for t, bm in reqs) + inner[b:]


def fix_headers_root(x):
    leaves = [sha(chunk_hash(s) + u64(h)) for s, h in x['slots']]
    x['rest'] = x['rest'][:64] + merkle(leaves) + x['rest'][96:]


# ---------------------------------------------------------------- witness
def parse_witness(wb):
    r = R(wb)
    fmt = r.bytes()
    sw = r.bytes()
    codes = wb[r.i:]
    s = R(sw)
    head_start = s.i
    s.u8(); s.hash(); s.u8()
    inner_start = s.i
    d0.read_inner(s)
    inner_end = s.i
    s.u64(); d0.read_signature(s)
    mid = sw[inner_end:s.i]
    main = read_tr(s)
    entries = []
    for _ in range(s.u32()):
        st = s.i
        key = s.hash()
        rs = s.vec(lambda: d0.read_receipt(s))
        s.u64(); s.u64(); s.vec(lambda: (s.hash(), s.u8()))
        entries.append(dict(key=key, body=sw[st + 32:s.i], n=len(rs)))
    applied = s.hash()
    assert s.u32() == 0
    implicit = s.vec(lambda: read_tr(s))
    assert s.u32() == 0
    s.end()
    return dict(fmt=fmt, codes=codes, head=sw[head_start:inner_start], inner=sw[inner_start:inner_end],
                mid=mid, main=main, entries=entries, applied=applied, implicit=implicit)


def read_tr(s):
    bh = s.hash()
    assert s.u8() == 0
    vals = s.vec(s.bytes)
    return dict(bh=bh, values=vals, post=s.hash())


def enc_tr(t):
    return t['bh'] + b'\x00' + u32(len(t['values'])) + b''.join(bstr(v) for v in t['values']) + t['post']


def enc_witness(w):
    sw = (w['head'] + w['inner'] + w['mid'] + enc_tr(w['main']) + u32(len(w['entries'])) +
          b''.join(e['key'] + e['body'] for e in w['entries']) + w['applied'] + u32(0) +
          u32(len(w['implicit'])) + b''.join(enc_tr(t) for t in w['implicit']) + u32(0))
    return bstr(w['fmt']) + bstr(sw) + w['codes']


# ---------------------------------------------------------------- trie helpers
def reachable(store, root):
    """Hashes of every node / value reachable from `root` through the store."""
    seen, stack = set(), [(root, False)]
    while stack:
        h, is_value = stack.pop()
        if h in seen or h not in store:
            continue
        seen.add(h)
        if is_value:
            continue
        n = decode_node(store[h])
        if n.kind == 'leaf':
            stack.append((n.vref[1], True))
        elif n.kind == 'ext':
            stack.append((n.child, False))
        else:
            if n.vref is not None:
                stack.append((n.vref[1], True))
            stack.extend((c, False) for c in n.children.values())
    return seen


def path_closure(store, root, keys):
    """Nodes on the nibble paths of `keys` (and the values at those keys) present in store."""
    out = set()
    for k in keys:
        nib = nibbles(k)
        h = root
        while h in store:
            out.add(h)
            n = decode_node(store[h])
            if n.kind == 'leaf':
                if n.key == nib and n.vref[1] in store:
                    out.add(n.vref[1])
                break
            if n.kind == 'ext':
                if nib[:len(n.key)] != n.key:
                    break
                nib = nib[len(n.key):]
                h = n.child
                continue
            if not nib:
                if n.vref is not None and n.vref[1] in store:
                    out.add(n.vref[1])
                break
            if nib[0] not in n.children:
                break
            h = n.children[nib[0]]
            nib = nib[1:]
    return out


def restrict(values, store, keep):
    """Old order for the kept old values, then the new ones (sorted by hash, deterministic)."""
    old = []
    seen = set()
    for v in values:
        h = sha(v)
        if h in keep and h not in seen:
            old.append(v)
            seen.add(h)
    new = [store[h] for h in sorted(keep - seen)]
    return old + new


# ---------------------------------------------------------------- the Python fixed point
class Capture:
    def __init__(self):
        self.calls = []
        self.orig = d0.finalize

    def __enter__(self):
        def fin(trie, overlay):
            root = self.orig(trie, overlay)
            self.calls.append((trie, root))
            return root
        d0.finalize = fin
        return self

    def __exit__(self, *a):
        d0.finalize = self.orig


def py_check(cb, wb):
    with Capture() as cap:
        try:
            v = d0.check_case_inner(cb, wb)
            return v, cap.calls
        except Exception as e:  # noqa: BLE001
            return "%s: %s" % (type(e).__name__, e), cap.calls


def fixpoint(c, w, claim_hashes, log):
    for _ in range(4 + 2 * len(w['implicit'])):
        cb, wb = enc_claim(c), enc_witness(w)
        v, calls = py_check(cb, wb)
        if v == "ok":
            return cb, wb
        log.append(v)
        if "main transition post_state_root mismatch" in v:
            w['main']['post'] = calls[0][1]
        elif "implicit transition post_state_root mismatch" in v:
            i = len(calls) - 2          # index of the failing implicit transition
            w['implicit'][i]['post'] = calls[-1][1]
        elif "InvalidStateRoot" in v:
            root = calls[-1][1]
            c['inner'] = c['inner'][:33] + root + c['inner'][65:]
            w['inner'] = c['inner']
        elif "MissingTrieValue" in v and w['implicit'] and len(calls) >= 1:
            # re-record the implicit base_state along 0x07 / 0x0f from the previous post trie
            i = len(calls) - 1
            trie, root = calls[-1]
            T = w['implicit'][i]
            store = dict(trie.store)
            for x in T['values']:
                store.setdefault(sha(x), x)
            keep = path_closure(store, root, [bytes([7]), bytes([15])])
            T['values'] = restrict(T['values'], store, keep)
        else:
            raise SystemExit("python checker: %s" % v)
    raise SystemExit("no fixed point: %s" % log)


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--dup", action="append", default=[], help="DSTBLK:DSTSLOT=SRCBLK:SRCSLOT")
    ap.add_argument("--buffered", default=None, help="S[=HEX|=absent],...  new indices (default groups value: empty)")
    ap.add_argument("--groups", default=None, help="S=empty|HEX,...  overwrite groups data of listed shards")
    ap.add_argument("--bw", action="append", default=[],
                    help="BLK:SLOT=TO/BITS[,TO/BITS...]  set a slot's BandwidthRequests (SLOT or TO may be "
                         "'*' = every slot / every layout shard id; BITS = 10 hex digits (5-byte bitmap); "
                         "empty right-hand side = no requests)")
    ap.add_argument("--state", action="append", default=[],
                    help="main pre-state trie surgery, in order: del:KEYHEX | put:KEYHEX=VALHEX | "
                         "put:KEYHEX=@SRCKEYHEX | keep:PFXHEX[,PFXHEX...] (rebuild from the revealed keys "
                         "with these byte prefixes) | ext0:NIBBLES (non-canonical empty-key extension above "
                         "the node at that nibble path); see trie_edit.py")
    ap.add_argument("--note", default="")
    ap.add_argument("--drop-extra", action="store_true",
                    help="negative: after the fixed point, drop the replaced slots' (extra, unused) "
                         "witness entries; RelD0 then fails (distinctKeys != #used lists)")
    a = ap.parse_args()

    cb0 = open(os.path.join(a.base, "claim.bin"), "rb").read()
    wb0 = open(os.path.join(a.base, "witness.bin"), "rb").read()
    c, w = parse_claim(cb0), parse_witness(wb0)
    assert enc_claim(c) == cb0 and enc_witness(w) == wb0, "codec round trip"
    assert w['inner'] == c['inner']
    blocks = c['blocks']
    old_hashes = [bhash(x) for x in blocks]
    heights = [height(x) for x in blocks]
    H = d0.decode_inner_bytes(c['inner'])
    claim_d = d0.decode_claim(cb0)
    L = d0.decode_layout(claim_d['epochs'][0]['layout_raw'])
    idx = L.index[H.shard_id]
    b2i = next(i for i, x in enumerate(blocks) if x['slots'][idx][1] == heights[i])
    nrec = {e['key']: e['n'] for e in w['entries']}
    changed = set()
    ops = []
    rekey = {}          # (block, slot) -> original chunk hash, for slots whose inner is edited in place

    def edit_slot(j, k, new_inner, copies=True):
        """Replace a chunk header in place where it is new (slot height = block height) and in
        every copy of it in newer blocks (a missed slot repeats the header), so the claim stays
        consistent; older blocks (receipt-shuffle seeds, source hashes) are untouched.
        `copies=False` (legacy --groups/--buffered, kept byte-stable): only this slot; the
        relation never reads the stale copy's prev_state_root."""
        if blocks[j]['slots'][k][1] != heights[j]:
            raise SystemExit("slot %d:%d is a missed slot (an old header): edit it where it is new" % (j, k))
        old = blocks[j]['slots'][k][0]
        for jj, x in enumerate(blocks[:j + 1]):
            for kk, (inner, hi) in enumerate(x['slots']):
                if inner == old and (copies or (jj, kk) == (j, k)):
                    if (jj, kk) not in rekey:
                        rekey[(jj, kk)] = chunk_hash(old)
                    x['slots'][kk] = [new_inner, hi]
                    changed.add(jj)

    for spec in a.dup:
        dst, src = spec.split("=")
        dj, dk = map(int, dst.split(":"))
        sj, si = map(int, src.split(":"))
        s_inner, s_h = blocks[sj]['slots'][si]
        d_inner, d_h = blocks[dj]['slots'][dk]
        if s_h != heights[sj] or d_h != heights[dj]:
            raise SystemExit("dup %s: both slots must be new in their blocks" % spec)
        if nrec.get(chunk_hash(s_inner), -1) != 0 or nrec.get(chunk_hash(d_inner), -1) != 0:
            raise SystemExit("dup %s: both slots need witness entries without receipts" % spec)
        if dj == b2i and dk == idx:
            raise SystemExit("dup %s: the own slot of B2 cannot be replaced" % spec)
        blocks[dj]['slots'][dk] = [s_inner, d_h]
        changed.add(dj)
        ops.append(dict(op="dup", dst=[dj, dk], src=[sj, si], key=chunk_hash(s_inner).hex(),
                        replaced_key=chunk_hash(d_inner).hex()))

    for spec in a.bw:
        dst, _, rhs = spec.partition("=")
        bj, bk = dst.split(":")
        bj = int(bj)
        # '*': every slot whose chunk is new in this block (missed slots repeat an older header)
        slots = ([k for k, (_, hi) in enumerate(blocks[bj]['slots']) if hi == heights[bj]]
                 if bk == "*" else [int(bk)])
        reqs = []
        for item in (rhs.split(",") if rhs else []):
            to, _, bits = item.partition("/")
            bm = bytes.fromhex(bits)
            if len(bm) != 5:
                raise SystemExit("--bw: bitmap must be 5 bytes")
            for t in (L.shard_ids if to == "*" else [int(to)]):
                reqs.append((t, bm))
        for k in slots:
            edit_slot(bj, k, set_bw(blocks[bj]['slots'][k][0], reqs))
        ops.append(dict(op="bw", block=bj, slots=list(slots), requests=[[t, bm.hex()] for t, bm in reqs]))

    if a.state:
        own_inner = blocks[b2i]['slots'][idx][0]
        pre_root = own_inner[33:65]
        store = {sha(v): v for v in w['main']['values']}
        try:
            new_root, new_entries, slog = trie_edit.apply_ops(store, pre_root, a.state)
        except trie_edit.EditError as e:
            raise SystemExit("--state: %s" % e)
        store.update(new_entries)
        keep = reachable(store, new_root)
        w['main']['values'] = restrict(w['main']['values'], store, keep)
        edit_slot(b2i, idx, own_inner[:33] + new_root + own_inner[65:])
        ops.append(dict(op="state", ops=a.state, log=slog, pre_state_root=new_root.hex()))

    if a.buffered or a.groups:
        own_inner = blocks[b2i]['slots'][idx][0]
        pre_root = own_inner[33:65]
        trie = PartialTrie(w['main']['values'], pre_root)
        gvals = {}
        bi_old = trie.get(bytes([13]))
        if a.buffered:
            if bi_old is not None:
                raise SystemExit("--buffered: base already has BufferedReceiptIndices")
            shards = []
            for item in a.buffered.split(","):
                s, _, v = item.partition("=")
                shards.append(int(s))
                if v != "absent":
                    gvals[int(s)] = bytes.fromhex(v)      # default "": the empty value
            shards.sort()
            trie.insert(bytes([13]), u32(len(shards)) + b''.join(u64(s) + u64(7) + u64(7) for s in shards))
        else:
            if bi_old is None:
                raise SystemExit("--groups: base has no BufferedReceiptIndices (use --buffered)")
            n = struct.unpack('<I', bi_old[:4])[0]
            shards = [struct.unpack('<Q', bi_old[4 + 24 * i:12 + 24 * i])[0] for i in range(n)]
        for item in (a.groups.split(",") if a.groups else []):
            s, _, v = item.partition("=")
            if int(s) not in shards:
                raise SystemExit("--groups: shard %s is not listed in BufferedReceiptIndices" % s)
            gvals[int(s)] = b'' if v == "empty" else bytes.fromhex(v)
        for s in sorted(gvals):
            trie.insert(bytes([16]) + u64(s), gvals[s])
        keep = reachable(trie.store, trie.root)
        w['main']['values'] = restrict(w['main']['values'], trie.store, keep)
        edit_slot(b2i, idx, own_inner[:33] + trie.root + own_inner[65:], copies=False)
        ops.append(dict(op="buffered" if a.buffered else "groups", shards=shards,
                        groups={str(s): ("absent" if s not in gvals else gvals[s].hex()) for s in shards},
                        empty_values=sum(1 for s in gvals if gvals[s] == b''),
                        pre_state_root=trie.root.hex()))

    if not ops:
        raise SystemExit("no operation")
    # slots edited in place keep their witness entry (source receipt proof): re-key it
    remap = {old: chunk_hash(blocks[j]['slots'][k][0]) for (j, k), old in rekey.items()}
    for e in w['entries']:
        if e['key'] in remap:
            e['key'] = remap[e['key']]
    for j in sorted(changed):
        fix_headers_root(blocks[j])
    for m in range(max(changed) - 1, -1, -1):
        blocks[m]['ph'] = bhash(blocks[m + 1])
    new_hashes = [bhash(x) for x in blocks]
    c['inner'] = c['inner'][:1] + new_hashes[0] + c['inner'][33:]
    w['inner'] = c['inner']
    # transition block hashes follow their blocks (not read by the relation; kept truthful)
    if w['main']['bh'] == old_hashes[b2i]:
        w['main']['bh'] = new_hashes[b2i]
    for T in w['implicit']:
        if T['bh'] in old_hashes:
            T['bh'] = new_hashes[old_hashes.index(T['bh'])]

    log = []
    cb, wb = fixpoint(c, w, new_hashes, log)
    expected, verdict, mutation = True, "ok", None
    if a.drop_extra:
        drop = {bytes.fromhex(o['replaced_key']) for o in ops if o['op'] == 'dup'}
        if not drop:
            raise SystemExit("--drop-extra needs a dup operation")
        w['entries'] = [e for e in w['entries'] if e['key'] not in drop]
        wb = enc_witness(w)
        verdict, _ = py_check(cb, wb)
        if verdict == "ok":
            raise SystemExit("--drop-extra: the Python checker still accepts")
        expected, mutation = False, "w.dup_noextra"
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "claim.bin"), "wb").write(cb)
    open(os.path.join(a.out, "witness.bin"), "wb").write(wb)
    # D0a verdict of the independent Python reference (amendments incl. A9's word count)
    runs = []
    orig_run = v3sched.run

    def counted(*args):
        before = set(map(id, d0a._RNGS))
        out = orig_run(*args)
        runs.append(sum(r.words for r in d0a._RNGS if id(r) not in before))
        return out
    v3sched.run = counted
    try:
        dv = d0a.check_case(a.out)
    finally:
        v3sched.run = orig_run
    if (dv[0] == "accept") != expected:
        raise SystemExit("python D0a verdict %s (%s), expected %s" % (dv[0], dv[1], expected))
    name = os.path.basename(os.path.normpath(a.out))
    meta = dict(case=name, base=os.path.relpath(os.path.abspath(a.base), REPO), kind="extra-d0a",
                generator="examples/np-udr-stark-v2/conformance/fixtures-extra/gen_extra_d0a.py",
                domain="D0a", expected_rel_d0=expected, expected_rel_d0a=expected,
                nearcore="not judged (constructed: the mutated blocks are not in nearcore's store)",
                ops=ops, python_fixups=log, python_verdict=verdict, python_d0a=dv[0],
                chacha_words=dv[3], chacha_words_runs=runs[:1 + len(w['implicit'])],
                note=a.note,
                claim_sha256=sha(cb).hex(), witness_sha256=sha(wb).hex())
    if mutation:
        meta["mutation"] = mutation
    json.dump(meta, open(os.path.join(a.out, "meta.json"), "w"), indent=1)
    print(json.dumps(dict(case=name, ops=len(ops), fixups=len(log), expected_rel_d0a=expected)))


if __name__ == "__main__":
    main()
