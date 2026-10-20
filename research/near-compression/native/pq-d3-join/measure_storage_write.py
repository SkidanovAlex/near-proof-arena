#!/usr/bin/env python3
"""Measure the state half of a `storage_write` on the smallest honest D3 fixture.

Lane pq-d3-join.  This is a *measurement* driver: it does not change the corpus and does not
implement a new AIR.  It uses the clean-room reference that already runs the D3 oracle
(`oracle/wasm-d3/cleanroom/` + `oracle/tools/spec_check_v3_d3.py`) to

1. verify the case (so the numbers are honest);
2. capture every `storage_write` the contract performs, with the pre-state trie root at the
   moment of the write (the state half sees the D3 `RealStore.root`, not the receipt's pre-root,
   because earlier writes of the same receipt land in the overlay and change what `upsV3` sees);
3. for each write: walk the `TrieKey::ContractData` path in the pre-state trie exactly as
   `D3Store._lookup` / `TTN.lookupFrom` do, and count the bytes `nodeV3` / `valV3` / `upsV3` /
   `sha_t` must render;
4. apply the write with `Trie2.update` (nearcore's insert/delete) and count the post nodes;
5. print a CSV row and a summary.

The mapping from bytes to cells uses the *measured* per-byte costs of the existing tables at the
D0a fixture (`pq-state-port` README §1 and the `statedump` heights): one `nodeV3` row per serialized
byte of a node record, one `valV3` row per value byte, one `sha_t` block per 64-byte chunk, and
`upsV3` rows = the serialized bytes of the new path records plus the value bytes.  It is a proxy,
not the AIR measurement: the AIR measurement needs the D3 render (see "Remaining checklist").

Usage:
  measure_storage_write.py CASE_DIR [CASE_DIR ...]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
TOOLS = os.path.join(REPO, "oracle", "tools")
sys.path.insert(0, TOOLS)
sys.path.insert(0, os.path.join(REPO, "oracle", "wasm-d3", "cleanroom"))

import spec_check_v3 as s3  # noqa: E402
import spec_check_v3_d2 as D2  # noqa: E402
import spec_check_v3_d3 as D3  # noqa: E402
from v3lib.prim import R, sha, nibbles  # noqa: E402
from v3lib.trie2 import Trie2  # noqa: E402

# Existing measured table constants (pq-state-port README §1 / D0a envelope).
SHA_T_WIDTH = 544
SHA_ROW_PER_BLOCK = 17          # 16 round rows + 1 digest row, `Render/rowsOf`
NODE_WIDTH = 188                # `UnfoldA7.nodeA7` width
VAL_WIDTH = 17                  # `Tables/Val.valV3` width
UPS_WIDTH = 202                 # `UnfoldA7.upsA7` width


def capture_writes(case):
    """Run the reference checker, recording each `storage_write` and its pre-root."""
    recs = []
    orig = D3.D3Store.write

    def wrapped(self, inst, k, v):
        recs.append((bytes(self.prefix), bytes(k), bytes(v), bytes(self.st.trie.root)))
        return orig(self, inst, k, v)

    D3.D3Store.write = wrapped
    try:
        D3.check_case_inner(open(os.path.join(case, "claim.bin"), "rb").read(),
                            open(os.path.join(case, "witness.bin"), "rb").read())
        verdict = "accept"
    except Exception as e:  # noqa: BLE001 - the measurement reports the verdict as data
        verdict = f"{type(e).__name__}: {e}"
    finally:
        D3.D3Store.write = orig
    return verdict, recs


def load_values(case):
    wb = open(os.path.join(case, "witness.bin"), "rb").read()
    r = R(wb)
    r.bytes()          # witness format tag
    sw = r.bytes()
    codes = r.vec(r.bytes)
    r.end()
    w = D2.decode_state_witness_d2(sw)
    return list(w["main"]["base_state"]) + list(codes)


def lookup_path(t, fk):
    """`D3Store._lookup`: the nodes (hash, decoded) on the path and the value ref."""
    if t.root == b"\0" * 32:
        return [], None
    nib, h, visited = nibbles(fk), t.root, []
    while True:
        n = t.node(h)
        visited.append((h, n))
        if n.kind == "leaf":
            return visited, (n.vref if n.key == nib else None)
        if n.kind == "ext":
            if nib[:len(n.key)] != n.key:
                return visited, None
            nib, h = nib[len(n.key):], n.child
            continue
        if not nib:
            return visited, n.vref
        if nib[0] not in n.children:
            return visited, None
        h, nib = n.children[nib[0]], nib[1:]


def sha_blocks(nbytes):
    return (nbytes + 9 + 63) // 64   # nearcore hashes `len(u32) ‖ data`; +1 block for padding


def measure(case):
    verdict, recs = capture_writes(case)
    values = load_values(case)
    rows = []
    for pfx, key, val, root in recs:
        fk = pfx + key
        pre = Trie2(values, root)
        visited, vr = lookup_path(pre, fk)
        ser_pre = sum(len(n.encode()) for _, n in visited)
        oldlen = 0 if vr is None else vr[0]
        # the post-state: apply exactly this write (nearcore insert) to a fresh copy
        post = Trie2(values, root)
        newroot = post.update([(fk, val)])
        # nodes the insert touched: recut the path in the post trie
        pv, pvr = lookup_path(post, fk)
        ser_post = sum(len(n.encode()) for _, n in pv)
        pre_hashes = {h for h, _ in visited}
        post_new = [(h, n) for h, n in pv if h not in pre_hashes]
        ser_new = sum(len(n.encode()) for _, n in post_new)
        # walk rows: START + one per key nibble + END (walkV3), all in the pre-state
        walk_rows = len(nibbles(fk)) + 2
        # `walkV3` has 6 interactions/row, `nodeV3` 23, `valV3` 9, `sha` 17, `upsV3` 19.
        rows.append(dict(
            key_bytes=len(fk), nibbles=len(nibbles(fk)),
            path_nodes=len(visited), pre_ser=ser_pre, old_len=oldlen, new_len=len(val),
            post_nodes=len(pv), new_nodes=len(post_new), new_ser=ser_new,
            walk_rows=walk_rows,
            node_rows=ser_pre + ser_new,
            sha_rows=(sha_blocks(ser_pre) + sha_blocks(ser_new) + sha_blocks(max(oldlen, len(val))))
                * SHA_ROW_PER_BLOCK,
            walk_inters=6 * walk_rows,
            node_inters=23 * (ser_pre + ser_new),
            val_inters=9 * oldlen,
            ups_inters=19 * (ser_new + len(val)),
            sha_inters=17 * (sha_blocks(ser_pre) + sha_blocks(ser_new)
                + sha_blocks(max(oldlen, len(val)))),
            # cells (proxy): one nodeV3 row per pre serialized byte + per post byte,
            # one valV3 row per pre value byte, sha_t per 64-byte block of every hashed record,
            # upsV3 per byte of the new records plus the new value.
            node_cells=(ser_pre + ser_new) * NODE_WIDTH,
            val_cells=oldlen * VAL_WIDTH,
            sha_cells=(sha_blocks(ser_pre) + sha_blocks(ser_new) + sha_blocks(max(oldlen, len(val))))
            * SHA_ROW_PER_BLOCK * SHA_T_WIDTH,
            ups_cells=(ser_new + len(val)) * UPS_WIDTH,
            newroot=newroot.hex(),
        ))
    return verdict, rows


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    print("case,key_bytes,nibbles,path_nodes,pre_ser,old_len,new_len,post_nodes,"
          "node_cells,val_cells,sha_cells,ups_cells,cell_estimate,walk_rows,node_rows,"
          "walk_inters,node_inters,val_inters,ups_inters,sha_inters,total_inters")
    total = {}
    for case in sys.argv[1:]:
        verdict, rows = measure(case)
        name = os.path.basename(os.path.normpath(case))
        if not rows:
            print(f"# {name}: verdict {verdict}; no storage_write", file=sys.stderr)
            continue
        for r in rows:
            est = r["node_cells"] + r["val_cells"] + r["sha_cells"] + r["ups_cells"]
            print(f"{name},{r['key_bytes']},{r['nibbles']},{r['path_nodes']},{r['pre_ser']},"
                  f"{r['old_len']},{r['new_len']},{r['post_nodes']},"
                  f"{r['node_cells']},{r['val_cells']},{r['sha_cells']},{r['ups_cells']},{est},"
                  f"{r['walk_rows']},{r['node_rows']},{r['walk_inters']},{r['node_inters']},"
                  f"{r['val_inters']},{r['ups_inters']},{r['sha_inters']},"
                  f"{r['walk_inters']+r['node_inters']+r['val_inters']+r['ups_inters']+r['sha_inters']}")
            r["total_inters"] = (r["walk_inters"] + r["node_inters"] + r["val_inters"]
                                 + r["ups_inters"] + r["sha_inters"])
            for k in ("node_cells", "val_cells", "sha_cells", "ups_cells", "total_inters"):
                total[k] = total.get(k, 0) + r[k]
    if total:
        print(f"# totals: {total}; all={sum(total.values())}", file=sys.stderr)


if __name__ == "__main__":
    main()
