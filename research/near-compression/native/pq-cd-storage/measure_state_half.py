#!/usr/bin/env python3
"""Render the *state half* of a `storage_write` for a real D3 fixture.

Lane `pq-cd-storage`.  Companion to `measure_storage_write.py` (lane `pq-d3-join`), which priced
the *bytes*.  This driver renders the tables the state AIR actually has to lay out, for the exact
ContractData key the write uses, and reports

* committed cells and interaction slots per table, at the tables' natural heights;
* the ContractData read rows (`cdWalkV3`), including the four bus messages each row emits;
* the write rows (`upsV3`), split into walk rows / value part / node parts;
* the `RealStore.writes` log entry the state side must reproduce, in order;
* the storage-usage delta (`Host.lean`'s rule).

The mapping from bytes to rows is the one the previous lane measured (`pq-d3-join` README §4.1):
one `nodeV3` row per serialized byte, one `valV3` row per value byte, `upsV3` rows = new path
record bytes + value bytes, `sha_t` = 17 rows per 64-byte block.  Widths are the Lean table
widths (`Tables/*.lean`), so the cell counts are the AIR's, not an estimate of a different table.

Usage:
  measure_state_half.py CASE_DIR [CASE_DIR ...]
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
TOOLS = os.path.join(REPO, "oracle", "tools")
sys.path.insert(0, TOOLS)
sys.path.insert(0, os.path.join(REPO, "oracle", "wasm-d3", "cleanroom"))

import spec_check_v3 as s3  # noqa: E402,F401
import spec_check_v3_d2 as D2  # noqa: E402
import spec_check_v3_d3 as D3  # noqa: E402
from v3lib.prim import R, nibbles  # noqa: E402
from v3lib.trie2 import Trie2  # noqa: E402

# Lean table widths and interaction counts (`zk-formal/ZkFormal/NearV3/Tables/*.lean`).
# `upsV3` is 200 wide with 19 interactions *per row* only if every interaction fires; the
# actual per-row multiplicity is what the render emits, so we count emitted messages instead.
TABLES = {
    # name: (width, interactions)
    "cdWalkV3": (56, 6),
    "nodeV3": (186, 21),
    "valV3": (15, 9),
    # `upsV3`'s interactions fire per row kind; the traffic is counted below from the render.
    "upsV3": (200, 19),
    "sha_t": (544, 17),
}
SHA_ROW_PER_BLOCK = 17
CELLS = {k: v[0] for k, v in TABLES.items()}

# The four `walkV3` modes (`Tables/Walk.lean`) and the messages of a `cdWalkV3` row.
MODE_STEP, MODE_ABS_KEY, MODE_ABS_BRANCH, MODE_DRAIN = 0, 1, 2, 3

CDKEYNIB, EDGE, BMAP, FINAL = 76, 10, 11, 12


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
    except Exception as e:  # noqa: BLE001 - the verdict is data for the measurement
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
    return (nbytes + 9 + 63) // 64


# The interactions of a `cdWalkV3` row, by mode, exactly as `Tables/Walk.lean` gates them:
#   CDKEYNIB recv  — every row except `START` (gated by `gK = act - ws`)
#   EDGE recv+send — step rows and absent-by-key rows
#   BMAP recv+send — absent-at-branch rows
#   FINAL send     — the last row only
INTER_CDKEYNIB = "CDKEYNIB"
INTER_EDGE = "EDGE"
INTER_BMAP = "BMAP"
INTER_FINAL = "FINAL"


def row_interactions(mode, t, last):
    """The `cdWalkV3` interactions that fire on one row."""
    out = []
    if t > 0:
        out.append(INTER_CDKEYNIB)
    if mode == MODE_STEP or mode == MODE_ABS_KEY:
        out.append(INTER_EDGE)
    if mode == MODE_ABS_BRANCH:
        out.append(INTER_BMAP)
    if last:
        out.append(INTER_FINAL)
    return out


def absent_mode(fk, path_nodes):
    """`ABS_BRANCH` or `ABS_KEY`, from the node where the pre-state path stops.

    `walkV3` gives `ABS_BRANCH` when the walk sits at a branch (`nI = 0`) whose bitmap has the
    next nibble clear, and `ABS_KEY` when the next edge is a `KEY`/`LEND` edge with a different
    symbol (a leaf or extension whose key diverges)."""
    if not path_nodes:
        return MODE_ABS_BRANCH
    _, n = path_nodes[-1]
    return MODE_ABS_BRANCH if n.kind == "branch" else MODE_ABS_KEY


def read_rows(fk, path_nodes, present):
    """The `cdWalkV3` rows of the read: `START`, one per key nibble, `END`.

    Modes are what `walkV3` decides from the pre-state: a nibble that leaves the path is
    `ABS_KEY`; a branch with a missing slot is `ABS_BRANCH`; the rest of the key after an absent
    terminal is `DRAIN`.  For a *present* path every key row is a `STEP` and the last key row is
    the `VAL` step.
    """
    nibs = nibbles(fk)
    # prefix nibbles the pre-state path covers
    covered = 0
    for _, n in path_nodes:
        if n.kind == "leaf":
            if present:
                covered = len(nibs)
        elif n.kind == "ext":
            covered += len(n.key)
        else:
            covered += 1

    def row(t, sym, mode, last):
        return dict(t=t, sym=sym, mode=mode, last=last,
                    inters=row_interactions(mode, t, last))

    amode = absent_mode(fk, path_nodes)
    rows = [row(0, "START", MODE_STEP, False)]
    absent_at = None
    for i, sym in enumerate(nibs):
        t = i + 1
        if present:
            rows.append(row(t, sym, MODE_STEP, False))
        elif absent_at is None and i >= covered:
            absent_at = i
            rows.append(row(t, sym, amode, False))
        elif absent_at is None:
            rows.append(row(t, sym, MODE_STEP, False))
        else:
            rows.append(row(t, sym, MODE_DRAIN, False))
    # the `END` row is the only `we` row: `mS` with `ek = EK_VAL` for a present key (this is the
    # final *step*), `mD` after an absent terminal
    rows.append(row(len(nibs) + 1, "END",
                    MODE_DRAIN if absent_at is not None else MODE_STEP, True))
    return rows


def measure(case):
    verdict, recs = capture_writes(case)
    values = load_values(case)
    out = []
    for pfx, key, val, root in recs:
        fk = pfx + key
        pre = Trie2(values, root)
        visited, vr = lookup_path(pre, fk)
        ser_pre = sum(len(n.encode()) for _, n in visited)
        oldlen = 0 if vr is None else vr[0]
        post = Trie2(values, root)
        newroot = post.update([(fk, val)])
        pv, _ = lookup_path(post, fk)
        pre_hashes = {h for h, _ in visited}
        post_new = [(h, n) for h, n in pv if h not in pre_hashes]
        ser_new = sum(len(n.encode()) for _, n in post_new)

        walk = read_rows(fk, visited, vr is not None)
        walk_rows = len(walk)
        # `upsV3`: 4 walk rows (START, 0, 15, END) even though the key is long — the key enters
        # via EDGE/BMAP, so the walked key is still `[0,15]`; then `L` value rows, then one part
        # per new path node (plus a `MEM` tail row per part: `qlen` = serialized bytes).
        ups_rows = 4 + max(oldlen, len(val)) + ser_new
        node_rows = ser_pre + ser_new
        val_rows = oldlen
        blocks = sha_blocks(ser_pre) + sha_blocks(ser_new) + sha_blocks(max(oldlen, len(val)))
        sha_rows = blocks * SHA_ROW_PER_BLOCK

        emitted = {}
        for r in walk:
            for i in r["inters"]:
                emitted[i] = emitted.get(i, 0) + 1

        cells = (walk_rows * CELLS["cdWalkV3"] + ups_rows * CELLS["upsV3"]
                 + node_rows * CELLS["nodeV3"] + val_rows * CELLS["valV3"]
                 + sha_rows * CELLS["sha_t"])
        intersects = (sum(emitted.values()) + ups_rows * TABLES["upsV3"][1]
                      + node_rows * TABLES["nodeV3"][1] + val_rows * TABLES["valV3"][1]
                      + sha_rows * TABLES["sha_t"][1])
        usage = ({"kind": "overwrite", "old": oldlen, "new": len(val),
                  "delta": len(val) - oldlen}
                 if vr is not None else
                 {"kind": "insert", "old": 0, "new": len(val),
                  "delta": len(val) + len(key) + 40})
        out.append(dict(
            case=os.path.basename(os.path.normpath(case)), verdict=verdict,
            account=pfx[1:-1].decode("utf-8", "replace"), key=key.decode("utf-8", "replace"),
            trie_key=fk.hex(), nibbles=len(nibbles(fk)), nibbles_hex=nibbles(fk),
            path_nodes=len(visited), pre_ser=ser_pre, old_len=oldlen, new_len=len(val),
            new_nodes=len(post_new), new_ser=ser_new,
            walk_rows=walk_rows, ups_rows=ups_rows, node_rows=node_rows, val_rows=val_rows,
            sha_rows=sha_rows, cells=cells, inters=intersects,
            emitted={str(k): v for k, v in sorted(emitted.items())},
            walk=walk,
            usage=usage, new_root=newroot.hex(),
        ))
    return out


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    rows = []
    for case in sys.argv[1:]:
        rows.extend(measure(case))
    print(json.dumps(rows, indent=1))
    if rows:
        tot = {k: sum(r[k] for r in rows) for k in
               ("walk_rows", "ups_rows", "node_rows", "val_rows", "sha_rows", "cells", "inters")}
        print(f"# totals: {tot}", file=sys.stderr)


if __name__ == "__main__":
    main()
