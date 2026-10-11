#!/usr/bin/env python3
"""Measure the candidate amendment A11 (post-rebuild store independence) on D0a cases.

For every applied transition the D0 checker runs, the A7 post term (`unfold_diff`, Lean
`diffT` of `rebuildPost`) reads the post trie from the witness store extended with the
nodes and values the transition wrote.  A11 asks that this term is unchanged when the
witness part of that store is restricted to the blobs revealed by the pre trie along the
read keys (the reconstruction's normalized store, Lean `normalStore`).  Two families of
witness blobs can break it:

  shadow  a witness blob with the sha256 of a newly written blob but different bytes
          (a SHA-256 collision; impossible to construct, counted for completeness);
  extra   a witness blob outside the pre trie's revealed part that the post rebuild reads.

usage: a11_measure_v3_d0a.py CASE_DIR...   (one JSON line per case accepted by RelD0a)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d0a as a  # noqa: E402
from v3lib.prim import nibbles  # noqa: E402


def revealed(store, h, keys, out):
    """Blob hashes `unfold_pre` reads (nodes and values), mirroring its traversal."""
    if not keys or h is None or h not in store:
        return
    n = a._parse(store[h])
    if n is None:
        return
    out.add(h)
    if n.kind == 'leaf':
        if any(k == n.key for k in keys) and n.vref is not None and n.vref[1] in store:
            out.add(n.vref[1])
        return
    if n.kind == 'ext':
        revealed(store, n.child, [k[len(n.key):] for k in keys if k[:len(n.key)] == n.key], out)
        return
    if any(len(k) == 0 for k in keys) and n.vref is not None and n.vref[1] in store:
        out.add(n.vref[1])
    for i, c in n.children.items():
        revealed(store, c, [k[1:] for k in keys if k and k[0] == i], out)


def measure(t):
    keys = [nibbles(k) for k in t.keys]
    seen = set()
    revealed(t.pre_store, t.pre_root, keys, seen)
    written = {h: v for h, v in t.store.items() if t.pre_store.get(h) != v}
    shadows = sum(1 for h in written if h in t.pre_store)
    small = {h: t.pre_store[h] for h in seen}
    small.update(written)
    full = a.unfold_diff(t.pre_store, t.pre_root, t.store, t.root, keys)
    norm = a.unfold_diff(t.pre_store, t.pre_root, small, t.root, keys)
    return full, norm, shadows


def main():
    for d in sys.argv[1:]:
        a._TRIES.clear()
        a._RNGS.clear()
        verdict, reason, u, _, _, _ = a.check_case(d)
        if verdict != "accept":
            continue
        rows = [measure(t) for t in a._TRIES]
        diff = sum(1 for f, n, _ in rows if f != n)
        print(json.dumps(dict(case=d, transitions=len(rows), unfold=u, differ=diff,
                              shadows=sum(s for _, _, s in rows),
                              delta=sum(f - n for f, n, _ in rows))))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
