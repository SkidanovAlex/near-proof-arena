"""A7 native post term: Lean vs Python on synthetic insert-split vectors.

usage: python3 split_vectors.py OUT.lean   (prints Python: name pre native rebuilt), then
       cd zk-formal && lake env lean OUT.lean   (prints Lean: name pre native rebuilt)
"""
import os, sys, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../oracle/tools"))
import spec_check_v3_d0a as a
from v3lib.prim import PartialTrie, ZERO32, nibbles
cases = {
  "leaf_split_unread": ([b'\x00ab'], [b'\x0f']),
  "leaf_split_read":   ([b'\x00ab'], [b'\x0f', b'\x00ab']),
  "ext_split_unread":  ([b'\x00ab', b'\x00ac'], [b'\x0f']),
  "ext_split_read":    ([b'\x00ab', b'\x00ac'], [b'\x0f', b'\x00ac']),
  "ext_moved_child":   ([b'\x10', b'\x11'], [b'\x0f']),
  "branch_newleaf":    ([b'\x00ab', b'\x10'], [b'\x0f', b'\x10']),
  "overwrite":         ([b'\x00ab', b'\x0f'], [b'\x0f']),
}
lean = []
for name, (accts, keys) in cases.items():
    t = PartialTrie([], ZERO32)
    vals = []
    for i, k in enumerate(accts):
        v = bytes([0x30 + i]) * (10 + i)
        t.insert(k, v); vals.append(v)
    store = list(t.store.values())
    root = t.root
    newv = b'\x00' * 7 + b'\x05'
    r = a.RecTrie(store, root)
    for k in keys: r.get(k)
    r.insert(b'\x0f', newv)
    kn = [nibbles(k) for k in r.keys]
    pre = a.unfold_pre(r.pre_store, r.pre_root, kn)
    nat = a.unfold_native(r, r.root, (), kn)
    reb = a.unfold_pre(r.store, r.root, kn)
    print(name, pre, nat, reb)
    L = lambda b: "[" + ",".join(str(x) for x in b) + "]"
    lean.append(f'#eval tst "{name}" ({L(root)}).map UInt8.ofNat [{",".join("("+L(v)+").map UInt8.ofNat" for v in store)}] [{",".join(L(k)+".map UInt8.ofNat" for k in keys)}]')
open(sys.argv[1], "w").write("""import NearSpecV3.ChunkValidationV0a
open NearSpec NearSpecV3
def tst (name : String) (root : Bytes) (vals : List Bytes) (keys : List Bytes) : String :=
  let ks := keys.map nibbles
  let t := partialTrie vals root ks
  let nv : Bytes := (List.replicate 7 (0 : UInt8)) ++ [5]
  match t.upsert (nibbles [15]) nv with
  | some t' => s!"{name} {unfoldedBytesT t} {unfoldedBytesT t'} {unfoldedBytesT (rebuildPost vals t' ks)} root_ok={t'.hashOf.length}"
  | none => s!"{name} upsert failed"
""" + "\n".join(l.replace(' ([', ' (([').replace(']).map UInt8.ofNat [', ']).map UInt8.ofNat) [', 1) for l in lean) + "\n")
