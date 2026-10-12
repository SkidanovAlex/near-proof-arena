import ZkFormal.NearV3.Render.UnfoldA7Aligned
import Lean.Data.Json

/-!
`np-lean-render-v3-a7 <table> <entries.json> <out.bin>` — run the Lean honest render of one
of the four A7 tables of `nearAirV3` (`Tables/UnfoldA7.lean`; indices 2, 4, 7, 21) on a JSON
entry list and dump the trace (format `np-render-v3-table`, all integers u32 LE:
`log, width`, then `2^log · width` cells row-major, `(tr.cell 0 r c).toNat`).

The renders are the definitions of `Render/UnfoldA7Aligned.lean`, called directly:

* `node`: `nodeA7Trace vs 0 (selN vs S)` (width 188);
* `val`:  `valA7Trace es 0 (selV es S)` (width 17);
* `ups`:  `upsA7Trace insts 0` (width 202);
* `size`: `sizeA7Trace pub v 0 (yA7 y0 y1 y2)` (width 57).

Inputs (compared byte for byte with `npudr v3render`, ../source):

* `node` / `val`: a JSON list of `NodeS3` / `ValE` objects (Lean field names), each with an
  optional `"rpl": bool` (absent or `null` → `false`): the replaced-record predicate
  `S n = es[n].rpl` on record indices.
* `ups`: a JSON list of `UpsInst` (with `UpsPartI` parts and `WStep3` walk steps).
* `size`: a one-element list `[{x0, x1, x2, ovh, yN?}]`: the `SizeV` totals, the public witness
  overhead `ovh` (`ovhNat pub`, placed at `PH_WOVH`) and the optional received A7 totals
  `yN = [y0, y1, y2]` (absent → zeros; entries past the third ignored, as `yA7`).

`selN`, `selV` (`Assembly/TrieA7Node.lean`, `Assembly/TrieA7Val.lean`) and `yA7`
(`Assembly/TrieSide.lean`) are restated here verbatim (`selN'`, `selV'`, `yA7'`) to avoid
importing the assembly; the record list is computed once and the row choice tabulated over the
record rows `q < R` (`selNTab`, `selVTab`); `tab.getD q false` is `selN vs S q` for every `q`
(both are `false` for `q ≥ R`).
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Render
  ZkFormal.NearV3.UnfoldA7

deriving instance FromJson for ValE
deriving instance FromJson for ZkFormal.NearV3.WStep3
deriving instance FromJson for ZkFormal.Near.NKid
deriving instance FromJson for ZkFormal.NearV3.NSlot3
deriving instance FromJson for ZkFormal.NearV3.NodeV3
deriving instance FromJson for ZkFormal.NearV3.NodeS3
deriving instance FromJson for ZkFormal.NearV3.Render.UpsPartI
deriving instance FromJson for ZkFormal.NearV3.Render.UpsInst

/-- `Assembly.TrieA7.selN` (verbatim). -/
def selN' (vs : List NodeS3) (S : Nat → Bool) (q : Nat) : Bool :=
  decide (q < NodeGen3.R vs) && S ((NodeGen3.recsOf vs).getD q default).n

/-- `Assembly.TrieA7.selV` (verbatim). -/
def selV' (es : List ValE) (S : Nat → Bool) (q : Nat) : Bool :=
  decide (q < ValGen.R es) && S ((ValGen.recs es).getD q default).1

/-- `Assembly.TrieSide.yA7` (verbatim). -/
def yA7' (a b c : Nat) : Nat → Nat :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0

/-- `selN' vs S` tabulated over the record rows `q < R vs`, the record list computed once. -/
def selNTab (vs : List NodeS3) (S : Nat → Bool) : Array Bool :=
  let R := NodeGen3.R vs
  let rs := (NodeGen3.recsOf vs).toArray
  (Array.range R).map fun q => decide (q < R) && S (rs.getD q default).n

/-- `selV' es S` tabulated over the record rows `q < R es`, the record list computed once. -/
def selVTab (es : List ValE) (S : Nat → Bool) : Array Bool :=
  let R := ValGen.R es
  let rs := (ValGen.recs es).toArray
  (Array.range R).map fun q => decide (q < R) && S (rs.getD q default).1

structure SizeIn where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  deriving FromJson

def u32 (b : ByteArray) (x : Nat) : ByteArray :=
  b.push (x % 256).toUInt8 |>.push (x / 256 % 256).toUInt8
    |>.push (x / 65536 % 256).toUInt8 |>.push (x / 16777216 % 256).toUInt8

def dump (tr : Trace Fp) (width : Nat) : ByteArray := Id.run do
  let log := tr.log 0
  let mut b := u32 (u32 ByteArray.empty log) width
  for r in [0:2 ^ log] do
    for c in [0:width] do
      b := u32 b (tr.cell 0 r c).toNat
  return b

/-- The entries of a JSON list and their optional `"rpl"` flags. -/
def parseRpl (α : Type) [FromJson α] (s : String) : Except String (List α × Array Bool) := do
  let j ← Json.parse s
  let arr ← j.getArr?
  let es : List α ← fromJson? j
  let fl ← arr.mapM fun x =>
    match x.getObjVal? "rpl" with
    | .error _ => pure false
    | .ok Json.null => pure false
    | .ok (Json.bool b) => pure b
    | .ok o => throw s!"\"rpl\" must be a boolean, got {o.compress}"
  return (es, fl)

/-- The optional `yN` list of the size entry (absent / `null` → `[]`). -/
def parseYN (j : Json) : Except String (List Nat) :=
  match j.getObjVal? "yN" with
  | .error _ => pure []
  | .ok Json.null => pure []
  | .ok y => fromJson? y

def render (table s : String) : Except String ByteArray :=
  match table with
  | "node" => do
    let (vs, fl) ← parseRpl NodeS3 s
    let S : Nat → Bool := fun n => fl.getD n false
    let tab := selNTab vs S
    return dump (nodeA7Trace vs 0 (fun q => tab.getD q false)) UnfoldA7.Node.width
  | "val" => do
    let (es, fl) ← parseRpl ValE s
    let S : Nat → Bool := fun n => fl.getD n false
    let tab := selVTab es S
    return dump (valA7Trace es 0 (fun q => tab.getD q false)) UnfoldA7.Val.width
  | "ups" => do
    let j ← Json.parse s
    let insts : List UpsInst ← fromJson? j
    return dump (upsA7Trace insts 0) UnfoldA7.Ups.width
  | "size" => do
    let j ← Json.parse s
    let arr ← j.getArr?
    let (e, I) ← match arr.toList with
      | [e] => do let I : SizeIn ← fromJson? e; pure (e, I)
      | _ => throw "size: expected exactly one entry"
    let y ← parseYN e
    let ovh : Nat := ((e.getObjValAs? Nat "ovh").toOption).getD 0
    let v : ZkFormal.NearV3.SizeV := ⟨I.x0, I.x1, I.x2⟩
    let pub := List.replicate ZkFormal.NearV3.SizeV3.PH_WOVH (0 : Fp) ++
      [Fp.ofNat (ovh % 256), Fp.ofNat (ovh / 256 % 256),
       Fp.ofNat (ovh / 65536 % 256), Fp.ofNat (ovh / 16777216 % 256)]
    return dump (sizeA7Trace pub v 0 (yA7' (y.getD 0 0) (y.getD 1 0) (y.getD 2 0))) UnfoldA7.Size.width
  | t => throw s!"unknown table {t} (node val ups size)"

def main (args : List String) : IO UInt32 := do
  match args with
  | [table, inp, out] =>
    match render table (← IO.FS.readFile inp) with
    | .ok b => IO.FS.writeBinFile out b; return 0
    | .error e => IO.eprintln s!"np-lean-render-v3-a7: {e}"; return 2
  | _ => IO.eprintln "usage: np-lean-render-v3-a7 <node|val|ups|size> <entries.json> <out.bin>"; return 2
