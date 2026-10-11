import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Extract.NodeView
import Lean.Data.Json

/-!
`np-lean-render-v3 <table> <entries.json> <out.bin>` — run the Lean aligned
generator of one `nearAirV3` table (`Render/Padded.lean`, `Render/PaddedTrie.lean`)
on a JSON list of its entries and dump the trace (format `np-render-v3-table`,
all integers u32 LE):

```
log, width, then 2^log · width cells row-major ((tr.cell 0 r c).toNat)
```

`<table>` ∈ `bnd akey head val uniq walk`.  Entries are JSON objects whose keys
are the Lean field names (`BndE`, `AkeyE`, `HeadE`, `ValE`, `UEnt`, `WalkR` with
`WStep3` steps).  Compared byte for byte with `npudr v3render` (../source).
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Render

deriving instance FromJson for BndE
deriving instance FromJson for AkeyE
deriving instance FromJson for HeadE
deriving instance FromJson for ValE
deriving instance FromJson for ZkFormal.NearV3.Render.UEnt
deriving instance FromJson for ZkFormal.NearV3.WStep3
deriving instance FromJson for ZkFormal.NearV3.WalkR
deriving instance FromJson for ZkFormal.Near.NKid
deriving instance FromJson for ZkFormal.NearV3.NSlot3
deriving instance FromJson for ZkFormal.NearV3.NodeV3
deriving instance FromJson for ZkFormal.NearV3.NodeS3

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

def parse (α : Type) [FromJson α] (s : String) : Except String (List α) := do
  let j ← Json.parse s
  fromJson? j

def render (table s : String) : Except String ByteArray :=
  match table with
  | "bnd" => return dump (bndTraceAligned (← parse BndE s)) BndV3.width
  | "akey" => return dump (akeyTraceAligned (← parse AkeyE s)) AkeyV3.width
  | "head" => return dump (headTraceAligned (← parse HeadE s)) HeadV3.width
  | "val" => return dump (valTraceAligned (← parse ValE s)) ValV3.width
  | "uniq" => return dump (uniqTraceAligned (← parse UEnt s)) Uniq.width
  | "walk" => return dump (walkTraceAligned (← parse WalkR s)) WalkV3.width
  | "node" => return dump (nodeTraceAligned (← parse NodeS3 s)) NodeV3.width
  | t => throw s!"unknown table {t}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [table, inp, out] =>
    match render table (← IO.FS.readFile inp) with
    | .ok b => IO.FS.writeBinFile out b; return 0
    | .error e => IO.eprintln s!"np-lean-render-v3: {e}"; return 2
  | _ => IO.eprintln "usage: np-lean-render-v3 <table> <entries.json> <out.bin>"; return 2
