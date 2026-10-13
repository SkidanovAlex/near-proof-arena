import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Rcpt.Render.AcctRender
import ZkFormal.NearV3.Rcpt.Render.SizeRender
import ZkFormal.NearV3.Rcpt.Render.Srcp.Gen
import ZkFormal.NearV3.Qv.Candidates.CombinedTrace
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
import ZkFormal.NearV3.Extract.NodeView
import ZkFormal.Sha.Gen
import ZkFormal.Size.PadHeader
import Lean.Data.Json
import Conformance.FastTrie

/-!
`np-lean-render-v3 <table> <entries.json> <out.bin>` — run the Lean aligned
generator of one `nearAirV3` table (`Render/Padded.lean`, `Render/PaddedTrie.lean`)
on a JSON list of its entries and dump the trace (format `np-render-v3-table`,
all integers u32 LE):

```
log, width, then 2^log · width cells row-major ((tr.cell 0 r c).toNat)
```

`<table>` ∈ `bnd akey head val uniq walk node acct size srcp qv`.  Entries are JSON
objects whose keys are the Lean field names (`BndE`, `AkeyE`, `HeadE`, `ValE`,
`UEnt`, `WalkR` with `WStep3` steps, `SrcpB` with `SrcpItem` path items, and for
`qv` a `{ walks, records }` object mirroring `CombinedWalkGen.Walk` /
`ValueGen.Record`).  Compared byte for byte with `npudr v3render` (../source).
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Render

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
deriving instance FromJson for ZkFormal.Near.AcctV
deriving instance FromJson for ZkFormal.NearV3.SizeV
deriving instance FromJson for ZkFormal.NearV3.SrcpItem
deriving instance FromJson for ZkFormal.NearV3.SrcpB
deriving instance FromJson for ZkFormal.Sha.Gen.Msg

/-- The `qvV3` JSON input: the Lean `CombinedWalkGen.Walk` and `ValueGen.Record`
projections, re-assembled into `Walk`/`Record` (the Rust `qv::render` mirrors
`mixedRows`).  Byte fields are `List Nat` (each `< 256`), as for `AcctV`. -/
structure QvWalkIn where
  code : Nat
  shard : Nat := 0
  tau : Nat
  slot : Nat
  count : Nat
  value : Option (List Nat)
  vid : Nat
  users : Nat
  lastMain : Bool
  final : Bool
  deriving FromJson

structure QvBufIn where
  shard : List Nat
  index : List Nat
  deriving FromJson

structure QvRecIn where
  rkind : Nat
  vid : Nat
  tau : Nat
  users : Nat
  index : List Nat := []
  entries : List QvBufIn := []
  bytes : List Nat := []
  deriving FromJson

structure QvIn where
  walks : List QvWalkIn
  records : List QvRecIn
  deriving FromJson

def QvWalkIn.toWalk (k : QvWalkIn) : ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk :=
  let kind : ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Kind :=
    match k.code with
    | 0 => .delayed | 1 => .buffered | 2 => .yielded | _ => .group k.shard
  ⟨kind, k.tau, k.slot, k.count, k.value.map (fun bs => bs.map UInt8.ofNat),
    k.vid, k.users, k.lastMain, k.final⟩

def QvBufIn.toByteBuffer (e : QvBufIn) : ZkFormal.NearV3.Qv.ByteBuffer :=
  ⟨e.shard.map UInt8.ofNat, e.index.map UInt8.ofNat⟩

def QvRecIn.toRecord (v : QvRecIn) : ZkFormal.NearV3.Qv.Candidates.ValueGen.Record :=
  let payload : ZkFormal.NearV3.Qv.Candidates.ValueGen.Payload :=
    match v.rkind with
    | 0 => .empty (v.index.map UInt8.ofNat)
    | 1 => .buffer (v.entries.map QvBufIn.toByteBuffer)
    | _ => .raw (v.bytes.map UInt8.ofNat)
  ⟨v.vid, v.tau, v.users, payload⟩

/-- A `SizeV` entry plus the public witness overhead `ovh = ovhNat pub` (taken as
a JSON field for the differential). -/
structure SizeIn where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  ovh : Nat
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

def parse (α : Type) [FromJson α] (s : String) : Except String (List α) := do
  let j ← Json.parse s
  fromJson? j

def parse1 (α : Type) [FromJson α] (s : String) : Except String α := do
  let j ← Json.parse s
  fromJson? j

def render (table s : String) : Except String ByteArray :=
  match table with
  | "bnd" => return dump (bndTraceAligned (← parse BndE s)) BndV3.width
  | "akey" => return dump (akeyTraceAligned (← parse AkeyE s)) AkeyV3.width
  | "head" => return dump (headTraceAligned (← parse HeadE s)) HeadV3.width
  | "val" => return dump (valTraceAligned (← parse ValE s)) ValV3.width
  | "uniq" => return dump (uniqTraceAligned (← parse UEnt s)) Uniq.width
  -- `walkTraceFast = walkTraceAligned` (`Conformance.FastTrie.walkTraceFast_eq`)
  | "walk" => return dump (Conformance.FastTrie.walkTraceFast (← parse WalkR s)) WalkV3.width
  | "node" => return dump (nodeTraceAligned (← parse NodeS3 s)) NodeV3.width
  | "srcp" => do
    let bs ← parse ZkFormal.NearV3.SrcpB s
    let log := ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (SrcpGen.R bs))
    return dump (rowsTrace log (ZkFormal.Near.Render.mkTab (2 ^ log) SrcpV3.width (SrcpGen.cell bs))) SrcpV3.width
  | "qv" => do
    let q ← parse1 QvIn s
    let ws := q.walks.map QvWalkIn.toWalk
    let vs := q.records.map QvRecIn.toRecord
    let rows := ws.flatMap ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.rows
      ++ ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsRows vs
    let log := ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf rows.length)
    let tr : Trace Fp :=
      ⟨fun _ => log, fun _ r c => Fp.ofNat ((rows.getD r []).getD c 0)⟩
    return dump tr ZkFormal.NearV3.Qv.Candidates.CombinedTable.width
  | "acct" => do
    let as ← parse ZkFormal.Near.AcctV s
    let log := ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (16 * as.length))
    return dump (rowsTrace log (acctV3Rows as)) ZkFormal.NearV3.AcctV3.width
  | "sha_t" | "sha_r" => do
    let ms ← parse ZkFormal.Sha.Gen.Msg s
    let log := ZkFormal.Sha.Gen.honestLog ms
    let w := ZkFormal.Sha.Layout.width
    let tr : Trace Fp :=
      ⟨fun _ => log, fun _ r c => Fp.ofNat (ZkFormal.Sha.Gen.honestCell ms r c)⟩
    return dump tr w
  | "size" => do
    let Is ← parse SizeIn s
    let I ← match Is with
      | [i] => pure i
      | _ => throw "size: expected exactly one entry"
    let v : ZkFormal.NearV3.SizeV := ⟨I.x0, I.x1, I.x2⟩
    let pub := List.replicate ZkFormal.NearV3.SizeV3.PH_WOVH (0 : ZkFormal.Algebra.Fp) ++
      [ZkFormal.Algebra.Fp.ofNat (I.ovh % 256),
       ZkFormal.Algebra.Fp.ofNat (I.ovh / 256 % 256),
       ZkFormal.Algebra.Fp.ofNat (I.ovh / 65536 % 256),
       ZkFormal.Algebra.Fp.ofNat (I.ovh / 16777216 % 256)]
    return dump (rowsTrace 2 (sizeRows pub v)) ZkFormal.NearV3.SizeV3.width
  | t => throw s!"unknown table {t}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [table, inp, out] =>
    match render table (← IO.FS.readFile inp) with
    | .ok b => IO.FS.writeBinFile out b; return 0
    | .error e => IO.eprintln s!"np-lean-render-v3: {e}"; return 2
  | _ => IO.eprintln "usage: np-lean-render-v3 <table> <entries.json> <out.bin>"; return 2
