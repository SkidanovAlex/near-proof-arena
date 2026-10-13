import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Render.CodecNative
import ZkFormal.NearV3.Render.ChachaLane
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.MemConcatCells
import ZkFormal.NearV3.Candidates.ProcScanDistPhases
import ZkFormal.NearV3.Candidates.ProcConcatGeometry
import Lean.Data.Json

/-! Shared JSON mirrors and executable twins for the scheduler tables, used by
both `RenderV3Sched` (the seeded sampler / renderers) and `SchedEntriesV3` (the
real-witness entry dumper). -/
open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3 ZkFormal.NearV3.Render
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Candidates

namespace NpSched

/-! ## JSON mirrors (the Lean field names; the Rust `sched` structs) -/

structure CReqJ where
  cid : Nat
  s : Nat
  r : Nat
  link : Nat
  bm : List Nat
  bits : List Nat
  incs : List Nat
  key : Nat
  deriving FromJson, ToJson

structure EntryJ where
  x : Nat
  ts : Nat
  ein : Nat
  eout : Nat
  inc : Nat
  rem : Nat
  s : Nat
  r : Nat
  link : Nat
  sbIn : Nat
  sbOut : Nat
  rbIn : Nat
  rbOut : Nat
  alIn : Nat
  alOut : Nat
  cS : Bool
  cR : Bool
  cL : Bool
  ok : Bool
  push : Bool
  zn : Nat
  deriving FromJson, ToJson

structure RoundJ where
  K : Nat
  z : Nat
  T : Nat
  Lr : Nat
  kst : Nat
  kend : Nat
  Kq : Nat
  zq : Nat
  entries : List EntryJ
  deriving FromJson, ToJson

structure MOpJ where
  t : Nat
  op : Nat
  vin : Nat
  v : Nat
  wp : Nat
  w : Nat
  inc : Nat
  ok : Bool
  c : Bool
  sf : Bool
  deriving FromJson, ToJson

structure SegJ where
  addr : Nat
  isL : Bool
  al : Bool
  vin0 : Nat
  v0 : Nat
  w0 : Nat
  ops : List MOpJ
  deriving FromJson, ToJson

structure RngJ where
  key : List Nat
  ctr : Nat
  buf : List Nat
  deriving FromJson, ToJson

structure PStateJ where
  sb : List Nat
  rb : List Nat
  al : List Nat
  g : List Nat
  rng : RngJ
  deriving FromJson, ToJson

structure RunJ where
  tau : Nat
  n : Nat
  base : Nat
  D : Nat
  seed : List Nat
  key : List Nat
  a2 : List Nat
  conv : List CReqJ
  used : List (List Bool)
  rounds : List RoundJ
  segs : List SegJ
  cmps : List (List Nat)
  kfin : Nat
  fin : PStateJ
  deriving FromJson, ToJson

structure ParamsJ where
  base : Nat
  maxShardBandwidth : Nat
  maxSingleGrant : Nat
  maxReceiptSize : Nat
  maxAllowance : Nat
  deriving FromJson, ToJson

structure SchedInJ where
  run : RunJ
  ids : List Nat
  allowed : List Bool
  params : ParamsJ
  present : Bool
  vid : Nat
  gb : List Nat
  fwd : List (List Nat)
  ash : List Nat
  a0 : List Nat
  prev_hash : List Nat
  deriving FromJson, ToJson

/-! ## Conversions -/

def EntryJ.toE (e : EntryJ) : Gen.Entry :=
  { x := e.x, ts := e.ts, ein := e.ein, eout := e.eout, inc := e.inc, rem := e.rem, s := e.s, r := e.r,
    link := e.link, sbIn := e.sbIn, sbOut := e.sbOut, rbIn := e.rbIn, rbOut := e.rbOut, alIn := e.alIn,
    alOut := e.alOut, cS := e.cS, cR := e.cR, cL := e.cL, ok := e.ok, push := e.push, zn := e.zn }

def EntryJ.ofE (e : Gen.Entry) : EntryJ :=
  { x := e.x, ts := e.ts, ein := e.ein, eout := e.eout, inc := e.inc, rem := e.rem, s := e.s, r := e.r,
    link := e.link, sbIn := e.sbIn, sbOut := e.sbOut, rbIn := e.rbIn, rbOut := e.rbOut, alIn := e.alIn,
    alOut := e.alOut, cS := e.cS, cR := e.cR, cL := e.cL, ok := e.ok, push := e.push, zn := e.zn }

def MOpJ.toM (o : MOpJ) : Gen.MOp :=
  { t := o.t, op := o.op, vin := o.vin, v := o.v, wp := o.wp, w := o.w, inc := o.inc, ok := o.ok,
    c := o.c, sf := o.sf }

def MOpJ.ofM (o : Gen.MOp) : MOpJ :=
  { t := o.t, op := o.op, vin := o.vin, v := o.v, wp := o.wp, w := o.w, inc := o.inc, ok := o.ok,
    c := o.c, sf := o.sf }

def tri (l : List Nat) : Nat × Nat × Nat := (l.getD 0 0, l.getD 1 0, l.getD 2 0)

def RunJ.toRun (r : RunJ) : Gen.Run :=
  { tau := r.tau, n := r.n, base := r.base, D := r.D, seed := r.seed.map UInt8.ofNat, key := r.key,
    a2 := r.a2.toArray,
    conv := r.conv.map fun c =>
      { cid := c.cid, s := c.s, r := c.r, link := c.link, bm := c.bm.map UInt8.ofNat, bits := c.bits,
        incs := c.incs, key := c.key },
    used := (r.used.map List.toArray).toArray,
    rounds := r.rounds.map fun rd =>
      { K := rd.K, z := rd.z, T := rd.T, Lr := rd.Lr, kst := rd.kst, kend := rd.kend, Kq := rd.Kq,
        zq := rd.zq, entries := rd.entries.map EntryJ.toE },
    segs := r.segs.map fun g =>
      { addr := g.addr, isL := g.isL, al := g.al, vin0 := g.vin0, v0 := g.v0, w0 := g.w0,
        ops := g.ops.map MOpJ.toM },
    cmps := r.cmps.map tri, kfin := r.kfin,
    fin := ⟨r.fin.sb.toArray, r.fin.rb.toArray, r.fin.al.toArray, r.fin.g.toArray,
      ⟨r.fin.rng.key, r.fin.rng.ctr, r.fin.rng.buf⟩⟩ }

def RunJ.ofRun (r : Gen.Run) : RunJ :=
  { tau := r.tau, n := r.n, base := r.base, D := r.D, seed := r.seed.map (·.toNat), key := r.key,
    a2 := r.a2.toList,
    conv := r.conv.map fun c =>
      { cid := c.cid, s := c.s, r := c.r, link := c.link, bm := c.bm.map (·.toNat), bits := c.bits,
        incs := c.incs, key := c.key },
    used := r.used.toList.map Array.toList,
    rounds := r.rounds.map fun rd =>
      { K := rd.K, z := rd.z, T := rd.T, Lr := rd.Lr, kst := rd.kst, kend := rd.kend, Kq := rd.Kq,
        zq := rd.zq, entries := rd.entries.map EntryJ.ofE },
    segs := r.segs.map fun g =>
      { addr := g.addr, isL := g.isL, al := g.al, vin0 := g.vin0, v0 := g.v0, w0 := g.w0,
        ops := g.ops.map MOpJ.ofM },
    cmps := r.cmps.map fun (x, y, b) => [x, y, b], kfin := r.kfin,
    fin := ⟨r.fin.sb.toList, r.fin.rb.toList, r.fin.al.toList, r.fin.g.toList,
      ⟨r.fin.rng.key, r.fin.rng.ctr, r.fin.rng.buf⟩⟩ }

def ParamsJ.toP (p : ParamsJ) : NearSpecV3.Scheduler.Params :=
  ⟨p.base, p.maxShardBandwidth, p.maxSingleGrant, p.maxReceiptSize, p.maxAllowance⟩

def ParamsJ.ofP (p : NearSpecV3.Scheduler.Params) : ParamsJ :=
  ⟨p.base, p.maxShardBandwidth, p.maxSingleGrant, p.maxReceiptSize, p.maxAllowance⟩

namespace SchedInJ
variable (b : SchedInJ)

/-- The prior state: absent (`State.initial`), or the canonical one (record `l` = link `l`,
allowance `a0[l]`, the sanity hash `prev_hash`). -/
def prev : NearSpec.Bandwidth.State :=
  if b.present then
    let n := b.ids.length
    ⟨(List.range b.a0.length).map (fun l => ⟨b.ids.getD (l / n) 0, b.ids.getD (l % n) 0, b.a0.getD l 0⟩),
     b.prev_hash.map UInt8.ofNat⟩
  else NearSpec.Bandwidth.State.initial

/-- `ProcPreparedSequence.input b.pub b.old` (raw requests are not read by tables 11–15). -/
def input : Gen.Input :=
  ⟨b.ids, b.params.toP, b.allowed.toArray, [], b.run.seed.map UInt8.ofNat, b.ash.map UInt8.ofNat, b.prev⟩

def R : Gen.Run := b.run.toRun

/-- `ProcNativeOldComparisonCapacity.distribution`. -/
def dist : Gen.DistOut :=
  match Gen.distRows b.input b.R with
  | .ok d => d
  | .error _ => ⟨#[], #[], []⟩

/-- The block's grants (`b.grants`): `gb` when given for every link, else the grid's. -/
def grants : Array Nat :=
  if b.gb.length = b.R.n * b.R.n then b.gb.toArray
  else if b.dist.gb.size = b.R.n * b.R.n then b.dist.gb else Array.replicate (b.R.n * b.R.n) 0

def fwdL : List (Nat × Nat) := b.fwd.map fun l => (l.getD 0 0, l.getD 1 0)

/-- `blkOf b` (`Render/CodecNative.lean`) on the block data; `recs` is tabulated once (the
same function on `kk < N`). -/
def blk : Cdc.Blk :=
  let I := b.input
  let R := b.R
  let N := R.n * R.n
  let a0 := a0Canon R.n I.prev
  let srcs : Array (Option Nat) := (List.range N).toArray.map (srcOf I.ids)
  let recOf (kk : Nat) : Cdc.Rec :=
    { kk := kk, srcS := (srcOf I.ids kk).getD 0, hasC := (srcOf I.ids kk).isSome,
      useC := srcs.any fun x => x == some kk,
      al := I.allowed[kk]!,
      a0s := match srcOf I.ids kk with
        | some k' => if b.present then a0[k']! else 0
        | none => 0,
      gb := b.grants[kk]!, afin := (R.segs.getD kk default).vfin,
      gfin := (R.segs.getD kk default).wfin,
      ft := if R.tau = 0 then Cdc.demand b.fwdL kk else 0,
      iklv := Cdc.inv (Gen.fsub kk (N - 1)) }
  let recsA := (List.range N).toArray.map recOf
  let hpre : List Nat := if b.present then I.prev.sanityHash.map (·.toNat) else List.replicate 32 0
  { I := ⟨R.tau, R.n, N, b.present, b.vid, I.p.base, I.p.maxShardBandwidth / R.n⟩
    ids := I.ids
    a0 := fun kk => a0[kk]!
    recs := fun kk => recsA.getD kk (recOf kk)
    dig := (NearSpec.sha256 ((hpre ++ I.ash.map (·.toNat)).map UInt8.ofNat)).map (·.toNat)
    hpre := hpre
    ash := I.ash.map (·.toNat) }

/-- `b.output.cmps` (`ProcPriorCodecGen.codecRows`, the block's codec output). -/
def codecCmps : List (Nat × Nat × Nat) :=
  match ProcPriorCodecGen.codecRows b.input b.R b.present b.vid b.grants b.fwdL with
  | .ok o => o.cmps
  | .error _ => []

end SchedInJ

/-! ## Streaming dump -/

def u32 (b : ByteArray) (x : Nat) : ByteArray :=
  b.push (x % 256).toUInt8 |>.push (x / 256 % 256).toUInt8
    |>.push (x / 65536 % 256).toUInt8 |>.push (x / 16777216 % 256).toUInt8

/-- Write `log, width`, then rows `0 … min(2^log, maxRows) − 1` of `Fp.ofNat (cell r c)`. -/
def emit (h : IO.FS.Stream) (log width maxRows : Nat) (cell : Nat → Nat → Nat) : IO Unit := do
  h.write (u32 (u32 ByteArray.empty log) width)
  let H := Nat.min (2 ^ log) maxRows
  let mut buf : ByteArray := ByteArray.emptyWithCapacity (1 <<< 21)
  for r in [0:H] do
    for c in [0:width] do
      buf := u32 buf (Fp.ofNat (cell r c)).toNat
    if buf.size ≥ (1 <<< 21) then
      h.write buf
      buf := ByteArray.emptyWithCapacity (1 <<< 21)
  h.write buf

/-- A table to dump: `log`, `width`, the cell function. -/
structure Dump where
  log : Nat
  width : Nat
  cell : Nat → Nat → Nat

def parseList (α : Type) [FromJson α] (s : String) : Except String (List α) := do
  let j ← Json.parse s
  match j with
  | .arr _ => fromJson? j
  | _ => return [← fromJson? j]

/-! ## The renders -/

deriving instance FromJson, ToJson for ZkFormal.Sha.Gen.Msg
deriving instance FromJson, ToJson for ZkFormal.Chacha.Gen.Req
deriving instance FromJson, ToJson for ZkFormal.Chacha.Rng.Gen.Call
deriving instance FromJson, ToJson for ZkFormal.Chacha.Shuffle.Gen.SInst

def shaDump (ms : List ZkFormal.Sha.Gen.Msg) : Dump :=
  let rows := (ZkFormal.Sha.Gen.honestRows ms).toArray
  ⟨ZkFormal.Size.padLog22 (logOf rows.size), ZkFormal.Sha.Layout.width,
   fun r c => ZkFormal.Sha.Gen.rowCell (rows.getD r .pad) c⟩

def chachaDump (reqs : List ZkFormal.Chacha.Gen.Req) : Dump :=
  let rows := (ZkFormal.Chacha.Gen.honestRows reqs).toArray
  ⟨ZkFormal.Size.padLog22 (logOf (86 * reqs.length)), ZkFormal.Chacha.Table.width,
   fun r c => ZkFormal.Chacha.Gen.rowCell (rows.getD r .pad) c⟩

def rngDump (calls : List ZkFormal.Chacha.Rng.Gen.Call) : Dump :=
  let rows := (ZkFormal.Chacha.Rng.Gen.honestRows calls).toArray
  let log := ZkFormal.Size.padLog22 (logOf rows.size)
  let base (r c : Nat) : Nat := ZkFormal.Chacha.Rng.Gen.rowCell (rows.getD r .pad) c
  -- `activeUpTo tr 9 r`: rows `r' ≤ r` with `cv tr 9 r' colA = 1` (`cv` = the cell's `toNat`)
  let act : Array Nat := Id.run do
    let mut a : Array Nat := Array.emptyWithCapacity (2 ^ log)
    let mut k := 0
    for r in [0:2 ^ log] do
      if (Fp.ofNat (base r ZkFormal.Chacha.Rng.Table.colA)).toNat = 1 then k := k + 1
      a := a.push k
    return a
  let total := act.getD (2 ^ log - 1) 0
  ⟨log, ZkFormal.Chacha.Rng.Table.widthW0, fun r c =>
    if c < 137 then base r c
    else if c = ZkFormal.Chacha.Rng.Table.colW then act.getD r 0
    else ZkFormal.Chacha.bt (ZkFormal.Chacha.Rng.Table.W0 - total) (c - 138)⟩

def shufDump (insts : List ZkFormal.Chacha.Shuffle.Gen.SInst) : Dump :=
  let rows := (ZkFormal.Chacha.Shuffle.Gen.honestRows insts).toArray
  ⟨ZkFormal.Size.padLog22 (logOf rows.size), ZkFormal.Chacha.Shuffle.Table.width,
   fun r c => ZkFormal.Chacha.Shuffle.Gen.rowCell (rows.getD r .pad) r c⟩

def codecDump (bs : List SchedInJ) : Dump :=
  let rows := ((Cdc.allDescs (bs.map SchedInJ.blk)).map Cdc.Desc.row).toArray
  ⟨22, Codec.width, fun r c => Complete.natCell rows Gen.codecPad r c⟩

def ssdDump (bs : List SchedInJ) : Dump :=
  let rows := (bs.flatMap (fun b => (Gen.Scan.rows b.R).toList) ++
    bs.flatMap (fun b => b.dist.rows.toList)).toArray
  ⟨22, ScanDist.width, fun r c => Complete.natCell rows Gen.distPad r c⟩

def procDump (bs : List SchedInJ) : Dump :=
  let rs := bs.map SchedInJ.R
  let rows := (ProcConcatGeometry.rows rs).toArray
  let tail := ProcConcatGeometry.tail rs
  ⟨22, Proc.width, fun r c =>
    (if h : r < rows.size then rows[r] else if r = rows.size then tail else Complete.padPV).cell c⟩

def memDump (bs : List SchedInJ) : Dump :=
  let rows := MemConcatCells.rows (bs.map SchedInJ.R)
  ⟨22, Mem.width, fun r c => Complete.natCell rows Complete.memPad r c⟩

/-- `ProcNativeOldComparisonCapacity.requests bs`. -/
def requests (bs : List SchedInJ) : List (Nat × Nat × Nat) :=
  bs.flatMap fun b => b.R.cmps ++ b.codecCmps ++ b.dist.cmps

def cmpDump (bs : List SchedInJ) : Dump :=
  let rows := Gen.Cmp.rows (requests bs)
  ⟨22, Cmp.width, fun r c => Complete.natCell rows (fun _ => Gen.Cmp.padRow) r c⟩

def dumpOf (table s : String) : Except String Dump :=
  match table with
  | "sha_t" | "sha_r" => return shaDump (← parseList ZkFormal.Sha.Gen.Msg s)
  | "chacha" => return chachaDump (← parseList ZkFormal.Chacha.Gen.Req s)
  | "rng" => return rngDump (← parseList ZkFormal.Chacha.Rng.Gen.Call s)
  | "shuf" => return shufDump (← parseList ZkFormal.Chacha.Shuffle.Gen.SInst s)
  | "codec" => return codecDump (← parseList SchedInJ s)
  | "scandist" => return ssdDump (← parseList SchedInJ s)
  | "proc" => return procDump (← parseList SchedInJ s)
  | "mem" => return memDump (← parseList SchedInJ s)
  | "cmp" => return cmpDump (← parseList SchedInJ s)
  | t => throw s!"unknown table {t}"

/-! ## Honest sampler (native scheduler) -/

/-- splitmix64. -/
abbrev Rnd := StateM UInt64

def next : Rnd UInt64 := do
  let s := (← get) + 0x9E3779B97F4A7C15
  set s
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return z ^^^ (z >>> 31)

def below (n : Nat) : Rnd Nat := do return (← next).toNat % (Nat.max n 1)

def bytes (k : Nat) : Rnd (List Nat) := (List.range k).mapM fun _ => below 256

/-- A sparse 5-byte bitmap (each bit set with probability `1/q`). -/
def bitmap (q : Nat) : Rnd (List Nat) :=
  (List.range 5).mapM fun _ => do
    let mut x := 0
    for i in [0:8] do
      if (← below q) = 0 then x := x + 2 ^ i
    return x

instance : Inhabited Gen.Run :=
  ⟨{ tau := 0, n := 0, base := 0, D := 0, seed := [], key := [], a2 := #[], conv := [], used := #[],
     rounds := [], segs := [], cmps := [], kfin := 0,
     fin := ⟨#[], #[], #[], #[], ⟨[], 0, []⟩⟩ }⟩

/-- One random scheduler block of instance `tau` (`none` if the native run throws). -/
def sampleBlock (tau maxShards maxReqs : Nat) : Rnd (Option SchedInJ) := do
  let n := 1 + (← below maxShards)
  let some p := NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 n | return none
  let idBase ← below 1000000
  let ids := (List.range n).map fun i => idBase * 64 + 7 * i + 1
  let allowed ← (List.range (n * n)).mapM fun _ => do return (← below 4) != 0
  let nreq ← below (maxReqs + 1)
  let q := 1 + (← below 12)
  let raw ← (List.range nreq).mapM fun _ => do
    let s ← below n
    let r ← below n
    let bm ← bitmap q
    return ({ s := s, r := r, bm := bm.map UInt8.ofNat } : RawReq)
  let seed ← bytes 32
  let ash ← bytes 32
  let present := (← below 2) = 1
  let a0 ← if present then (List.range (n * n)).mapM fun _ => below p.maxAllowance else pure []
  let ph ← if present then bytes 32 else pure []
  let b0 : SchedInJ :=
    { run := RunJ.ofRun default, ids := ids, allowed := allowed, params := ParamsJ.ofP p,
      present := present, vid := 0, gb := [], fwd := [], ash := ash, a0 := a0, prev_hash := ph }
  let I : Gen.Input := { b0.input with raw := raw, seed := seed.map UInt8.ofNat }
  match Gen.ActualRun.run I tau with
  | .error _ => return none
  | .ok R =>
    let b1 := { b0 with run := RunJ.ofRun R }
    match Gen.distRows b1.input b1.R with
    | .error _ => return none
    | .ok d =>
      let gb := d.gb.toList
      let fwd ← if tau = 0 then
          (List.range (n * n)).filterMapM fun l => do
            if (← below 2) = 0 then return none
            let cap := (R.segs.getD l default).wfin + gb.getD l 0
            return some [l, ← below (cap + 1)]
        else pure []
      let vid ← below (1 <<< 30)
      let b2 := { b1 with gb := gb, fwd := fwd, vid := vid }
      match ProcPriorCodecGen.codecRows b2.input b2.R b2.present b2.vid b2.grants b2.fwdL with
      | .error _ => return none
      | .ok _ => return some b2

def sampleBlocks (blocks maxShards maxReqs : Nat) : Rnd (List SchedInJ) := do
  let mut out : Array SchedInJ := #[]
  for tau in [0:blocks] do
    let mut got : Option SchedInJ := none
    for _ in [0:50] do
      if got.isNone then got ← sampleBlock tau maxShards maxReqs
    match got with
    | some b => out := out.push b
    | none => pure ()
  return out.toList

end NpSched
