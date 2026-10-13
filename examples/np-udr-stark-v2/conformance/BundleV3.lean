import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Assembly.SchedulerPriorValueId
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Render.CodecNative
import ZkFormal.NearV3.Render.ChachaLane
import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcPreparedSequence
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-bundle-v3 <case_dir> <out_dir>` — the honest entries of the `nearAirV3` tables the
Rust prover cannot yet derive natively (lane v3-prover-prove stopgap until lane
v3-prover-schedqv publishes its native port), for a real D0a fixture:

* `sched.json` (tables 11 codec, 12 scandist, 13 proc, 14 mem, 15 cmp): the scheduler blocks
  `bs` of the completeness proof (`RcptTrieSide.rcpt_trie_vbytes`, `PriorCore`), one per
  scheduler call `τ` — main chunk first, then the implicit steps
  (`bs.map (ctx, pre) = (m.ctx k, m.pre) :: steps.map (implicitCtx k e, e.pre)`), as the Rust
  `sched::SchedIn` / Lean `NpSched.SchedInJ` JSON (`RenderV3Sched.lean`):
  `pub = p.sched[τ]`, `prior = readKey pre keyBwState`, `old` its decoding (or `State.initial`),
  `run = ActualRun.run (ProcPreparedSequence.input pub old) τ` (`PreparedRun`),
  `vid = priorValueId (pres.take τ) pre`, grants `gb` = the native distribution grid
  (`GrantWit`, via `Gen.distRows`), `fwd = fwdLinks (m.ctx k) m.result.outgoing` at `τ = 0`
  (else `[]`), `a0 = a0Canon n old`, `prev_hash = old.sanityHash`.
* `chacha.json` / `rng.json` / `shuf.json` (tables 8, 9, 10): `ChachaBus.laneReqs/laneCalls/
  laneInsts` of the runs.
* `qv.json` (table 22): `{walks, records}` = `qvNativeWalks m.pre v pres` /
  `qvNativeRecords m.pre v pres` (`AcceptedV3.qvAcc`, `qvRenderV3`), `v` the main values read
  from `m.pre` (`mainValues_unique`), in the `NearRenderV3.QvIn` JSON the Rust `qv::render` reads.

The native objects (`k w m steps p`) are built as in `TrieEntriesV3.lean`'s `nativeOf`.
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Render
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3

deriving instance ToJson for ZkFormal.Chacha.Gen.Req
deriving instance ToJson for ZkFormal.Chacha.Rng.Gen.Call
deriving instance ToJson for ZkFormal.Chacha.Shuffle.Gen.SInst

namespace NpBundle

/-! ## JSON mirrors (the `NpSched` structures of `RenderV3Sched.lean`, output only) -/

structure CReqJ where
  cid : Nat
  s : Nat
  r : Nat
  link : Nat
  bm : List Nat
  bits : List Nat
  incs : List Nat
  key : Nat
  deriving ToJson

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
  deriving ToJson

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
  deriving ToJson

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
  deriving ToJson

structure SegJ where
  addr : Nat
  isL : Bool
  al : Bool
  vin0 : Nat
  v0 : Nat
  w0 : Nat
  ops : List MOpJ
  deriving ToJson

structure RngJ where
  key : List Nat
  ctr : Nat
  buf : List Nat
  deriving ToJson

structure PStateJ where
  sb : List Nat
  rb : List Nat
  al : List Nat
  g : List Nat
  rng : RngJ
  deriving ToJson

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
  deriving ToJson

structure ParamsJ where
  base : Nat
  maxShardBandwidth : Nat
  maxSingleGrant : Nat
  maxReceiptSize : Nat
  maxAllowance : Nat
  deriving ToJson

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
  deriving ToJson

def EntryJ.ofE (e : Gen.Entry) : EntryJ :=
  { x := e.x, ts := e.ts, ein := e.ein, eout := e.eout, inc := e.inc, rem := e.rem, s := e.s, r := e.r,
    link := e.link, sbIn := e.sbIn, sbOut := e.sbOut, rbIn := e.rbIn, rbOut := e.rbOut, alIn := e.alIn,
    alOut := e.alOut, cS := e.cS, cR := e.cR, cL := e.cL, ok := e.ok, push := e.push, zn := e.zn }

def MOpJ.ofM (o : Gen.MOp) : MOpJ :=
  { t := o.t, op := o.op, vin := o.vin, v := o.v, wp := o.wp, w := o.w, inc := o.inc, ok := o.ok,
    c := o.c, sf := o.sf }

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

def ParamsJ.ofP (p : NearSpecV3.Scheduler.Params) : ParamsJ :=
  ⟨p.base, p.maxShardBandwidth, p.maxSingleGrant, p.maxReceiptSize, p.maxAllowance⟩

/-! ## Native objects (as `TrieEntriesV3.nativeOf`, without the account replay) -/

structure Nat3 where
  k : WalkD0
  w : StateWitness
  m : MainExecutionV3
  steps : List ImplicitStepV3
  p : Prep

def nativeOf (cb wb : Bytes) : Except String Nat3 := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk: B2"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk: prev B2"
  let receipts := appliedReceipts k w
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing buffered index"
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot (mainKeys receipts bshards)
  let ctx := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let out ← applyNewChunk prims ctx tMain receipts
  let m : MainExecutionV3 := ⟨B2, prevB2, bshards, tMain, out⟩
  let (steps, _) ← traceImplicit k out.trie.hashOf (k.implicitBlks.zip w.implicit)
  let p ← prepD0 cb (nativeHint k w m)
  pure ⟨k, w, m, steps, p⟩

/-- The scheduler block of call `tau` (context `ctx`, state read `pre`, earlier pres `before`). -/
def blockOf (N : Nat3) (before : List PTrie) (tau : Nat) (ctx : ApplyCtx) (pre : PTrie) :
    Except String (SchedInJ × Gen.Run) := do
  let sp ← match N.p.sched[tau]? with | some s => pure s | none => throw s!"block {tau}: no p.sched entry"
  if (schedPub ctx).isNone then throw s!"block {tau}: schedPub ctx = none"
  let prior ← readKey pre keyBwState "bandwidth scheduler state"
  let old ← match prior with
    | none => pure Bandwidth.State.initial
    | some raw => match Bandwidth.State.decode raw with
      | some s => pure s | none => throw s!"block {tau}: prior state does not decode"
  let I := ProcPreparedSequence.input sp old
  let R ← Gen.ActualRun.run I tau
  let d ← Gen.distRows I R
  let n := sp.ids.length
  let fwdL : List (Nat × Nat) := if tau = 0 then fwdLinks (N.m.ctx N.k) N.m.result.outgoing else []
  let fwd : List (List Nat) := fwdL.map fun (l, x) => [l, x]
  let b : SchedInJ :=
    { run := RunJ.ofRun R, ids := sp.ids, allowed := sp.allowed.toList, params := ParamsJ.ofP sp.params,
      present := prior.isSome, vid := priorValueId before pre, gb := d.gb.toList, fwd := fwd,
      ash := sp.allShardsHash.map (·.toNat), a0 := (a0Canon n old).toList,
      prev_hash := old.sanityHash.map (·.toNat) }
  -- the codec generator accepts the block (`NativeBlock.Valid`)
  match ProcPriorCodecGen.codecRows I R prior.isSome b.vid d.gb fwdL with
  | .ok _ => pure (b, R)
  | .error e => throw s!"block {tau}: codecRows: {e}"

def blocks (N : Nat3) : Except String (List SchedInJ × List Gen.Run) := do
  let calls := (N.m.ctx N.k, N.m.pre) :: N.steps.map (fun e => (implicitCtx N.k e, e.pre))
  let pres := calls.map Prod.snd
  let mut bs : Array SchedInJ := #[]
  let mut rs : Array Gen.Run := #[]
  for ((ctx, pre), tau) in calls.zipIdx do
    let (b, R) ← blockOf N (pres.take tau) tau ctx pre
    bs := bs.push b
    rs := rs.push R
  return (bs.toList, rs.toList)

/-! ## qv -/

def bytesJ (b : Bytes) : Json := toJson (b.map (·.toNat))

def walkJ (w : Qv.Candidates.CombinedWalkGen.Walk) : Json :=
  let (code, shard) := match w.kind with
    | .delayed => (0, 0) | .buffered => (1, 0) | .yielded => (2, 0) | .group s => (3, s)
  Json.mkObj [("code", toJson code), ("shard", toJson shard), ("tau", toJson w.tau),
    ("slot", toJson w.slot), ("count", toJson w.count),
    ("value", match w.value with | some v => bytesJ v | none => Json.null),
    ("vid", toJson w.vid), ("users", toJson w.users), ("lastMain", toJson w.lastMain),
    ("final", toJson w.final)]

def recJ (v : Qv.Candidates.ValueGen.Record) : Json :=
  let base := [("vid", toJson v.vid), ("tau", toJson v.tau), ("users", toJson v.users)]
  match v.payload with
  | .empty ix => Json.mkObj (("rkind", toJson (0 : Nat)) :: ("index", bytesJ ix) :: base)
  | .buffer es => Json.mkObj (("rkind", toJson (1 : Nat)) ::
      ("entries", Json.arr (es.map fun e => Json.mkObj [("shard", bytesJ e.shard),
        ("index", bytesJ e.index)]).toArray) :: base)
  | .raw bs => Json.mkObj (("rkind", toJson (2 : Nat)) :: ("bytes", bytesJ bs) :: base)

def mainValuesOf (m : MainExecutionV3) : Except String Qv.MainValues := do
  let rd (key : List Nat) (what : String) : Except String (Option Bytes) :=
    match m.pre.find key with | some v => pure v | none => throw s!"main values: {what} unread"
  let d ← rd keyDelayedIdx "delayed"
  let b ← rd keyBufferedIdx "buffered"
  let y ← rd keyYieldIdx "yield"
  pure ⟨d, b, m.bufferedShards, y⟩

def qvJ (N : Nat3) : Except String Json := do
  let v ← mainValuesOf N.m
  let pres := N.steps.map ImplicitStepV3.pre
  let ws := qvNativeWalks N.m.pre v pres
  let vs := qvNativeRecords N.m.pre v pres
  return Json.mkObj [("walks", Json.arr (ws.map walkJ).toArray),
    ("records", Json.arr (vs.map recJ).toArray)]

end NpBundle

open NpBundle in
def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, outdir] =>
    let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
    let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
    match checkD0a B0 cb wb with
    | .error e => IO.eprintln s!"np-lean-bundle-v3: {dir}: checkD0a failed: {e}"; return 2
    | .ok () =>
    match nativeOf cb wb with
    | .error e => IO.eprintln s!"np-lean-bundle-v3: {dir}: {e}"; return 2
    | .ok N =>
    match blocks N, qvJ N with
    | .error e, _ | _, .error e => IO.eprintln s!"np-lean-bundle-v3: {dir}: {e}"; return 2
    | .ok (bs, rs), .ok q =>
      IO.FS.createDirAll outdir
      IO.FS.writeFile s!"{outdir}/sched.json" (toJson bs).compress
      IO.FS.writeFile s!"{outdir}/chacha.json" (toJson (ChachaBus.laneReqs rs)).compress
      IO.FS.writeFile s!"{outdir}/rng.json" (toJson (ChachaBus.laneCalls rs)).compress
      IO.FS.writeFile s!"{outdir}/shuf.json" (toJson (ChachaBus.laneInsts rs)).compress
      IO.FS.writeFile s!"{outdir}/qv.json" q.compress
      IO.println s!"bundle: {bs.length} scheduler blocks, chacha {(ChachaBus.laneReqs rs).length} reqs, rng {(ChachaBus.laneCalls rs).length} calls, shuf {(ChachaBus.laneInsts rs).length} insts"
      return 0
  | _ => IO.eprintln "usage: np-lean-bundle-v3 <case_dir> <out_dir>"; return 2
