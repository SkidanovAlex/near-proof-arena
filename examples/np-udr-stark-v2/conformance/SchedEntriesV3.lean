import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.TrieNative
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Assembly.SchedulerCodecAllocatedIds
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Candidates.ProcNativeOldComparisonCapacity
import ZkFormal.NearV3.Candidates.ProcActualInput
import ZkFormal.NearV3.Render.PaddedProc
import ZkFormal.NearV3.Render.PaddedSched
import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Candidates.NativeQueueIds
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Conformance.SchedJson

/-!
`np-lean-sched-v3` — the **honest scheduler / ChaCha / queue-value entries** of `nearAirV3`
(tables 8 chacha, 9 rng, 10 shuf, 11 codec, 12 scandist, 13 proc, 14 mem, 15 cmp, 22 qv) for a
real D0a fixture: the ground truth of the Rust derivation `npudr v3sched`.

```
np-lean-sched-v3 <case_dir> <out_dir>                 entries (+ summary.json)
np-lean-sched-v3 render <table> <case_dir> <out|-> [maxRows]
```

**Blocks.**  The completeness proof (`Render/CompleteV3.lean`) renders tables 11–15 from the
`PriorCore` blocks `bs` of the accepted witness and tables 8–10 from their runs
(`chacha_buses_balanced`: `laneReqs/laneCalls/laneInsts (bs.map NativeBlock.run)`).  `bs` is the
list built by `native_allocated_blocks_run` (`SchedulerCodecRetainedAllocation.lean`) →
`native_ordered_blocks_run` → `native_main_block` (main chunk, `τ = 0`) and
`implicit_blocks_run` / `native_missing_block` (one per implicit step, `τ = 1, 2, …`); here the
same construction is evaluated (`mkBlock`):

* `witness = schedulerUpsertWitness ctx pre`, with `(ctx, pre) = (m.ctx k, m.pre)` then
  `(implicitCtx k e, e.pre)` (`hctx` of `rcpt_trie_vbytes`);
* `pub = p.sched[τ]` (checked `= schedPub ctx`), `prior = readKey pre keyBwState`,
  `old = decodePrevious prior`, `I = ProcPreparedSequence.input pub old`;
* `run = ActualRun.run I τ`;
* `grants = gd` of `distributeEv n allowed st.sb st.rb lp.cntS lp.cntR` with
  `(st, _) = ProcActualInput.process I` and `lp = linkPass … (allowances ids prev)`
  (`ProcNativeMainCodecWitness.native_main` / `ProcActualNativeFinish.distribution_exists`);
* `vid = nativePriorIds (m.pre :: steps.pre) τ` (`native_allocated_blocks_run`);
* `forwarded = fwdLinks ctx out.outgoing` for the main block, `[]` for missing chunks;
* `output = ProcPriorCodecGen.codecRows I run prior.isSome vid grants forwarded`.

Entries are written in the `np-lean-render-v3-sched` / Rust `sched::SchedIn` format
(`SchedInJ`, `a0 = a0Canon n prev`, `prev_hash = prev.sanityHash`, `gb = grants`, `fwd`): files
`codec.json scandist.json proc.json mem.json cmp.json` (the same block list), `chacha.json`
(`laneReqs`), `rng.json` (`laneCalls`), `shuf.json` (`laneInsts`).  `SchedInJ` rebuilds the prior
state canonically (record `l` = link `l`); `summary.json` reports whether that rebuild has the
same `allowances` as the real prior state (the only other prior-state read of tables 11–15) and
the grid/`distRows` grant agreement.

**qv (22).**  `A.qvAcc = qvRenderV3 pub m.pre qvVals (steps.map pre)` (`RenderV3RcptAccepted`):
walks `qvNativeWalks pre v pres` (`plan pre v pres (NativeQueueIds.resolve pre v pres)`) and
records `qvNativeRecords pre v pres`, `v` the unique `MainValues` read from `m.pre`
(`mainValues_unique`); `qv.json` in the `np-lean-render-v3 qv` / Rust `qv::QvIn` format.

**Renders** (`render` mode) evaluate the proof's trace definitions on the native blocks with
the row lists computed once (`*_twin` lemmas below: equal cells): codec `codecCell (bs.map blkOf)`,
scandist `ProcScanDistPhases.trace bs`, proc `procTraceV3 rs`, mem `MemConcatCells.trace rs`,
cmp `cmpTraceAligned (requests bs)`, qv `qvTraceAligned … = mixedTrace`; tables 8–10 through the
`np-lean-render-v3-sched` twins of `chachaTraceAligned`/`rngTraceW0`/`shufTraceAligned` on the
lane entries.
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open NearSpec NearSpecV3

namespace NpSchedNative

deriving instance BEq for NearSpecV3.Scheduler.SchedPub

/-! ## Native objects (as `TrieEntriesV3.nativeOf`, without the account replay) -/

structure SNat where
  k : WalkD0
  w : StateWitness
  m : MainExecutionV3
  steps : List ImplicitStepV3
  p : Prep

def nativeOf (cb wb : Bytes) : Except String SNat := do
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

/-- The unique `MainValues` with `Valid ∧ Reads m.pre m.pre m.pre` (`mainValues_unique`). -/
def mainValuesOf (m : MainExecutionV3) : Except String Qv.MainValues := do
  let rd (key : List Nat) (what : String) : Except String (Option Bytes) :=
    match m.pre.find key with | some v => pure v | none => throw s!"main values: {what} unread"
  let d ← rd keyDelayedIdx "delayed"
  let b ← rd keyBufferedIdx "buffered"
  let y ← rd keyYieldIdx "yield"
  pure ⟨d, b, m.bufferedShards, y⟩

/-! ## The `PriorCore` blocks -/

/-- One native block (the construction of `native_main_block` / `native_missing_block`). -/
def mkBlock (p : Prep) (trees : List PTrie) (tau : Nat) (ctx : ApplyCtx) (pre : PTrie)
    (fwd : List (Nat × Nat)) : Except String NativeBlock := do
  let u ← schedulerUpsertWitness ctx pre
  let sp ← match p.sched[tau]? with
    | some sp => pure sp | none => throw s!"block {tau}: no prepared scheduler instance"
  match schedPub ctx with
  | some sp' => unless sp' == sp do throw s!"block {tau}: schedPub ctx ≠ p.sched[τ]"
  | none => throw s!"block {tau}: schedPub ctx = none"
  let prior ← readKey pre keyBwState "bandwidth scheduler state"
  let old ← match ProcActualCore.decodePrevious prior with
    | some s => pure s | none => throw s!"block {tau}: prior state does not decode"
  let I := ProcPreparedSequence.input sp old
  let R ← Gen.ActualRun.run I tau
  let (st, _) ← ProcActualInput.process I
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let (gd, _, _) ← distributeEv I.ids.length I.allowed st.sb st.rb lp.cntS lp.cntR
  let vid := nativePriorIds trees tau
  let out ← ProcPriorCodecGen.codecRows I R prior.isSome vid gd fwd
  pure ⟨u, sp, prior, old, R, vid, gd, fwd, out⟩

/-- `bs`: the main block, then one block per implicit step. -/
def blocksOf (N : SNat) : Except String (List NativeBlock) := do
  let trees := N.m.pre :: N.steps.map ImplicitStepV3.pre
  let b0 ← mkBlock N.p trees 0 (N.m.ctx N.k) N.m.pre (fwdLinks (N.m.ctx N.k) N.m.result.outgoing)
  let tail ← N.steps.zipIdx.mapM fun (e, i) => mkBlock N.p trees (i + 1) (implicitCtx N.k e) e.pre []
  pure (b0 :: tail)

/-- The `SchedInJ` (Rust `sched::SchedIn`) view of a native block. -/
def toJ (b : NativeBlock) : NpSched.SchedInJ :=
  let I := ProcPreparedSequence.input b.pub b.old
  { run := NpSched.RunJ.ofRun b.run, ids := I.ids, allowed := I.allowed.toList,
    params := NpSched.ParamsJ.ofP I.p, present := b.prior.isSome, vid := b.vid,
    gb := b.grants.toList, fwd := b.forwarded.map fun (l, d) => [l, d],
    ash := I.ash.map (·.toNat), a0 := (a0Canon b.run.n I.prev).toList,
    prev_hash := I.prev.sanityHash.map (·.toNat) }

/-- The prior state the `SchedInJ` view rebuilds has the same `allowances` (the codec record
step's `a0s`) and the same `a0Canon` as the real one, and the grid grants equal `distRows`'. -/
def viewChecks (b : NativeBlock) : List (String × Bool) :=
  let I := ProcPreparedSequence.input b.pub b.old
  let j := toJ b
  [ ("allowances ids prev = allowances ids (canonical rebuild)",
      ProcActualInput.allowances I.ids I.prev == ProcActualInput.allowances I.ids j.prev)
  , ("a0Canon prev = a0Canon (canonical rebuild)", a0Canon b.run.n I.prev == a0Canon b.run.n j.prev)
  , ("sanityHash", I.prev.sanityHash == j.prev.sanityHash)
  , ("grants = distRows gb", (ProcNativeOldComparisonCapacity.distribution b).gb == b.grants)
  , ("codec cmps (view) = output.cmps", j.codecCmps == b.output.cmps) ]

/-! ## The queue-value entries (table 22) -/

def walkJ (w : Qv.Candidates.CombinedWalkGen.Walk) : Json :=
  let shard := match w.kind with | .group s => s | _ => 0
  Json.mkObj [("code", toJson w.kind.code), ("shard", toJson shard), ("tau", toJson w.tau),
    ("slot", toJson w.slot), ("count", toJson w.count),
    ("value", match w.value with | some v => toJson (v.map (·.toNat)) | none => Json.null),
    ("vid", toJson w.vid), ("users", toJson w.users), ("lastMain", toJson w.lastMain),
    ("final", toJson w.final)]

def recJ (r : Qv.Candidates.ValueGen.Record) : Json :=
  let (kind, ix, es, bs) : Nat × Bytes × List Qv.ByteBuffer × Bytes := match r.payload with
    | .empty ix => (0, ix, [], []) | .buffer es => (1, [], es, []) | .raw bs => (2, [], [], bs)
  Json.mkObj [("rkind", toJson kind), ("vid", toJson r.vid), ("tau", toJson r.tau),
    ("users", toJson r.users), ("index", toJson (ix.map (·.toNat))),
    ("entries", Json.arr (es.map fun e => Json.mkObj [("shard", toJson (e.shard.map (·.toNat))),
      ("index", toJson (e.index.map (·.toNat)))]).toArray),
    ("bytes", toJson (bs.map (·.toNat)))]

structure QvData where
  ws : List Qv.Candidates.CombinedWalkGen.Walk
  vs : List Qv.Candidates.ValueGen.Record

def qvOf (N : SNat) : Except String QvData := do
  let v ← mainValuesOf N.m
  let pres := N.steps.map ImplicitStepV3.pre
  pure ⟨qvNativeWalks N.m.pre v pres, qvNativeRecords N.m.pre v pres⟩

def QvData.json (q : QvData) : Json :=
  Json.mkObj [("walks", Json.arr (q.ws.map walkJ).toArray), ("records", Json.arr (q.vs.map recJ).toArray)]

/-! ## Executable twins of the proof's trace definitions (row lists computed once)

Each table's rows are tabulated by a `*Rows` definition and read by a `*Cell` function; the
`*_twin` lemmas state that `*Cell (*Rows x)` is the proof's cell.  (The driver computes `*Rows`
once and closes the cell function over it.) -/

/-- `natCell rows pad` (`Sched/Complete/Trace.lean`) as a cell function. -/
def natCellOf (pad : Nat → Array Nat) (rows : Array (Array Nat)) (r c : Nat) : Nat :=
  Complete.natCell rows pad r c

/-- Table 11 rows: the descriptor rows of `bs.map blkOf`. -/
def codecRowsA (bs : List NativeBlock) : Array (Array Nat) :=
  ((Cdc.allDescs (bs.map Cdc.blkOf)).map Cdc.Desc.row).toArray

theorem codec_twin (bs : List NativeBlock) (r c : Nat) :
    natCellOf Gen.codecPad (codecRowsA bs) r c = Cdc.codecCell (bs.map Cdc.blkOf) r c := rfl

/-- Table 12: `ProcScanDistPhases.trace bs`. -/
theorem ssd_twin (bs : List NativeBlock) (t r c : Nat) :
    (ProcScanDistPhases.trace bs).cell t r c =
      Fp.ofNat (natCellOf Gen.distPad (ProcScanDistPhases.rows bs) r c) := rfl

/-- Table 13: `procTraceV3 rs` (`procCell rs r c = (atRow rs r).cell c`). -/
def procCellA (rows : Array Complete.PV) (tl : Complete.PV) (r c : Nat) : Nat :=
  (if h : r < rows.size then rows[r] else if r = rows.size then tl else Complete.padPV).cell c

theorem proc_twin (rs : List Gen.Run) (r c : Nat) :
    procCellA (ProcConcatGeometry.rows rs).toArray (ProcConcatGeometry.tail rs) r c = procCell rs r c := by
  simp only [procCellA, procCell, ProcConcatGeometry.atRow, List.size_toArray, List.getElem_toArray]

/-- Table 14: `MemConcatCells.trace rs`. -/
theorem mem_twin (rs : List Gen.Run) (t r c : Nat) :
    (MemConcatCells.trace rs).cell t r c = Fp.ofNat (natCellOf Complete.memPad (MemConcatCells.rows rs) r c) :=
  rfl

/-- Table 15: `cmpTraceAligned (requests bs)` (= `SchedHeight.trace` below `2^22`). -/
def cmpRowsA (bs : List NativeBlock) : Array (Array Nat) :=
  Gen.Cmp.rows (ProcNativeOldComparisonCapacity.requests bs)

theorem cmp_twin (bs : List NativeBlock) (t r c : Nat) (hr : r < 2 ^ 22) :
    (cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs)).cell t r c =
      Fp.ofNat (natCellOf (fun _ => Gen.Cmp.padRow) (cmpRowsA bs) r c) :=
  (schedTraceAligned_cells _ _ t r hr c).symm

/-- Table 22: `mixedTrace ws vs log` with the row list tabulated. -/
def qvCellA (rows : Array (List Nat)) (r c : Nat) : Nat := (rows.getD r []).getD c 0

theorem qv_twin (ws : List Qv.Candidates.CombinedWalkGen.Walk) (vs : List Qv.Candidates.ValueGen.Record)
    (r c : Nat) : qvCellA (Qv.Candidates.CombinedWalkGen.mixedRows ws vs).toArray r c =
      ((Qv.Candidates.CombinedWalkGen.mixedRows ws vs).getD r []).getD c 0 := by
  simp only [qvCellA, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

def qvLog (q : QvData) : Nat := ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (qvRows q.ws q.vs))

/-! ## Driver -/

def liftE {α : Type} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)

def load (dir : String) : IO SNat := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => throw (IO.userError s!"checkD0a failed: {e}")
  | .ok () => liftE (nativeOf cb wb)

def dumpOfNative (N : SNat) (table : String) : Except String NpSched.Dump := do
  match table with
  | "qv" =>
    let q ← qvOf N
    let rows := (Qv.Candidates.CombinedWalkGen.mixedRows q.ws q.vs).toArray
    return ⟨qvLog q, Qv.Candidates.CombinedTable.width, qvCellA rows⟩
  | _ =>
    let bs ← blocksOf N
    let rs := bs.map NativeBlock.run
    match table with
    | "chacha" => return NpSched.chachaDump (ChachaBus.laneReqs rs)
    | "rng" => return NpSched.rngDump (ChachaBus.laneCalls rs)
    | "shuf" => return NpSched.shufDump (ChachaBus.laneInsts rs)
    | "codec" => let rows := codecRowsA bs; return ⟨22, Codec.width, natCellOf Gen.codecPad rows⟩
    | "scandist" =>
      let rows := ProcScanDistPhases.rows bs; return ⟨22, ScanDist.width, natCellOf Gen.distPad rows⟩
    | "proc" =>
      let rows := (ProcConcatGeometry.rows rs).toArray
      let tl := ProcConcatGeometry.tail rs
      return ⟨22, Proc.width, procCellA rows tl⟩
    | "mem" => let rows := MemConcatCells.rows rs; return ⟨22, Mem.width, natCellOf Complete.memPad rows⟩
    | "cmp" => let rows := cmpRowsA bs; return ⟨22, Cmp.width, natCellOf (fun _ => Gen.Cmp.padRow) rows⟩
    | t => throw s!"unknown table {t}"

def entries (dir out : String) : IO UInt32 := do
  let N ← load dir
  let bs ← liftE (blocksOf N)
  let rs := bs.map NativeBlock.run
  let q ← liftE (qvOf N)
  IO.FS.createDirAll out
  let js := (toJson (bs.map toJ)).compress
  for t in ["codec", "scandist", "proc", "mem", "cmp"] do
    IO.FS.writeFile s!"{out}/{t}.json" js
  IO.FS.writeFile s!"{out}/chacha.json" (toJson (ChachaBus.laneReqs rs)).compress
  IO.FS.writeFile s!"{out}/rng.json" (toJson (ChachaBus.laneCalls rs)).compress
  IO.FS.writeFile s!"{out}/shuf.json" (toJson (ChachaBus.laneInsts rs)).compress
  IO.FS.writeFile s!"{out}/qv.json" q.json.compress
  let checks := bs.zipIdx.flatMap fun (b, i) => (viewChecks b).map fun (n, ok) => (s!"block {i}: {n}", ok)
  let summary := Json.mkObj
    [ ("blocks", toJson bs.length)
    , ("requests", toJson (rs.map fun R => R.conv.length))
    , ("rounds", toJson (rs.map fun R => R.rounds.length))
    , ("shards", toJson (rs.map fun R => R.n))
    , ("kfin", toJson (rs.map fun R => R.kfin))
    , ("present", toJson (bs.map fun b => b.prior.isSome))
    , ("qv_walks", toJson q.ws.length), ("qv_records", toJson q.vs.length)
    , ("qv_rows", toJson (qvRows q.ws q.vs))
    , ("checks", Json.mkObj (checks.map fun (n, ok) => (n, Json.bool ok))) ]
  IO.FS.writeFile s!"{out}/summary.json" summary.compress
  let bad := checks.filter (!·.2)
  for (n, _) in bad do IO.eprintln s!"np-lean-sched-v3: {dir}: check failed: {n}"
  IO.println s!"{bs.length} blocks, {(rs.map fun R => R.conv.length).sum} requests, qv {q.ws.length} walks / {q.vs.length} records"
  return (if bad.isEmpty then 0 else 3)

end NpSchedNative

open NpSchedNative in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "render" :: table :: dir :: out :: rest =>
      let maxRows := (rest.head?.bind String.toNat?).getD (2 ^ 23)
      let N ← load dir
      let d ← liftE (dumpOfNative N table)
      if out == "-" then
        let o ← IO.getStdout
        NpSched.emit o d.log d.width maxRows d.cell
        o.flush
      else IO.FS.withFile out .write fun h => NpSched.emit (IO.FS.Stream.ofHandle h) d.log d.width maxRows d.cell
      return 0
    | [dir, out] => entries dir out
    | _ =>
      IO.eprintln "usage: np-lean-sched-v3 <case_dir> <out_dir>\n       np-lean-sched-v3 render <table> <case_dir> <out.bin|-> [maxRows]"
      return 2
  catch e =>
    IO.eprintln s!"np-lean-sched-v3: {e}"
    return 2
