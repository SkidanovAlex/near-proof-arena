import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import SchedJson
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Render.ChachaLane
import ZkFormal.NearV3.Candidates.ProcPreparedSequence
import ZkFormal.NearV3.Sched.Gen.Dist
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-sched-v3 <case_dir> [<out_dir>]` — honest **scheduler-side** entries of
`nearAirV3` for a real D0a fixture (tables 11–15 and the ChaCha lane 8/9/10), the
ground truth of `npudr v3sched` / `npudr v3chacha`.

Re-runs the native execution of an accepted witness, reconstructs each applied
block's `SchedIn` (the Rust `sched::SchedIn`) from the actual scheduler run
`ActualRun.run (ProcPreparedSequence.input sp prev) τ` and the distribute grid
`distRows`, and emits the ChaCha lane entries of the runs.
-/
open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3
open NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render

namespace NpSchedEntries

deriving instance ToJson for ZkFormal.Chacha.Gen.Req
deriving instance ToJson for ZkFormal.Chacha.Rng.Gen.Call
deriving instance ToJson for ZkFormal.Chacha.Shuffle.Gen.SInst

structure Native where
  k : WalkD0
  w : StateWitness
  m : MainExecutionV3
  steps : List ImplicitStepV3
  p : Prep

def hashNats (raw : Bytes) : List Nat :=
  ((Bandwidth.State.decode raw).map (fun s => s.sanityHash)).getD [] |>.map (·.toNat)

/-- Build the `SchedInJ` of one applied block from its native scheduler inputs. -/
def schedInOf (tau : Nat) (sp : NearSpecV3.Scheduler.SchedPub) (prior : Option Bytes)
    (forwarded : List (Nat × Nat)) (vid : Nat) : NpSched.SchedInJ :=
  let old := match prior with
    | none => Bandwidth.State.initial
    | some raw => (Bandwidth.State.decode raw).getD Bandwidth.State.initial
  let I := ProcPreparedSequence.input sp old
  let R := (ActualRun.run I tau).toOption.getD default
  let d := (distRows I R).toOption.getD ⟨#[], #[], []⟩
  { run := NpSched.RunJ.ofRun R
    ids := sp.ids
    allowed := sp.allowed.toList
    params := NpSched.ParamsJ.ofP sp.params
    present := prior.isSome
    vid := vid
    gb := d.gb.toList
    fwd := forwarded.map fun (l, t) => [l, t]
    ash := sp.allShardsHash.map (·.toNat)
    a0 := (a0Canon R.n I.prev).toList
    prev_hash := match prior with | some raw => hashNats raw | none => [] }

def runsOf (N : Native) : Except String (List Run) := do
  let ctx := N.m.ctx N.k
  let sp0 ← match N.p.sched[0]? with | some s => pure s | none => throw "sched[0]"
  let prior0 ← match N.m.pre.find keyBwState with | some v => pure v | none => pure none
  let old0 := match prior0 with
    | none => Bandwidth.State.initial
    | some raw => (Bandwidth.State.decode raw).getD Bandwidth.State.initial
  let R0 ← match ActualRun.run (ProcPreparedSequence.input sp0 old0) 0 with
    | .ok r => pure r | .error e => throw s!"main run: {e}"
  let mut out : List Run := [R0]
  for h : i in [0:N.steps.length] do
    let e := N.steps[i]
    let tau := i + 1
    let sp ← match N.p.sched[tau]? with | some s => pure s | none => throw s!"sched[{tau}]"
    let prior ← match e.pre.find keyBwState with | some v => pure v | none => pure none
    let old := match prior with
      | none => Bandwidth.State.initial
      | some raw => (Bandwidth.State.decode raw).getD Bandwidth.State.initial
    let R ← match ActualRun.run (ProcPreparedSequence.input sp old) tau with
      | .ok r => pure r | .error e => throw s!"run τ={tau}: {e}"
    out := out ++ [R]
  pure out

/-- (prior, forwarded) inputs per applied block for the `SchedInJ` list. -/
def schedInsOf (N : Native) : Except String (List NpSched.SchedInJ) := do
  let ctx := N.m.ctx N.k
  let sp0 ← match N.p.sched[0]? with | some s => pure s | none => throw "sched[0]"
  let prior0 ← match N.m.pre.find keyBwState with | some v => pure v | none => pure none
  let mut out : List NpSched.SchedInJ := [schedInOf 0 sp0 prior0 (fwdLinks ctx N.m.result.outgoing) 0]
  for h : i in [0:N.steps.length] do
    let e := N.steps[i]
    let tau := i + 1
    let sp ← match N.p.sched[tau]? with | some s => pure s | none => throw s!"sched[{tau}]"
    let prior ← match e.pre.find keyBwState with | some v => pure v | none => pure none
    out := out ++ [schedInOf tau sp prior [] 0]
  pure out

def nativeOf (cb wb : Bytes) : Except String Native := do
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
  let (steps, last) ←
    match traceImplicit k out.trie.hashOf (k.implicitBlks.zip w.implicit) with
    | .ok r => pure r
    | .error e => throw s!"implicit: {e}"
  if last != k.H.prevStateRoot then throw "implicit: post state root"
  let p ← prepD0 cb (nativeHint k w m)
  pure ⟨k, w, m, steps, p⟩

def runCase (outDir : Option String) (dir : String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => IO.eprintln s!"np-lean-sched-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
    match nativeOf cb wb with
    | .error e => IO.eprintln s!"np-lean-sched-v3: {dir}: {e}"; return 2
    | .ok N =>
      match runsOf N, schedInsOf N with
      | .ok rs, .ok ins =>
        let sched := Json.compress (Json.arr (ins.map (fun b => toJson b)).toArray)
        let chacha := Json.compress (toJson (ChachaBus.laneReqs rs))
        let rng := Json.compress (toJson (ChachaBus.laneCalls rs))
        let shuf := Json.compress (toJson (ChachaBus.laneInsts rs))
        match outDir with
        | none => IO.println sched; IO.println chacha; IO.println rng; IO.println shuf
        | some od =>
          IO.FS.createDirAll od
          IO.FS.writeFile (od ++ "/sched.json") sched
          IO.FS.writeFile (od ++ "/chacha.json") chacha
          IO.FS.writeFile (od ++ "/rng.json") rng
          IO.FS.writeFile (od ++ "/shuf.json") shuf
        IO.println s!"{ins.length} scheduler blocks"
        return 0
      | .error e, _ | _, .error e => IO.eprintln s!"np-lean-sched-v3: {dir}: {e}"; return 2

end NpSchedEntries

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => NpSchedEntries.runCase none dir
  | [dir, outDir] => NpSchedEntries.runCase (some outDir) dir
  | _ => IO.eprintln "usage: np-lean-sched-v3 <case_dir> [<out_dir>]"; return 2
