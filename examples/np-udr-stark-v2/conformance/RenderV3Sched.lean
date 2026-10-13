import Conformance.SchedJson

/-!
`np-lean-render-v3-sched` — executable Lean renders of the `nearAirV3` tables
0, 1 (`sha_t`, `sha_r`), 8 (`chacha`), 9 (`rng`), 10 (`shuf`), 11 (`codec`),
12 (`scandist`), 13 (`proc`), 14 (`mem`), 15 (`cmp`), and an honest sampler of
scheduler blocks (the native scheduler `ActualRun.run`).

```
np-lean-render-v3-sched render <table> <entries.json> <out.bin|-> [maxRows]
np-lean-render-v3-sched sample <seed> <blocks> <maxShards> <maxReqs> <outdir>
```

`render` writes the `np-render-v3-table` dump (u32 LE `log, width`, then the
cells row-major, `(tr.cell t r c).toNat`) of the render the D0a completeness
proof uses (`Render/CompleteV3.lean`, `BundleSched.lean`, `sched_renders_on`),
streamed (the scheduler tables are `2^22` rows); with `maxRows` only the first
`maxRows` rows are written (the header keeps the full `log`), so the output is a
prefix of the full dump.

**Executable twins.**  The Lean renders are functions of `(r, c)` that recompute
their row lists per cell (`honestCell = rowCell ((honestRows _).getD r .pad)`,
`procCell rs r c = (atRow rs r).cell c`, `ssdCell bs r c = natCell (rows bs) …`,
`activeUpTo` counts rows `≤ r`), which is quadratic.  Each table below evaluates the
same definitions with the row list computed once (`List.getD` ↦ `Array.getD` of
the same list; `rowsTrace`/`mkTab` cells below the width and height are exactly
these cells):

| table | render (proof) | twin |
|---|---|---|
| sha_t/sha_r | `shaTraceAligned msgs` | `Sha.Gen.rowCell (rows.getD r .pad) c` at `padLog22 (logOf rows)` |
| chacha | `chachaTraceAligned reqs` | `Chacha.Gen.rowCell`, `padLog22 (logOf (86·|reqs|))` |
| rng | `rngTraceW0 calls 9` | base `Chacha.Rng.Gen.rowCell`; col 137 = prefix count of `cv · 129 = 1`, cols `138+e` = `bt (W0 − total) e` |
| shuf | `shufTraceAligned insts` | `Chacha.Shuffle.Gen.rowCell (rows.getD r .pad) r c` |
| codec | `codecCell (bs.map blkOf)` | `natCell ((allDescs Bs).map Desc.row).toArray codecPad`, `Bs` = `blkOfJ` (below) |
| scandist | `ProcScanDistPhases.trace bs` | `natCell (scan rows ++ distribution rows) distPad` |
| proc | `procTraceV3 rs` | `ProcConcatGeometry.atRow` on `(rows rs).toArray`, `tail rs`, `padPV` |
| mem | `MemConcatCells.trace rs` | `natCell (MemConcatCells.rows rs) memPad` |
| cmp | `cmpTraceAligned (requests bs)` | `natCell (Gen.Cmp.rows cmps) (fun _ => padRow)`, `cmps` = per block `run.cmps ++ output.cmps ++ (distribution b).cmps` |

**Entries.**  Tables 0/1/8/9/10: JSON lists of `Sha.Gen.Msg`, `Chacha.Gen.Req`,
`Chacha.Rng.Gen.Call`, `Chacha.Shuffle.Gen.SInst` (Lean field names).  Tables 11–15: a
JSON list of scheduler blocks `SchedInJ` (one per instance `τ`, the Rust
`sched::SchedIn`): the run `Gen.Run` and the block data the certificate reads from
the `NativeBlock` (`ids`, `allowed`, `params`, `present` = `prior.isSome`, `vid`,
`gb` = `grants`, `fwd` = `forwarded`, `ash`, `a0` = the canonical prior allowances
`a0Canon n prev`, `prev_hash` = `prev.sanityHash`).  The block's
`ProcPreparedSequence.input` is rebuilt as `SchedInJ.input` (raw requests are not
read by tables 11–15).

`sample` runs `ActualRun.run` on seeded random scheduler inputs (`Params.calculate
pv86 n`, random allowed matrix, raw requests, seed, `all_shards` hash, absent or
canonical prior state) for instances `τ = 0 … blocks−1`, with the grants of the
distribute grid, random forwarding demands `≤ gfin + gb` (instance 0) and a random
`vid`, and writes `sched.json` (the blocks) and the ChaCha-lane entries of their runs
`chacha.json`, `rng.json`, `shuf.json` (`laneReqs`, `laneCalls`, `laneInsts`).
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3 ZkFormal.NearV3.Render
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Candidates

namespace NpSched


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

open NpSched in
def main (args : List String) : IO UInt32 := do
  match args with
  | "render" :: table :: inp :: out :: rest =>
    let maxRows := (rest.head?.bind String.toNat?).getD (2 ^ 23)
    match dumpOf table (← IO.FS.readFile inp) with
    | .error e => IO.eprintln s!"np-lean-render-v3-sched: {e}"; return 2
    | .ok d =>
      if out == "-" then
        let o ← IO.getStdout
        emit o d.log d.width maxRows d.cell
        o.flush
      else IO.FS.withFile out .write fun h => emit (IO.FS.Stream.ofHandle h) d.log d.width maxRows d.cell
      return 0
  | ["sample", seed, blocks, maxShards, maxReqs, outdir] =>
    let some sd := seed.toNat? | IO.eprintln "seed"; return 2
    let (bs, _) := (sampleBlocks blocks.toNat! maxShards.toNat! maxReqs.toNat!).run sd.toUInt64
    IO.FS.createDirAll outdir
    IO.FS.writeFile s!"{outdir}/sched.json" (toJson bs).compress
    let rs := bs.map SchedInJ.R
    IO.FS.writeFile s!"{outdir}/chacha.json" (toJson (ChachaBus.laneReqs rs)).compress
    IO.FS.writeFile s!"{outdir}/rng.json" (toJson (ChachaBus.laneCalls rs)).compress
    IO.FS.writeFile s!"{outdir}/shuf.json" (toJson (ChachaBus.laneInsts rs)).compress
    IO.println s!"{bs.length} blocks"
    return 0
  | _ =>
    IO.eprintln "usage: np-lean-render-v3-sched render <table> <entries.json> <out.bin|-> [maxRows]\n       np-lean-render-v3-sched sample <seed> <blocks> <maxShards> <maxReqs> <outdir>"
    return 2
