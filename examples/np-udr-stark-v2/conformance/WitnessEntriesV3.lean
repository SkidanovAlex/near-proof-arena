import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.ForestViews
import ZkFormal.NearV3.Assembly.TraceHeads
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata
import ZkFormal.NearV3.Render.UniqGen
import ZkFormal.NearV3.Render.WalkGen
import ZkFormal.NearV3.Rcpt.Render.AkeyRender
import ZkFormal.NearV3.Rcpt.Render.BndRender
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-entries-v3 <case_dir> [<table>]` — part 2c of `np-udr-stark-v2`: the
**witness → per-table entries** extraction, differential-tested against the Rust
`node` (`src/v3`) generator.

Reads `case_dir/claim.bin` and `case_dir/witness.bin`; if `checkD0a B0 cb wb = .ok ()`
(the deployed D0a relation) and the reference execution trace
(`ZkFormal.V3.Tools.TestPrep.trace`) succeeds, it computes the per-table entry lists
that the Lean aligned generators (`Render/Padded.lean`, `Render/PaddedTrie.lean`)
consume, and prints them as JSON (Lean's `ToJson`, the same nested-tagged encoding
`NearRenderV3.lean`'s `FromJson` expects).

Tables derived here (the ones whose Rust generators exist in `src/v3`):

* `node`   — `initializeList 0 (forestNodes 0 0 0 ts)` (the concrete occurrence
  forest with local metadata: `ucid` from `windowIds`, zero use counts);
* `val`    — `seedValuesFrom 0 (forestBytes ts)`;
* `head`   — `traceHeads 0 0 pairs` over the runtime transition pairs;

where `ts = m.pre :: steps.map pre` and `pairs = (m.pre, post) :: …` are exactly
`nativeExecutionViews`'s forest (`SourceSemantics.lean`).  `walk`, `uniq`, `akey`,
`bnd` need the query/receipt allocation layers and are left as the documented
extension point (see the `entries` function).

Without `<table>` the whole `{ "node": …, "val": …, "head": … }` object is printed;
with `<table>` only that array is printed (for the shell differential).
-/

open Lean ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3

deriving instance ToJson for ZkFormal.Near.NKid
deriving instance ToJson for ZkFormal.NearV3.NSlot3
deriving instance ToJson for ZkFormal.NearV3.NodeV3
deriving instance ToJson for ZkFormal.NearV3.NodeS3
deriving instance ToJson for ZkFormal.NearV3.ValE
deriving instance ToJson for ZkFormal.NearV3.HeadE
deriving instance ToJson for ZkFormal.NearV3.WStep3
deriving instance ToJson for ZkFormal.NearV3.WalkR
deriving instance ToJson for ZkFormal.NearV3.Render.UEnt
deriving instance ToJson for ZkFormal.NearV3.AkeyE
deriving instance ToJson for ZkFormal.NearV3.BndE

/-- The reference execution the extraction consumes: the main transition's
pre-state and result (from `applyNewChunk`) and every implicit `(pre, post)`.
This is `ZkFormal.V3.Tools.TestPrep.trace`, re-declared here (that module is an
exe and owns the name `main`). -/
structure XTr where
  tMain : PTrie
  out : MainOut
  impl : List (PTrie × PTrie)

/-- Re-run the accepted D0a execution (`checkD0a`'s own steps). -/
def xtrace (cb wb : Bytes) : Except String XTr := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceipts k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot (mainKeys receipts bshards)
  let out ← applyNewChunk prims ctxB2 tMain receipts
  let mut root := out.trie.hashOf
  let mut impl : List (PTrie × PTrie) := []
  for (M, T) in k.implicitBlks.zip w.implicit do
    let ctxM := blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    impl := impl ++ [(tM, tM')]
    root := tM'.hashOf
  pure ⟨tMain, out, impl⟩

/-- The runtime transition pairs `(pre, post)`: the main transition then every
implicit one, exactly `ZkFormal.NearV3.Assembly.runtimePairs`. -/
def runtimePairsOf (t : XTr) : List (PTrie × PTrie) :=
  (t.tMain, t.out.trie) :: t.impl

/-- The pre-state trees of the runtime pairs (what `forestNodes` allocates over). -/
def preTreesOf (t : XTr) : List PTrie := (runtimePairsOf t).map Prod.fst

/-- Per-table entry lists from an accepted D0a execution. -/
def entriesOf (t : XTr) : List (String × Json) :=
  let pairs := runtimePairsOf t
  let ts := preTreesOf t
  [ ("node", toJson (initializeList 0 (forestNodes 0 0 0 ts)))
  , ("val",  toJson (seedValuesFrom 0 (forestBytes ts)))
  , ("head", toJson (traceHeads 0 0 pairs)) ]

/-- Extract `case_dir` and print the requested table (or the whole object). -/
def runCase (table : Option String) (dir : String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => IO.eprintln s!"np-lean-entries-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
    match xtrace cb wb with
    | .error e => IO.eprintln s!"np-lean-entries-v3: {dir}: trace failed: {e}"; return 2
    | .ok t =>
      let es := entriesOf t
      match table with
      | none => IO.println (Json.compress (Json.mkObj es))
      | some name =>
        match es.find? (·.1 == name) with
        | some (_, j) => IO.println (Json.compress j)
        | none =>
          IO.eprintln s!"np-lean-entries-v3: no extraction for table '{name}' (have: node val head)"
          return 2
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => runCase none dir
  | [dir, table] => runCase (some table) dir
  | _ => IO.eprintln "usage: np-lean-entries-v3 <case_dir> [<table>]"; return 2
