import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.TrieNative
import ZkFormal.NearV3.Assembly.TrieUpsNative
import ZkFormal.NearV3.Assembly.TrieUniqDup
import ZkFormal.NearV3.Assembly.TrieA7Ups
import ZkFormal.NearV3.Assembly.TrieA7Val
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Assembly.SchedulerPriorValueId
import ZkFormal.NearV3.Assembly.ForestAddress
import ZkFormal.NearV3.Assembly.PathRecordId
import ZkFormal.NearV3.Assembly.ExtendedAddresses
import ZkFormal.NearV3.Assembly.SourceAddresses
import ZkFormal.NearV3.Assembly.RootedUpsert
import ZkFormal.NearV3.Render.Ups.NativePartEncoding
import ZkFormal.NearV3.Render.Ups.NativeChildLengths
import ZkFormal.NearV3.Render.Ups.NativeWalkConstruction
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts
import ZkFormal.NearV3.Candidates.PhysicalWindowRequests
import ZkFormal.NearV3.Candidates.NativeQueueIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryBounds
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryList
import ZkFormal.NearV3.Rcpt.Candidates.WalkRanks
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Render.HonestBalanceRcpt
import ZkFormal.NearV3.Rcpt.Extract.SizeProof
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Lean.Data.Json
import Std.Data.HashSet
import Conformance.FastTrie

/-!
`np-lean-trie-v3 <case_dir>` — the **honest trie-side entries** of `nearAirV3` (tables 2 node,
3 head, 4 val, 5 walk, 6 uniq, 7 ups, 21 size, with the A7 inputs of nodeA7/valA7/upsA7/sizeA7)
for a real D0a fixture: the ground truth for the Rust derivation (`npudr v3trie`) and the
first source of honest `upsV3` instances.

The entry lists are those of `Assembly/TrieSide.lean` `trie_side_exact`, evaluated on the native
objects of the accepted witness (`k w m steps p`, the account-write replay `writes`/`oldPost`
and the scheduler upserts `us`, built as in `ShaBinsV3.lean`'s `nativeOf`):

* **ups** `Js = TrieUpsNative.upsRanked ws insts`, where `insts[tau] = honestInst us tau us[tau]`
  is the construction inside `NativeReaderOrigin.scheduler_instance_origin_inputs` with
  `baseI := default`, `base := default` (as `TrieUpsKeys.coverage_kf` passes):
  `root = forestRootAt 0 0 (us.map pre) tau`, `recordId = pathRecordId (extendedAddresses …)`,
  `Qs` the `some` payload of `encodeNativeParts` (`forest_native_walk_exact`, total by
  `encodeNativeParts_total`), `a` the source address whose tree is `run.terminalSource`
  (unique by size, `sourceAddresses_decreasing`), `B = nativeWalkBase recordId (fun _ => a.vid)
  (occurrenceResolvedId recordId) {nativeRootBase default u.pre u.run with tau}`,
  `I = nativeInstance recordId B root.tree u.run u.value Qs`.  (The proof takes
  `Classical.choose` of the existential this construction proves; any witness of it is honest.)
* **walk** `rankWalks [] ws`, `ws = nativeQueryWalks pairs (allLookupQueries (appliedReceipts k w)
  m.pre v (steps.map pre) (NativeQueueIds.resolve m.pre v (steps.map pre)))`, `v` the unique
  `MainValues` read from `m.pre` (`TrieWalkAlign.mainValues_unique`).
* **node** `TrieNative.nodes m steps oldPost writes q` with
  `q = useReq ws insts (PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS)`;
  **head** `TrieNative.heads m steps oldPost writes q.edges`; **val** `TrieNative.vals m steps`;
  **uniq** `TrieUniqDup.uniqNative m steps`.
* **A7**: `S n = ([n] ∈ insts.flatMap upsRplMsgs)`, `SV n = ([n] ∈ insts.flatMap upsRplvMsgs)`
  (the witnesses of `TrieA7Perm.a7_perm_native` via `perm_of_singletons`); dumped as the
  per-entry `"rpl"` flags of node/val (`S` on node record index = list position).
* **size** `[{x0, x1, x2, ovh, yN}]`: `honestSizeV ns es A.sizeBlocks`, `ovhNat pub`, and
  `yN = [nodeA7Total ns S, valA7Total es SV, upsA7Total Js]`.

Output: one JSON object `{node, val, head, walk, uniq, ups, size, checks}`; `checks` reports
the self-checks (rpl/rplv message lists are duplicate-free singletons below the table sizes —
the `Perm` of `a7_perm_native`; the A7 total ≤ B0; instance count = scheduler calls).
-/

open Lean ZkFormal.NearV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Rcpt.Candidates
  ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Render ZkFormal.NearV3.Render.UpsGen
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
deriving instance ToJson for ZkFormal.NearV3.Render.UpsPartI
deriving instance ToJson for ZkFormal.NearV3.Render.UpsInst

/-- The native objects of an accepted witness (as `ShaBinsV3.nativeOf`). -/
structure TrieNat where
  k : WalkD0
  w : StateWitness
  m : MainExecutionV3
  steps : List ImplicitStepV3
  p : Prep
  writes : List (List Nat × Bytes)
  oldPost : PTrie
  us : List SchedulerUpsertWitness

def nativeOf (cb wb : Bytes) : Except String TrieNat := do
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
  let writes := receipts.map fun r =>
    let key := accountKeyPath r.receiverId
    (key, (out.trie.get key).getD [])
  let oldPost ← writes.foldlM (fun (t : PTrie) (kb : List Nat × Bytes) =>
    match t.set kb.1 kb.2 with
    | some t' => (pure t' : Except String PTrie)
    | none => throw "account replay: set failed") tMain
  let (_, so) ← schedStep prims (m.ctx k) tMain
  match oldPost.upsert keyBwState so.state with
  | some t => if t.hashOf == out.trie.hashOf then pure () else throw "account replay: post root mismatch"
  | none => throw "account replay: scheduler upsert failed"
  let u0 ← schedulerUpsertWitness (m.ctx k) oldPost
  let us ← steps.mapM fun e => schedulerUpsertWitness (implicitCtx k e) e.pre
  pure ⟨k, w, m, steps, p, writes, oldPost, u0 :: us⟩

def TrieNat.pub (N : TrieNat) : List ZkFormal.Algebra.Fp :=
  ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes N.p 0)

/-- The unique `MainValues` with `Valid ∧ Reads m.pre m.pre m.pre` (`mainValues_unique`). -/
def mainValuesOf (m : MainExecutionV3) : Except String Qv.MainValues := do
  let rd (key : List Nat) (what : String) : Except String (Option Bytes) :=
    match m.pre.find key with | some v => pure v | none => throw s!"main values: {what} unread"
  let d ← rd keyDelayedIdx "delayed"
  let b ← rd keyBufferedIdx "buffered"
  let y ← rd keyYieldIdx "yield"
  pure ⟨d, b, m.bufferedShards, y⟩

/-- The honest native ups instance of scheduler call `tau` (construction of
`scheduler_instance_origin_inputs`, `baseI := default`, `base := default`). -/
def honestInst (us : List SchedulerUpsertWitness) (tau : Nat) (u : SchedulerUpsertWitness) :
    Except String UpsInst := do
  let root ← match forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau with
    | some r => pure r | none => throw s!"ups {tau}: no forest root"
  let rid := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let Qs ← match encodeNativeParts rid root.tree u.run (nativeSourceBase rid u.run (fun _ => default)) with
    | some q => pure q | none => throw s!"ups {tau}: encodeNativeParts failed"
  let ts := tsize u.run.terminalSource
  let a ← match (sourceAddresses root.nid root.vid root.depth root.tree [0,15]).find?
      (fun b => tsize b.tree == ts) with
    | some a => pure a | none => throw s!"ups {tau}: terminal source address not found"
  let B := nativeWalkBase rid (fun _ => a.vid) (occurrenceResolvedId rid)
    {nativeRootBase default u.pre u.run with tau := tau} root.tree u.run u.value
  pure (nativeInstance rid B root.tree u.run u.value Qs)

def honestInsts (us : List SchedulerUpsertWitness) : Except String (List UpsInst) :=
  us.zipIdx.mapM fun (u, tau) => honestInst us tau u

/-- Lookup set of the singleton messages `[n]` of a message list. -/
def singletons (L : List ZkFormal.Near.Msg) : Std.HashSet Nat :=
  L.foldl (fun s msg => match msg with | [n] => s.insert n | _ => s) {}

/-- `nodeA7Total` / `valA7Total` in one pass (same sums; `getD` hoisted). -/
def nodeTot (ns : List NodeS3) (S : Nat → Bool) : Nat :=
  (ns.zipIdx.map fun (s, n) => (if S n then 1 else 2) * (s.v.ser false).length).sum

def valTot (es : List ValE) (S : Nat → Bool) : Nat :=
  (es.zipIdx.map fun (e, t) => (if S t then 1 else 2) * e.len).sum

theorem nodeTot_eq (ns : List NodeS3) (S : Nat → Bool) : nodeTot ns S = TrieA7.nodeA7Total ns S := by
  unfold nodeTot TrieA7.nodeA7Total
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < ns.length := by simpa using h1
  simp [NodeGen3.rec, List.getElem?_eq_getElem hi]

theorem valTot_eq (es : List ValE) (S : Nat → Bool) : valTot es S = TrieA7.valA7Total es S := by
  unfold valTot TrieA7.valA7Total
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < es.length := by simpa using h1
  simp [ValGen.ent, List.getElem?_eq_getElem hi]

def withRpl {α : Type} [ToJson α] (xs : List α) (S : Nat → Bool) : Json :=
  Json.arr (xs.zipIdx.map fun (x, i) => (toJson x).setObjVal! "rpl" (Json.bool (S i))).toArray

structure TrieOut where
  json : Json
  checks : List (String × Bool)

def stage (t0 : Nat) (n : String) : IO Nat := do
  let t ← IO.monoMsNow
  if (← IO.getEnv "TRIE_TIMING").isSome then IO.eprintln s!"  [{t - t0} ms] {n}"
  return t

def liftE {α : Type} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)

def trieEntries (N : TrieNat) : IO TrieOut := do
  let t ← IO.monoMsNow
  let v ← liftE (mainValuesOf N.m)
  let pres := N.steps.map ImplicitStepV3.pre
  let pairs := (N.m.pre, N.m.result.trie) :: N.steps.map (fun s => (s.pre, s.post))
  let qs := allLookupQueries (appliedReceipts N.k N.w) N.m.pre v pres
    (Candidates.NativeQueueIds.resolve N.m.pre v pres)
  let ws ← match nativeQueryWalks pairs qs with
    | some ws => pure ws | none => throw (IO.userError "nativeQueryWalks failed")
  let t ← stage t s!"walks ({ws.length})"
  let insts ← liftE (honestInsts N.us)
  let t ← stage t s!"insts ({insts.length})"
  let Js := TrieUpsNative.upsRanked ws insts
  let t ← stage t "ranked"
  -- `upsTraceFast Js = upsTraceAligned Js` (`Conformance.FastTrie.upsTraceFast_eq`)
  let W := Candidates.PhysicalWindowRequests.keys (Conformance.FastTrie.upsTraceFast Js) Assembly.T_UPS
  let t ← stage t s!"window keys ({W.length})"
  let q := TrieUpsNative.useReq ws insts W
  let ns := TrieNative.nodes N.m N.steps N.oldPost N.writes q
  let t ← stage t s!"nodes ({ns.length})"
  let es := TrieNative.vals N.m N.steps
  let t ← stage t s!"vals ({es.length})"
  let hs := TrieNative.heads N.m N.steps N.oldPost N.writes q.edges
  let t ← stage t s!"heads ({hs.length})"
  let L := TrieUniqDup.uniqNative N.m N.steps
  let t ← stage t s!"uniq ({L.length})"
  let walk := rankWalks [] ws
  let t ← stage t s!"rankWalks ({walk.length})"
  let rplL := insts.flatMap TrieA7.upsRplMsgs
  let rplvL := insts.flatMap TrieA7.upsRplvMsgs
  let sS := singletons rplL
  let sV := singletons rplvL
  let S : Nat → Bool := fun n => sS.contains n
  let SV : Nat → Bool := fun n => sV.contains n
  let y0 := nodeTot ns S
  let y1 := valTot es SV
  let y2 := TrieA7.upsA7Total Js
  let t ← stage t "A7 totals"
  let pub := N.pub
  let A_dd := DedupCompile.blocks N.p.lists N.w.entries
  let sizeBlocks := A_dd.map fun B => if B.dup then { B with path := [] } else B
  let sv := honestSizeV ns es sizeBlocks
  let size := Json.arr #[Json.mkObj [("x0", toJson sv.x0), ("x1", toJson sv.x1), ("x2", toJson sv.x2),
    ("ovh", toJson (ovhNat pub)), ("yN", toJson [y0, y1, y2])]]
  let _ ← stage t "size"
  let single (L : List ZkFormal.Near.Msg) (n : Nat) : Bool :=
    L.all (fun m => match m with | [x] => decide (x < n) | _ => false)
  let checks :=
    [ ("insts = scheduler calls", insts.length == N.us.length)
    , ("rpl msgs: distinct singletons < |node|", single rplL ns.length && sS.size == rplL.length)
    , ("rplv msgs: distinct singletons < |val|", single rplvL es.length && sV.size == rplvL.length)
    , ("A7 total ≤ B0", decide (y0 + y1 + y2 ≤ 2000000))
    , ("base size ≤ B0", decide (sv.x0 + sv.x1 ≤ 2000000)) ]
  pure ⟨Json.mkObj
    [ ("node", withRpl ns S), ("val", withRpl es SV), ("head", toJson hs), ("walk", toJson walk)
    , ("uniq", toJson L), ("ups", toJson Js), ("size", size)
    , ("checks", Json.mkObj (checks.map fun (n, b) => (n, Json.bool b))) ], checks⟩

def runCase (dir : String) (table : Option String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => IO.eprintln s!"np-lean-trie-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
    let t0 ← IO.monoMsNow
    match nativeOf cb wb with
    | .error e => IO.eprintln s!"np-lean-trie-v3: {dir}: {e}"; return 2
    | .ok N =>
      let _ ← stage t0 "native execution"
      let o ← trieEntries N
      for (n, b) in o.checks do
        unless b do IO.eprintln s!"np-lean-trie-v3: {dir}: self-check failed: {n}"
      match table with
      | none => IO.println o.json.compress
      | some t =>
        match o.json.getObjVal? t with
        | .ok j => IO.println j.compress
        | .error _ => IO.eprintln s!"np-lean-trie-v3: no table {t}"; return 2
      return (if o.checks.all (·.2) then 0 else 3)

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => runCase dir none
  | [dir, t] => runCase dir (some t)
  | _ => IO.eprintln "usage: np-lean-trie-v3 <case_dir> [<table>]"; return 2
