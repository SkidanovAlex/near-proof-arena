import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Render.HonestRcptQ
import ZkFormal.NearV3.Assembly.RenderV3RcptAccepted
import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Assembly.RcptSourceRcOutputs
import ZkFormal.NearV3.Rcpt.Candidates.AccountShaJobs
import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocation
import ZkFormal.NearV3.Candidates.MerkleRender.NativeRoot
import ZkFormal.NearV3.Candidates.NativeSortIds
import ZkFormal.NearV3.Render.PaddedMrk
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-rcptfam-v3 <case_dir> <out_dir> [<max_rows>]` — the honest entries of the
receipt-side tables of `nearAirV3` for a real D0a fixture, the ground truth of
`npudr v3rcptfam` (`src/v3/rcptfam.rs`).

Reads `case_dir/claim.bin` / `witness.bin`, requires `checkD0a B0 cb wb = .ok ()`, re-runs the
native execution (the objects of `AcceptedV3`, `Assembly/RenderV3RcptAccepted.lean`: walk `k`,
witness `w` with its raw bytes, main execution `m`, `p = prepD0 cb (nativeHint k w m)`) and
evaluates **the definitions of the accepted receipt-side renders** on them:

* `rcpt.json` / `rcpt.prefix.bin` (table 16): the honest receipt input `AcceptedV3.rcptInput`
  = `acceptedRcptInput cb raw k w m p (nativeAccountId m.pre lists)
  (NativeReceiptAccessIds.accessId m.pre) 0 [] (NativeAccessKeyRanks.rankAux m.pre rs 0) 0`
  with `lists = sourceInputLists (m.ctx k) p.lists w.entries`; its native trace
  `rcptTraceNative pub x` (`pub = pubOf (preparedBytes p 0)`); the list view
  `(nativeBlocks lists).map (ListBlock.view tN 0)` (`nativeRcptLists`) with each receipt's
  native routing interval and `own`/`height`/`bgp` (the Rust `RcptIn` JSON, as
  `np-lean-render-v3-rcpt`); and the first `planned + 8` rows of the installed render
  `patchTrace (counterPatch tN 0 (physicalBoundaryRank tN 0)) 0` (u32 LE `22, width, n`, then
  the rows).  Only when `planned rows ≤ max_rows` (default 4000): every cell walks the plan.
* `bnd.json` (table 19): `AcceptedV3.bnds = boundaryEntries (boundedIntervals k.L own)
  (physicalBoundaryKeys tN 0)` (only with the trace).
* `acct.json` (17): `nativeAccountViews m.pre oldPost rs` (the executable form of
  `AcceptedV3.accts`, as `np-lean-shabins-v3`; `oldPost` = the account-write replay, root-checked).
* `akey.json` (18): `AcceptedV3.akeys = NativeAccessKeyProviders.providers m.pre rs`.
* `srcp.json` (20): `AcceptedV3.ddBlocks = DedupCompile.blocks p.lists w.entries`, each block with
  its repetition bit `rep = sourceRepeated p.lists j` (`AcceptedV3.ddRep`).
* `mrk.json` (23): `{n, levels}` with `levels = mrkLevels m.result.outcomes`
  (`mrkRender_accepted`).
* `sort.json` (24): `NativeSortIds.sorted rs` (`sortRenderV3` over `A.rcptInput.lists`).
* `sha_receipt.json`: the receipt SHA job family `ReceiptGatedShaJobs.jobs` through the native
  outcome identities (as `np-lean-shabins-v3`).
* `summary.json`: counts and whether the trace parts were evaluated.
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3
open NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.NearV3.Assembly.RoutingQCandidate ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.NearV3.Candidates

deriving instance ToJson for ZkFormal.Near.AcctV
deriving instance ToJson for ZkFormal.NearV3.SrcpItem
deriving instance ToJson for ZkFormal.NearV3.SrcpB
deriving instance ToJson for ZkFormal.Sha.Gen.Msg
deriving instance ToJson for ZkFormal.NearV3.AkeyE
deriving instance ToJson for ZkFormal.NearV3.BndE
deriving instance ToJson for ZkFormal.Near.Render.MNode

namespace RcptFam

def W : Nat := RcptV3.width

/-- The native objects of an accepted witness used by the receipt side. -/
structure Native where
  k : WalkD0
  w : StateWitness
  raw : Bytes
  m : MainExecutionV3
  p : Prep
  oldPost : PTrie

def nativeOf (cb wb : Bytes) : Except String Native := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let (raw, _) ← decodeWitnessFile wb
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
  let p ← prepD0 cb (nativeHint k w m)
  -- the account-write replay (as `np-lean-shabins-v3`)
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
  pure ⟨k, w, raw, m, p, oldPost⟩

def Native.pub (N : Native) : List Fp :=
  ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes N.p 0)

def Native.lists (N : Native) : List (List Input) :=
  sourceInputLists (N.m.ctx N.k) N.p.lists N.w.entries

def Native.rs (N : Native) : List Receipt := N.lists.flatten.map Input.receipt

/-- `AcceptedV3.rcptInput`. -/
def Native.rcptInput (cb : Bytes) (N : Native) : RcptInput :=
  acceptedRcptInput cb N.raw N.k N.w N.m N.p (nativeAccountId N.m.pre N.lists)
    (NativeReceiptAccessIds.accessId N.m.pre) (fun _ _ => 0) (fun _ _ => [])
    (NativeAccessKeyRanks.rankAux N.m.pre N.rs (fun _ _ _ => 0)) (fun _ _ _ => 0)

/-! ## JSON -/

def jn (xs : List Nat) : Json := Json.arr (xs.map toJson).toArray
def jb (xs : Bytes) : Json := jn (xs.map UInt8.toNat)
def jbs (xs : List Bool) : Json := Json.arr (xs.map toJson).toArray
def toN (b : Bytes) : List Nat := b.map UInt8.toNat

def rcptJson (e : RcptE) (iv : Option Bytes × Option Bytes) : Json :=
  Json.mkObj [
    ("p", jn e.p), ("v", jn e.v), ("s", jn e.s), ("rid", jn e.rid), ("kt", toJson e.kt),
    ("pk", jn e.pk), ("gp", jn e.gp), ("dep", jn e.dep), ("hr", toJson e.hr), ("ge", toJson e.ge),
    ("kslot", toJson e.kslot), ("tprev", toJson e.tprev), ("bef", jn e.bef), ("lk", jn e.lk),
    ("st", jn e.st), ("aft", jn e.aft), ("burnt", jn e.burnt), ("ramt", jn e.ramt),
    ("rfid", jn e.rfid), ("peoh", jn e.peoh), ("sys", toJson e.sys), ("ee", toJson e.ee),
    ("gv", jbs e.gv), ("gs", jbs e.gs), ("sx", jn e.sx), ("akf", toJson e.akf),
    ("akk", toJson e.akk), ("aku", toJson e.aku), ("q", toJson e.q),
    ("rlk", Json.arr (e.rlk.map fun (pos, lo, hi, hn, u) =>
      Json.mkObj [("pos", toJson pos), ("lo", toJson lo), ("hi", toJson hi), ("hn", toJson hn),
        ("u", toJson u)]).toArray),
    ("iv", Json.mkObj [("lo", match iv.1 with | some b => jb b | none => Json.null),
      ("hi", match iv.2 with | some b => jb b | none => Json.null)])]

def srcpJson (B : SrcpB) (rep : Bool) : Json :=
  match toJson B with
  | .obj kvs => .obj (kvs.insert "rep" (toJson rep))
  | j => j

/-! ## The receipt SHA family (as `np-lean-shabins-v3`) -/

def receiptOutcomeJobs (pub : List Fp) (os : List Outcome) : List ZkFormal.Near.Render.Msg :=
  os.zipIdx.flatMap fun (o, r) =>
    [⟨ZkFormal.Near.msgId ZkFormal.Near.K_PEO r, toN o.partialEncode⟩,
     ⟨ZkFormal.Near.msgId ZkFormal.Near.K_LEAF r, toN (u32 2 ++ o.id ++ sha256 o.partialEncode)⟩] ++
    (if o.receiptIds ≠ [] then
      [⟨ZkFormal.Near.msgId ZkFormal.Near.K_RID r,
        toN o.id ++ ZkFormal.Near.pubBytes pub ZkFormal.NearV3.PH_HEIGHT 8 ++ List.replicate 8 0⟩]
     else [])

def Native.accts (N : Native) : List ZkFormal.Near.AcctV :=
  (nativeAccountViews N.m.pre N.oldPost (appliedReceipts N.k N.w)).getD []

def receiptFamily (N : Native) : List ZkFormal.Sha.Gen.Msg :=
  let os := N.m.result.outcomes
  RcptSkeleton.sourceRcShaJobs N.k.H.shardId N.p.lists N.w.entries ++
    jobsToSha (receiptOutcomeJobs N.pub os ++ accountShaJobs N.accts ++
      merkleShaJobs (ZkFormal.NearV3.Candidates.MerkleRender.outcomePreimages os))

/-! ## Trace materialisation (as `np-lean-render-v3-rcpt`) -/

def materialize (tr : Trace Fp) (n : Nat) : Array Fp := Id.run do
  let mut a : Array Fp := Array.mkEmpty (n * W)
  for r in [0:n] do
    for col in [0:W] do
      a := a.push (tr.cell 0 r col)
  return a

def ofArray (a : Array Fp) (n : Nat) : Trace Fp :=
  ⟨fun _ => 22, fun _ r col => if r < n ∧ col < W then a.getD (r * W + col) 0 else 0⟩

def u32b (b : ByteArray) (x : Nat) : ByteArray :=
  b.push (x % 256).toUInt8 |>.push (x / 256 % 256).toUInt8
    |>.push (x / 65536 % 256).toUInt8 |>.push (x / 16777216 % 256).toUInt8

def writeJson (path : String) (j : Json) : IO Unit := IO.FS.writeFile path j.compress

def runCase (dir out : String) (maxRows : Nat) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => IO.eprintln s!"np-lean-rcptfam-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
  match nativeOf cb wb with
  | .error e => IO.eprintln s!"np-lean-rcptfam-v3: {dir}: native run failed: {e}"; return 2
  | .ok N =>
  IO.FS.createDirAll out
  let pub := N.pub
  let lists := N.lists
  let rs := N.rs
  let own := N.k.H.shardId
  -- tables 17, 18, 20, 23, 24 and the receipt SHA family
  writeJson (out ++ "/acct.json") (toJson N.accts)
  writeJson (out ++ "/akey.json") (toJson (NativeAccessKeyProviders.providers N.m.pre rs))
  let bs := DedupCompile.blocks N.p.lists N.w.entries
  writeJson (out ++ "/srcp.json") (Json.arr (bs.zipIdx.map fun (B, j) =>
    srcpJson B (sourceRepeated N.p.lists j)).toArray)
  let os := N.m.result.outcomes
  writeJson (out ++ "/mrk.json") (Json.mkObj [("n", toJson os.length),
    ("levels", toJson (ZkFormal.NearV3.Render.mrkLevels os))])
  writeJson (out ++ "/sort.json") (toJson (NativeSortIds.sorted rs))
  writeJson (out ++ "/sha_receipt.json") (toJson (receiptFamily N))
  -- table 16 (and 19, which counts the receipt table's physical boundary keys)
  let rows := (plannedRows lists).length
  let traced : Bool := decide (rows ≤ maxRows)
  if traced then
    let x := N.rcptInput cb
    let n := rows + 8
    let a := materialize (rcptTraceNative pub x) n
    for r in [rows:n] do
      for col in [0:W] do
        if (a.getD (r * W + col) 0).toNat != 0 then
          IO.eprintln s!"np-lean-rcptfam-v3: native padding row {r} col {col} is nonzero"
          return 1
    let tM := ofArray a n
    let tQ := patchTrace (counterPatch tM 0 (physicalBoundaryRank tM 0)) 0
    let mut b := u32b (u32b (u32b ByteArray.empty 22) W) n
    for r in [0:n] do
      for col in [0:W] do
        b := u32b b (tQ.cell 0 r col).toNat
    IO.FS.writeBinFile (out ++ "/rcpt.prefix.bin") b
    let views := (nativeBlocks lists).map (RcptV3Proof.ListBlock.view tM 0)
    let ivs := rs.map fun r =>
      (boundedIntervals N.k.L own).getD (nativeRoutingIndex N.k r) (none, none)
    let mut k := 0
    let mut ls : Array Json := #[]
    for v in views do
      let mut js : Array Json := #[]
      for e in v.rs do
        js := js.push (rcptJson e (ivs.getD k (none, none)))
        k := k + 1
      ls := ls.push (Json.mkObj [("n0", toJson v.n0), ("n1", toJson v.n1), ("rs", Json.arr js)])
    let ctx := N.m.ctx N.k
    writeJson (out ++ "/rcpt.json") (Json.mkObj [("lists", Json.arr ls), ("own", toJson own),
      ("height", toJson ctx.height), ("bgp", toJson ctx.gasPrice)])
    -- rows `≥ n` of `tM` are zero (`gBd = 0`), so the keys of the first `n` rows are all of them
    let keys := (List.range n).filterMap fun r =>
      if tM.cell 0 r RcptV3.gBd = 1 then some (physicalBoundaryKey tM 0 r) else none
    writeJson (out ++ "/bnd.json") (toJson (boundaryEntries (boundedIntervals N.k.L own) keys))
  writeJson (out ++ "/summary.json") (Json.mkObj [("receipts", toJson rs.length),
    ("lists", toJson lists.length), ("rows", toJson rows), ("traced", toJson traced),
    ("accts", toJson N.accts.length), ("outcomes", toJson os.length)])
  IO.println s!"{dir}: {rs.length} receipts in {lists.length} lists, {rows} planned rows, traced {traced}"
  return 0

end RcptFam

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, out] => RcptFam.runCase dir out 4000
  | [dir, out, m] => RcptFam.runCase dir out m.toNat!
  | _ => IO.eprintln "usage: np-lean-rcptfam-v3 <case_dir> <out_dir> [<max_rows>]"; return 2
