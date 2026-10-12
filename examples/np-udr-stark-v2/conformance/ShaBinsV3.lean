import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.TrieShaEmpty
import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Assembly.TrieNative
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Assembly.SchedulerSanityJobs
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
import ZkFormal.NearV3.Assembly.UpsertShaCapacity
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Assembly.RcptSourceRcOutputs
import ZkFormal.NearV3.Assembly.SourceShaMessages
import ZkFormal.NearV3.Rcpt.Candidates.AccountShaJobs
import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocation
import ZkFormal.NearV3.Candidates.MerkleRender.NativeRoot
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-shabins-v3 <case_dir>` — the honest SHA job bins of `nearAirV3` tables 0/1
(`sha_t`, `sha_r`) for a real D0a fixture, the ground truth of `npudr v3sha`.

Reads `case_dir/claim.bin` / `witness.bin`, requires `checkD0a B0 cb wb = .ok ()`, re-runs the
native execution (`AcceptedV3`'s objects: `k`, `w`, `m`, `steps`, `p = prepD0 cb (nativeHint k w m)`)
and evaluates the four SHA job families of `TrieSide.trie_side_exact` /
`RcptTrieSide.rcpt_trie_side` and their two bins
`TrieShaTwo.twoShaJobBins weight scheduler native receipt source = [b0, b1]`
(`b0 = native ++ src₀`, `b1 = scheduler ++ receipt ++ src₁`, `splitJobs` over whole source jobs
with capacity `2^22 − rows(native)`):

* **scheduler** `schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us`, `us` the native scheduler
  calls in order (`CallPin`): the main call on the rebased pre tree `oldPost` (`UpsA7`: the
  scheduler pre trees are `oldPost :: steps.pre`), then one per implicit step on `e.pre`, each
  `schedulerUpsertWitness ctx pre` (the executable extraction of `SchedulerUpsertCost`);
* **native** `jobsToSha (TrieShaEmpty.nativeShaJobsE ns es)` with
  `ns = TrieNative.nodes m steps oldPost writes q`, `es = TrieNative.vals m steps` (the job bytes do
  not depend on the use requests `q`; `q = ⟨[], [], []⟩` here);
* **receipt** `ReceiptGatedShaJobs.jobs pub ls accts (sourceDup lists)`
  = `rcJobs ++ jobsToSha (ReceiptDigestPartition.jobs pub ls ++ accountShaJobs accts ++
  merkleShaJobs leaves)`.  The receipt list view `ls` is an existential of the proof (a view of
  the patched receipt trace), so it is evaluated through its native identities (executable twin):
  `rcJobs` is `sourceRcShaJobs own lists entries` (RC preimage `u64 own ‖ encodeReceipts`, digest
  output gated by `!sourceDup`); receipt `r`'s `PEO`/`LEAF`/`RID` preimages are those of the
  `r`-th native outcome (`flatR ls` leaves `= outcomePreimages os`, `RcptV.peo =
  o.partialEncode`, refund iff `o.receiptIds ≠ []`, `RID = o.id ‖ u64 height ‖ 0⁸`);
  `accts = nativeAccountViews m.pre oldPost (appliedReceipts k w)` (`AcceptedV3.vslot_views`);
  `leaves = outcomePreimages m.result.outcomes`;
* **source** `sourceShaMessages p.lists w.entries` (= `AcceptedV3.srcShaAll`).

`oldPost`/`writes` (the account-write replay, `SizedAccountRun m.pre writes oldPost`, an
existential of the proof) are rebuilt here: one write per applied receipt at
`accountKeyPath receiverId` with the receiver's final account bytes, `oldPost` the pre tree with
these writes; the exe checks `oldPost.upsert keyBwState so.state` has the post-state root.

Output (stdout, one JSON object): `b0`, `b1`, the four families, `cap` (the split capacity),
and `entries` — the honest per-table entry lists the families are made of, for the Rust collector:
`node` (`TrieNative.nodes`, metadata of `q = ⟨[],[],[]⟩`), `val`, `acct`, `srcp`
(`DedupCompile.blocks`), `ups` (per call `{tau, v, parts: [{q}]}`, `q = nodeEnc` of the part
output) and `codec` (per call `{tau, present, prev_hash, ash}`, the 64-byte sanity input split
in halves).  Only the fields the SHA collector reads are dumped for `ups`/`codec`.
-/

open Lean ZkFormal.NearV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Rcpt.Candidates
  ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3

deriving instance ToJson for ZkFormal.Near.NKid
deriving instance ToJson for ZkFormal.NearV3.NSlot3
deriving instance ToJson for ZkFormal.NearV3.NodeV3
deriving instance ToJson for ZkFormal.NearV3.NodeS3
deriving instance ToJson for ZkFormal.NearV3.ValE
deriving instance ToJson for ZkFormal.Near.AcctV
deriving instance ToJson for ZkFormal.NearV3.SrcpItem
deriving instance ToJson for ZkFormal.NearV3.SrcpB
deriving instance ToJson for ZkFormal.Sha.Gen.Msg

/-- The native objects of an accepted witness (computable twin of `AcceptedV3`'s data plus the
account-write replay and the scheduler calls). -/
structure ShaNative where
  k : WalkD0
  w : StateWitness
  m : MainExecutionV3
  steps : List ImplicitStepV3
  p : Prep
  writes : List (List Nat × Bytes)
  oldPost : PTrie
  us : List SchedulerUpsertWitness

def nativeOf (cb wb : Bytes) : Except String ShaNative := do
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
  -- the account-write replay: one write per applied receipt, final account bytes
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

def ShaNative.pub (N : ShaNative) : List ZkFormal.Algebra.Fp :=
  ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes N.p 0)

def ShaNative.nodes (N : ShaNative) : List NodeS3 :=
  TrieNative.nodes N.m N.steps N.oldPost N.writes ⟨[], [], []⟩

def ShaNative.vals (N : ShaNative) : List ValE := TrieNative.vals N.m N.steps

def ShaNative.accts (N : ShaNative) : List ZkFormal.Near.AcctV :=
  (nativeAccountViews N.m.pre N.oldPost (appliedReceipts N.k N.w)).getD []

def toN (b : Bytes) : List Nat := b.map UInt8.toNat

/-- `ReceiptDigestPartition.jobs pub ls` through the outcomes (see the module doc). -/
def receiptOutcomeJobs (pub : List ZkFormal.Algebra.Fp) (os : List Outcome) : List ZkFormal.Near.Render.Msg :=
  os.zipIdx.flatMap fun (o, r) =>
    [⟨ZkFormal.Near.msgId ZkFormal.Near.K_PEO r, toN o.partialEncode⟩,
     ⟨ZkFormal.Near.msgId ZkFormal.Near.K_LEAF r, toN (u32 2 ++ o.id ++ sha256 o.partialEncode)⟩] ++
    (if o.receiptIds ≠ [] then
      [⟨ZkFormal.Near.msgId ZkFormal.Near.K_RID r,
        toN o.id ++ ZkFormal.Near.pubBytes pub ZkFormal.NearV3.PH_HEIGHT 8 ++ List.replicate 8 0⟩]
     else [])

structure Families where
  scheduler : List ZkFormal.Sha.Gen.Msg
  native : List ZkFormal.Sha.Gen.Msg
  receipt : List ZkFormal.Sha.Gen.Msg
  source : List ZkFormal.Sha.Gen.Msg

def families (N : ShaNative) : Families :=
  let os := N.m.result.outcomes
  { scheduler := schedulerShaJobs 0 N.us ++ schedulerSanityJobs 0 N.us
    native := jobsToSha (TrieShaEmpty.nativeShaJobsE N.nodes N.vals)
    receipt := RcptSkeleton.sourceRcShaJobs N.k.H.shardId N.p.lists N.w.entries ++
      jobsToSha (receiptOutcomeJobs N.pub os ++ accountShaJobs N.accts ++
        merkleShaJobs (ZkFormal.NearV3.Candidates.MerkleRender.outcomePreimages os))
    source := sourceShaMessages N.p.lists N.w.entries }

def shaWeight (m : ZkFormal.Sha.Gen.Msg) : Nat := (ZkFormal.Sha.Gen.msgRows m).length

def jnats (xs : List Nat) : Json := Json.arr (xs.map (fun x => toJson x)).toArray

def upsLite (N : ShaNative) : Json :=
  Json.arr (N.us.zipIdx.map fun (u, tau) => Json.mkObj
    [ ("tau", toJson tau), ("v", jnats (toN u.value))
    , ("parts", Json.arr (u.run.parts.map fun pt =>
        Json.mkObj [("q", jnats (toN (ZkFormal.NearV3.nodeEnc pt.output)))]).toArray) ]).toArray

def codecLite (N : ShaNative) : Json :=
  Json.arr (N.us.zipIdx.map fun (u, tau) =>
    let s := toN ((schedulerWitnessSanity u).getD [])
    Json.mkObj [ ("tau", toJson tau), ("present", toJson true)
      , ("prev_hash", jnats (s.take 32)), ("ash", jnats (s.drop 32)) ]).toArray

def runCase (dir : String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e => IO.eprintln s!"np-lean-shabins-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
    match nativeOf cb wb with
    | .error e => IO.eprintln s!"np-lean-shabins-v3: {dir}: native trace failed: {e}"; return 2
    | .ok N =>
      let F := families N
      let bins := TrieShaTwo.twoShaJobBins shaWeight F.scheduler F.native F.receipt F.source
      let cap := 2 ^ 22 - (F.native.map shaWeight).sum
      let ents := Json.mkObj
        [ ("node", toJson N.nodes), ("val", toJson N.vals), ("acct", toJson N.accts)
        , ("srcp", toJson (DedupCompile.blocks N.p.lists N.w.entries))
        , ("ups", upsLite N), ("codec", codecLite N) ]
      IO.println (Json.compress (Json.mkObj
        [ ("b0", toJson (bins.getD 0 [])), ("b1", toJson (bins.getD 1 []))
        , ("scheduler", toJson F.scheduler), ("native", toJson F.native)
        , ("receipt", toJson F.receipt), ("source", toJson F.source)
        , ("cap", toJson cap), ("entries", ents) ]))
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => runCase dir
  | _ => IO.eprintln "usage: np-lean-shabins-v3 <case_dir>"; return 2
