import ZkFormal.NearV3.Candidates.NativeExecutionPost
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedReplayHead
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedRebasedOrigins
import ZkFormal.NearV3.Assembly.RenderV3Trie
import ZkFormal.NearV3.Assembly.UniqNative

/-!
# ZkFormal.NearV3.Assembly.TrieNative — honest native entries of the trie tables

The honest entry lists of `nodeV3`, `valV3`, `headV3` and `uniqV3` as definite functions of
the native objects of an accepted witness:

* the pre forest `forest m steps = m.pre :: steps.pre` (`checkD0a_native_trace`);
* the old-record replay `nativeReplayForest m steps oldPost writes` (`SizedAccountRun`);
* the use requests `q` (EDGE / BMAP / UPB uses of the node records), the head EDGE keys
  `keys` and the `uniq` tie-break `rk` — bookkeeping inputs fixed by the bus balances, free
  here (only their lengths matter for the honest-input conditions).

| table | entries | honest-input condition (from acceptance) |
|---|---|---|
| node | `nodes m steps oldPost writes q` | `NodeOk` (`accepted_ok`) |
| val | `vals m steps` | `ValOk` (`accepted_ok`) |
| head | `heads m steps oldPost writes keys` | `HeadOk` (`accepted_ok`) |
| uniq | `uniqs rk m steps oldPost writes q keys` | `DigsBal` with node/head (`uniqs_digsBal`) |

`accepted_native` gives the native objects of an accepted witness (`walkD0`, `decodeW`,
`checkD0a_native_trace`, the account-write replay `SizedAccountRun` and the scheduler upsert
inventory), so `accepted_bundle_parts` yields the four `TableRenderV3` components of tables
2, 3, 4 (and the uniq `DIGS` balance) for every accepted witness.
-/

namespace ZkFormal.NearV3.Assembly.TrieNative

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Near ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

/-- The native pre forest (main pre trie and the implicit pre tries). -/
def forest (m : MainExecutionV3) (steps : List ImplicitStepV3) : List PTrie :=
  m.pre :: steps.map ImplicitStepV3.pre

/-- The seeded node records of the pre forest (DFS occurrence order). -/
def seedNodes (m : MainExecutionV3) (steps : List ImplicitStepV3) : List NodeS3 :=
  initializeList 0 (forestNodes 0 0 0 (forest m steps))

/-- The seeded value records of the pre forest. -/
def seedVals (m : MainExecutionV3) (steps : List ImplicitStepV3) : List ValE :=
  seedValuesFrom 0 (forestBytes (forest m steps))

/-- The duplicate chain (`DUP`/`ENT` metadata) of the store occurrences, by content class. -/
def chain (m : MainExecutionV3) (steps : List ImplicitStepV3) : List StoreDuplicateChain.Entry :=
  StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences (seedNodes m steps)
    (NativeStoreProvenance.valueTau (forest m steps)) (seedVals m steps))

/-- **Honest `nodeV3` records.** -/
def nodes (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) : List NodeS3 :=
  assignList q 0 (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
    (ChainMetadata.assign (chain m steps) 0 (seedNodes m steps)))

/-- **Honest `valV3` records.** -/
def vals (m : MainExecutionV3) (steps : List ImplicitStepV3) : List ValE :=
  ChainMetadata.assignValues (chain m steps) (seedVals m steps)

/-- **Honest `headV3` entries** (one per replayed tree). -/
def heads (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (keys : List ZkFormal.Near.Msg) : List HeadE :=
  assignHeadUses keys (forestWalkHeads 0 0
    ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post))))

/-- **Honest `uniqV3` entries**: the node and head `DIGS` windows, sorted. -/
def uniqs (rk : Nat → Nat) (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg) : List UEnt :=
  UniqNative.uniqOf rk (nodes m steps oldPost writes q) (heads m steps oldPost writes keys)

/-- **The honest-input conditions of node, val and head from acceptance.** -/
theorem accepted_ok {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat × Bytes)} (hr : SizedAccountRun m.pre writes oldPost)
    (q : UseRequests) (he : q.edges.length < Algebra.P) (hb : q.bmaps.length < Algebra.P)
    (hu : q.windows.length < Algebra.P) (keys : List ZkFormal.Near.Msg) (hkeys : keys.length < Algebra.P) :
    NodeOk (nodes m steps oldPost writes q) ∧ ValOk (vals m steps) ∧
      HeadOk (heads m steps oldPost writes keys) := by
  obtain ⟨hn, hval⟩ := NativeExecutionPost.assigned_inputs hk hw h (by decide) hm hv
    (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu
  exact ⟨hn, ⟨hval⟩, (accepted_replay_head hk hw h hm hv hr keys hkeys 0 []).1⟩

/-- **`DIGS` balance** of the honest node, head and uniq entries (no hypothesis). -/
theorem uniqs_digsBal (rk : Nat → Nat) (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg) :
    Link3.DigsBal (nodes m steps oldPost writes q) (heads m steps oldPost writes keys)
      (uniqEntries (uniqs rk m steps oldPost writes q keys)) :=
  UniqNative.uniqOf_digsBal rk _ _

/-- **The native objects of an accepted witness**: the decoded walk and witness, the native
main execution and implicit trace, and the account-write replay. -/
theorem accepted_native {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) :
    ∃ (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) (steps : List ImplicitStepV3)
      (last : Bytes) (writes : List (List Nat × Bytes)) (oldPost : PTrie),
      walkD0 cb = .ok k ∧ decodeW wb = .ok w ∧ m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      SizedAccountRun m.pre writes oldPost := by
  have ha := ((relD0a_iff B0 cb wb).mpr h)
  have ha2 := ha.2.2.1
  unfold a2 at ha2
  cases hk : walkD0 cb with
  | error err => simp only [hk, Bool.false_eq_true] at ha2
  | ok k =>
  cases hw : decodeW wb with
  | error err => simp only [hk, hw, Bool.false_eq_true] at ha2
  | ok w =>
  obtain ⟨m, steps, last, hm, _, hv, -⟩ := checkD0a_native_trace hk hw h
  obtain ⟨writes, oldPost, -, -, hr, -⟩ :=
    accepted_rebased_origin_instances hk hw h hm hv (fun _ => default) (fun _ _ => default)
  exact ⟨k, w, m, steps, last, writes, oldPost, rfl, rfl, hm, hv, hr⟩

/-- **The node, head and value bundle components of every accepted witness** (any public
vector, any use requests and head keys of field-bounded length). -/
theorem accepted_bundle_parts {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) (pub : List Algebra.Fp) :
    ∃ (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) (steps : List ImplicitStepV3)
      (last : Bytes) (writes : List (List Nat × Bytes)) (oldPost : PTrie),
      walkD0 cb = .ok k ∧ decodeW wb = .ok w ∧ m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      SizedAccountRun m.pre writes oldPost ∧
      ∀ (q : UseRequests), q.edges.length < Algebra.P → q.bmaps.length < Algebra.P →
        q.windows.length < Algebra.P → ∀ (keys : List ZkFormal.Near.Msg), keys.length < Algebra.P →
        ∃ (hn : NodeOk (nodes m steps oldPost writes q)) (hv : ValOk (vals m steps))
          (Rh : TableRenderV3 pub T_HEAD (by decide)),
          (∀ sel, ExtOf (nodeRenderV3 pub _ hn sel).tf (nodeTraffic3 (nodes m steps oldPost writes q))) ∧
          Rh.tf = headTraffic (heads m steps oldPost writes keys) ∧
          (∀ sel, ExtOf (valRenderV3 pub _ hv sel).tf (valTraffic (vals m steps))) := by
  obtain ⟨k, w, m, steps, last, writes, oldPost, hk, hw, hm, hv, hr⟩ := accepted_native h
  refine ⟨k, w, m, steps, last, writes, oldPost, hk, hw, hm, hv, hr, ?_⟩
  intro q he hb hu keys hkeys
  obtain ⟨hn, hval, hh⟩ := accepted_ok hk hw h hm hv hr q he hb hu keys hkeys
  exact ⟨hn, hval, headRenderTrie pub _ hh, nodeRenderV3_ext pub _ hn, rfl, valRenderV3_ext pub _ hval⟩

end ZkFormal.NearV3.Assembly.TrieNative
