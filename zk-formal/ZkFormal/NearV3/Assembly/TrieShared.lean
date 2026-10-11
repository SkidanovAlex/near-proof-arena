import ZkFormal.NearV3.Assembly.TrieUpsRoot
import ZkFormal.NearV3.Candidates.NativeAccountSlotBalance

/-!
# ZkFormal.NearV3.Assembly.TrieShared — trie side of the shared buses

* **`VSLOT`** (node receives `[vid]` for every written value window; `acct` sends `[a.k]` per
  account): `vslot_records` (the record conservation from the account-digest permutation),
  `vslot_accepted` (that permutation for the honest node records and the native account views
  `nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as`, given the account-write
  keys and the final scheduler upsert of the SAME replay), `balancedAt_vslot` (bundle level:
  node (2) and acct (17) components).
* **`VBYTES`** (value records receive `[vid, p, byte]`): `vals_vbytes` — the honest value
  table receives exactly the bytes of every pre-forest value occurrence at its id; the senders
  (codec 11, acct 17, akey 18, qv 22) must send this multiset.
* **`SIZE`** tags 0, 1: `nodes_size`, `vals_size` — the node table sends `[0, Σ len]` over
  non-duplicate records, the value table `[1, Σ len]` over non-empty non-duplicate values.
* **`KEYNIB`/`FINAL`** — the walk component's traffic is `walkTraffic3 (rankWalks [] ws)`
  (`walkRecvs3 … B_KEYNIB`, `walkSends3 … B_FINAL`); the receipt/qv side must match it.
-/

namespace ZkFormal.NearV3.Assembly.TrieShared

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

/-- **`VSLOT` record conservation** from the account-digest permutation. -/
theorem vslot_records (as : List AcctV) (ns : List NodeS3)
    (hp : ((accountShaJobs as).map Render.digestMsg).Perm (ns.flatMap postSlotDigests)) (m : List Fp) :
    cnt (acctV3Sends as B_VSLOT) m = cnt (nodeRecvs3 ns B_VSLOT) m := by
  unfold cnt
  rw [← NativeAccountSlotBalance.account_slots, ← NativeAccountSlotBalance.node_slots]
  exact ((hp.map _).map Msg.toFp).count_eq m

/-- **`VSLOT` permutation for the honest node records and native account views.** -/
theorem vslot_accepted {k : WalkD0} {w : StateWitness} {m : MainExecutionV3} (hm : m.NativeValid k w)
    {writes : List (List Nat × Bytes)} {oldPost : PTrie} (hr : SizedAccountRun m.pre writes oldPost)
    (hkeys : writes.map Prod.fst = (appliedReceipts k w).map (fun r => accountKeyPath r.receiverId))
    {state : Bytes} (hup : oldPost.upsert keyBwState state = some m.result.trie)
    {as : List AcctV} (has : nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as)
    (steps : List ImplicitStepV3) (q : UseRequests) :
    ((accountShaJobs as).map Render.digestMsg).Perm
      ((TrieNative.nodes m steps oldPost writes q).flatMap postSlotDigests) :=
  native_main_account_digest_balance hm hr hkeys hup has steps q (TrieNative.chain m steps)

/-- The honest value table receives the bytes of every non-empty pre-forest value at its id. -/
theorem vals_vbytes (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    valRecvs (TrieNative.vals m steps) B_VBYTES =
      (TrieNative.seedVals m steps).flatMap fun e =>
        if e.vz then [] else (List.range e.bytes.length).map fun p => [e.vid, p, e.bytes.getD p 0] := by
  simp [valRecvs, TrieNative.vals, ChainMetadata.assignValues, ChainMetadata.patchValue, List.flatMap_map]
  try rfl

theorem nodes_size (ns : List NodeS3) :
    nodeSends3 ns B_SIZE = [[0, ((ns.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum]] := by
  simp [nodeSends3, B_SIZE, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT]

theorem vals_size (es : List ValE) :
    valSends es B_SIZE = [[1, ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum]] := by
  simp [valSends, B_SIZE, B_BYTES, B_ENT]

end ZkFormal.NearV3.Assembly.TrieShared

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

theorem covers_vslot_send : Covers B_VSLOT true (fun t => t == 17) = true := by decide +kernel
theorem covers_vslot_recv : Covers B_VSLOT false (fun t => t == 2) = true := by decide +kernel
theorem pub_vslot (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_VSLOT s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`VSLOT` balance of a bundle** whose node and account components carry `ns` and `as`. -/
theorem balancedAt_vslot (ns : List NodeS3) (as : List AcctV)
    (hn : (R ⟨T_NODE, by decide⟩).tf = nodeTraffic3 ns) (ha : (R ⟨T_ACCT, by decide⟩).tf = acctV3Traffic as)
    (hbal : ∀ m, cnt (acctV3Sends as B_VSLOT) m = cnt (nodeRecvs3 ns B_VSLOT) m) :
    R.BalancedAt B_VSLOT := by
  intro m
  rw [R.sum_tables true _ m _ covers_vslot_send, R.sum_tables false _ m _ covers_vslot_recv,
    pub_vslot, pub_vslot]
  have e2 : R.tf 2 = nodeTraffic3 ns := by rw [← hn]; rfl
  have e17 : R.tf 17 = acctV3Traffic as := by rw [← ha]; rfl
  have hf17 : (List.range 25).filter (fun t => t == 17) = [17] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 2) = [2] := by decide
  rw [hf17, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2, e17, sel, ite_true,
    Bool.false_eq_true, ite_false, nodeTraffic3, acctV3Traffic]
  have := hbal m
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
