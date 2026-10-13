import ZkFormal.NearV3.Assembly.TrieDigestUps
import ZkFormal.NearV3.Assembly.TrieShaEmpty
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestPipeline
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayDigestPartition
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestBoundJobs

/-!
# ZkFormal.NearV3.Assembly.TrieDigestTrie — the trie side `htrie` of the bundle `DIGEST` balance

* **`node_head_digests`** (message level, accepted native data): node + head `DIGEST` receives of
  `ns = TrieNative.nodes …`, `hs = TrieNative.heads …` are the digests of the native family WITH the
  empty-value jobs, `jobsToSha (nativeShaJobsE ns es)`, plus the written-value cross term
  `X = ns.flatMap postSlotDigests` (whose SHA jobs are the account jobs, receipt family).
  Ingredients: `native_replay_digest_partition` + `pipeline_node_job_digests` (head + child
  digests = node jobs), `slot_digest_split`, `native_preSlot_inventory` + `valueJobsE_digests`
  (pre-slot digests = value jobs incl. empty ones).
* **`RenderBundleV3.htrie_of`**: the `htrie` hypothesis of `TrieShaBus.RenderBundleV3.balancedAt_digest`
  (tables 2, 3, 7) from the node/head identity and the ups inventory (`TrieDigestUps`).
-/

namespace ZkFormal.NearV3.Assembly.TrieDigestTrie

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate TrieShaEmpty TrieShaBus

theorem cnt_perm {a b : List ZkFormal.Near.Msg} (h : (a.map Msg.toFp).Perm (b.map Msg.toFp)) (m : List Fp) :
    cnt a m = cnt b m := h.count_eq m

theorem cnt_flat_append {α : Type} (xs : List α) (f g : α → List ZkFormal.Near.Msg) (m : List Fp) :
    cnt (xs.flatMap (fun x => f x ++ g x)) m = cnt (xs.flatMap f) m + cnt (xs.flatMap g) m := by
  induction xs with
  | nil => simp [cnt]
  | cons x xs ih =>
    simp only [List.flatMap_cons, cnt, List.map_append, List.count_append] at *
    omega

/-- The count algebra of `node_head_digests`, for any node records `ns`, head receives `H` and values `es`. -/
theorem node_head_core (ns : List NodeS3) (es : List ValE) (H : List ZkFormal.Near.Msg) (msg : List Fp)
    (hc : cnt H msg + cnt (ns.flatMap childDigests) msg =
      cnt (Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ns))) msg)
    (hpre : ns.flatMap preSlotDigests = (nativeValueShaJobsE es).map Render.digestMsg) :
    cnt (nodeRecvs3 ns B_DIGEST) msg + cnt H msg =
      cnt (Sha.Gen.expectedDigests (jobsToSha (nativeShaJobsE ns es))) msg + cnt (ns.flatMap postSlotDigests) msg := by
  have hE : Sha.Gen.expectedDigests (jobsToSha (nativeShaJobsE ns es)) =
      Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ns)) ++
        (nativeValueShaJobsE es).map Render.digestMsg := by
    rw [← NearV3.Candidates.ReceiptDigestPartition.jobs_digests (nativeValueShaJobsE es), ← expectedDigests_append]
    unfold nativeShaJobsE jobsToSha
    rw [List.map_append]
  have hslot : cnt (ns.flatMap slotDigests) msg = cnt (ns.flatMap preSlotDigests) msg +
      cnt (ns.flatMap postSlotDigests) msg := by
    rw [← cnt_flat_append]
    have hf : slotDigests = fun s => preSlotDigests s ++ postSlotDigests s := funext slot_digest_split
    rw [hf]
  rw [node_digest_records, cnt_flat_append, hE, TrieShaBus.cnt_append, hslot, hpre]
  omega

/-- **Node + head `DIGEST` receives of the accepted native records.** -/
theorem node_head_digests {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat × Bytes)} (hr : SizedAccountRun m.pre writes oldPost)
    (q : UseRequests) (keys : List ZkFormal.Near.Msg)
    (hn : NodeOk (TrieNative.nodes m steps oldPost writes q)) (msg : List Fp) :
    cnt (nodeRecvs3 (TrieNative.nodes m steps oldPost writes q) B_DIGEST) msg +
        cnt (headRecvs (TrieNative.heads m steps oldPost writes keys) B_DIGEST) msg =
      cnt (Sha.Gen.expectedDigests (jobsToSha (nativeShaJobsE (TrieNative.nodes m steps oldPost writes q)
          (TrieNative.vals m steps)))) msg +
        cnt ((TrieNative.nodes m steps oldPost writes q).flatMap postSlotDigests) msg := by
  let rs := nativeReplayForest m steps oldPost writes
  have hrs : rs.map ReplayTree.pre = TrieNative.forest m steps := by
    simp [rs, nativeReplayForest, TrieNative.forest, Function.comp_def]
  have hvalid : ∀ r ∈ rs, r.Valid := by
    intro r hh
    simp only [rs, nativeReplayForest, List.mem_cons, List.mem_map] at hh
    rcases hh with rfl | ⟨s, hs, rfl⟩
    · exact hr
    · exact SizedAccountRun.nil _
  have hwell : ∀ r ∈ rs, r.pre.wf = true := by
    intro r hh
    simp only [rs, nativeReplayForest, List.mem_cons, List.mem_map] at hh
    rcases hh with rfl | ⟨s, hs, rfl⟩
    · change m.pre.wf = true
      rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · exact (hv.input_facts s hs).2.2
  have hns : TrieNative.nodes m steps oldPost writes q =
      assignList q 0 (records (forestOldInputs rs) (NearV3.Candidates.ChainMetadata.assign (TrieNative.chain m steps) 0
        (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))) := by
    rw [hrs]; rfl
  have hj := pipeline_node_job_digests rs hvalid hwell q (TrieNative.chain m steps)
    (fun s hs => hn.wf.wf s (hns ▸ hs))
  have hp := native_replay_digest_partition hm hv hr (steps := steps)
  have hchild := pipeline_child_digests (forestOldInputs rs) q (TrieNative.chain m steps)
    (forestNodes 0 0 0 (rs.map ReplayTree.pre))
  have hpre := native_preSlot_inventory (forestOldInputs rs) q (TrieNative.chain m steps) (TrieNative.forest m steps)
  have hhead : headRecvs (TrieNative.heads m steps oldPost writes keys) B_DIGEST =
      headRecvs (forestWalkHeads 0 0 (rs.map (fun r => (r.pre, r.post)))) B_DIGEST := by
    simp only [TrieNative.heads, headRecvs, ite_true, assignHeadUses, List.flatMap_map]
    rfl
  rw [hhead]
  apply node_head_core
  · rw [hns, hchild, hj, ← TrieShaBus.cnt_append]
    exact cnt_perm (hp.map Msg.toFp) msg
  · rw [valueJobsE_digests]
    exact hpre

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`htrie` of `balancedAt_digest`** (tables 2, 3, 7): from the node + head identity and the ups
`DIGEST` inventory of the SAME scheduler witnesses `us`. -/
theorem htrie_of (ns : List NodeS3) (hs : List HeadE) (Js : List UpsInst) (hok : UpsRenderOk Js)
    (us : List SchedulerUpsertWitness) (N : List Render.Msg) (X : List ZkFormal.Near.Msg)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 ns))
    (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (viewOf (upsTraceAligned Js) T_UPS (segsOf Js))))
    (hnode : ∀ m, cnt (nodeRecvs3 ns B_DIGEST) m + cnt (headRecvs hs B_DIGEST) m =
      cnt (Sha.Gen.expectedDigests (jobsToSha N)) m + cnt X m)
    (hups : ((CompactPhysicalDigests.compactGeneratedDigests Js).map Msg.toFp).Perm
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp)) :
    ∀ m, cnt ((R.tf 2).recvs B_DIGEST) m + cnt ((R.tf 3).recvs B_DIGEST) m +
        cnt ((R.tf 7).recvs B_DIGEST) m =
      cnt (Sha.Gen.expectedDigests (schedulerShaJobs 0 us ++ jobsToSha N)) m + cnt X m := by
  intro m
  have e2 := R.tf_ext 2 (by decide) hn B_DIGEST (by decide) (by decide) (by decide)
  have e7 := R.tf_ext 7 (by decide) hu B_DIGEST (by decide) (by decide) (by decide)
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  rw [e2.2, e7.2, e3, expectedDigests_append, TrieShaBus.cnt_append]
  simp only [nodeTraffic3, headTraffic, upsTraffic]
  rw [TrieDigestUps.view_digest_recv Js hok T_UPS, cnt_perm hups m]
  have := hnode m
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly.TrieDigestTrie
