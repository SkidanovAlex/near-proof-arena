import ZkFormal.NearV3.Assembly.TrieUps
import ZkFormal.NearV3.Assembly.TrieUpb
import ZkFormal.NearV3.Assembly.TrieUpsOrigin
import ZkFormal.NearV3.Assembly.TrieUpsKeys
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedReplaySharedBalance
import ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootRanks
import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootRecords
import ZkFormal.NearV3.Assembly.UpsertAncestorCost
import ZkFormal.NearV3.Rcpt.Candidates.CompactRootRanks
import ZkFormal.NearV3.Rcpt.Candidates.NativeHeadRootRecords
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootRecords

/-!
# ZkFormal.NearV3.Assembly.TrieUpsNative — native ups instances, EDGE and BMAP from acceptance

From ONE choice of native objects of an accepted witness (`accepted_window_coverage`,
`accepted_same_lookup_physical`, for the given `m`, `steps`):
account-write replay (`writes`, `oldPost`), scheduler upserts `us`, native ups instances `insts`
(each `InstOk` and `NativePartFamily`), the ranked lookup walks `ws` with their walk component.
With the use requests `q = ⟨walkEdgeKeys (ws ++ ups walks), walkBmapKeys …, W⟩` (any `W`) and the
head keys `q.edges`:

* `EDGE` record conservation of `TrieNative.nodes … q`, `TrieNative.heads … q.edges`,
  `rankWalks [] ws` and the ranked ups walks `physicalPrefixUps (ws.flatMap steps) insts`;
* `BMAP` record conservation of the nodes, ranked walks and ranked ups walks;
* `UpsOrigin` (`TrieUpsOrigin`): the node/value records the native instances read;
* `UpsRenderOk` of the ranked instances **given the row cap** `R insts + 1 ≤ 2^22` (open, see
  the lane log: the proven per-family bounds do not imply it; it follows from the A7 measure
  once the ups rows are matched with the rebuilt post tries).
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsNative

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  Qv Qv.Candidates.CombinedWalkGen

/-- The use requests of the honest node records. -/
def useReq (ws : List WalkR) (insts : List UpsInst) (W : List ZkFormal.Near.Msg) : UseRequests :=
  ⟨walkEdgeKeys (ws ++ upsWalkInventory insts), walkBmapKeys (ws ++ upsWalkInventory insts), W⟩

/-- The rendered (counter-ranked) ups instances. -/
def upsRanked (ws : List WalkR) (insts : List UpsInst) : List UpsInst :=
  physicalPrefixUps (ws.flatMap (·.steps)) insts

/-- The native origin of an allocated ups instance (input of `TrieUpsMemdNative.memdPair_of_origin`). -/
def NativeMemdSrc (J : UpsInst) : Prop :=
  ∃ (us : List SchedulerUpsertWitness) (tau : Nat) (u : SchedulerUpsertWitness) (root : OccurrenceAddress),
    AllocatedNativeInstance us tau u J ∧ NativeReaderOrigin root u.run u.value J ∧
    traceUpsert root.tree [0,15] u.value = some u.run ∧ root.tree.wf = true ∧ u.value.length < 2^24

theorem prefix_post_digests (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map UpsInst.post = Is.map UpsInst.post := by
  induction Is generalizing p with
  | nil => rfl
  | cons I Is ih =>
    simpa only [physicalPrefixUps, rankUpsList, List.map_cons, syncUps, rankUps] using congrArg
      (List.cons I.post) (ih (p ++ fourSteps I))

theorem accepted_ups_walks {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Resolve) (pub : List Fp) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (insts : List UpsInst) (v : MainValues) (ws : List WalkR),
      SizedAccountRun m.pre writes oldPost ∧ KeysFinal k w m writes oldPost ∧
      nativeQueryWalks ((m.pre, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve) = some ws ∧
      v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      (∃ Rw : TableRenderV3 pub T_WALK (by decide), Rw.tf = walkTraffic3 (rankWalks [] ws)) ∧
      0 < insts.length ∧ (∀ I ∈ insts, InstOk I) ∧ (∀ I ∈ insts, NativePartFamily I) ∧
      TrieUpsOrigin.UpsOrigin (m.pre :: steps.map ImplicitStepV3.pre) insts ∧
      TrieUpsOrigin.UpsSha insts ∧
      (walkEdgeKeys (ws ++ upsWalkInventory insts)).length < Algebra.P ∧
      (walkBmapKeys (ws ++ upsWalkInventory insts)).length < Algebra.P ∧
      ∀ W : List ZkFormal.Near.Msg, W.length < Algebra.P →
        let q := useReq ws insts W
        let ns := TrieNative.nodes m steps oldPost writes q
        let hs := TrieNative.heads m steps oldPost writes q.edges
        let Js := upsRanked ws insts
        (∀ msg, cnt (nodeSends3 ns B_EDGE) msg + cnt (headSends hs B_EDGE) msg +
            cnt (walkSends3 (rankWalks [] ws) B_EDGE) msg + cnt (upsWalkMessages Js B_EDGE true) msg =
          cnt (nodeRecvs3 ns B_EDGE) msg + cnt (headRecvs hs B_EDGE) msg +
            cnt (walkRecvs3 (rankWalks [] ws) B_EDGE) msg + cnt (upsWalkMessages Js B_EDGE false) msg) ∧
        (∀ msg, cnt (nodeSends3 ns B_BMAP) msg + cnt (walkSends3 (rankWalks [] ws) B_BMAP) msg +
            cnt (upsWalkMessages Js B_BMAP true) msg =
          cnt (nodeRecvs3 ns B_BMAP) msg + cnt (walkRecvs3 (rankWalks [] ws) B_BMAP) msg +
            cnt (upsWalkMessages Js B_BMAP false) msg) ∧
        (R insts + 1 ≤ 2 ^ 22 → UpsRenderOk Js) ∧
        headSends hs B_MIDROOT = Js.map (fun I => [I.tau, I.rid] ++ I.mid) ∧
        (∀ I ∈ Js, I.mid.length = 32 ∧ I.post.length = 32) ∧
        headRecvs hs B_ROOT = Rcpt.Candidates.NodePostUpdate.nativeInputRoots 0 (m.pre :: steps.map ImplicitStepV3.pre) ∧
        Js.map (fun I => [I.tau + 1] ++ I.post) =
          nativeRootRecords 0 (m.result.trie :: steps.map ImplicitStepV3.post) ∧
        (W = Candidates.PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS → R insts + 1 ≤ 2 ^ 22 →
          UpsRows.UpbBal ns (viewOf (upsTraceAligned Js) T_UPS (segsOf Js))) ∧
        (∀ J ∈ Js, NativeMemdSrc J) := by
  obtain ⟨writes, oldPost, us, insts, hkf, hr, hpairs, hpos, hlen, hgood, hpre, hout, hval, hcount, hinst, hforest,
    hbytes, -⟩ := coverage_kf hk hw h hm hv (fun _ => default) (fun _ _ => default)
  obtain ⟨v, ws, hvvalid, hvreads, hws, hwlocal, hwtraffic, hranges⟩ :=
    accepted_same_lookup_physical hk hw h hm hv resolve T_WALK pub
  have hinstl : ∀ I ∈ insts, ∃ i, ∃ hi : i < us.length, us[i]? = some us[i] ∧ insts[i]? = some I := by
    intro I hI
    obtain ⟨i, hii, hei⟩ := List.mem_iff_getElem.mp hI
    exact ⟨i, by omega, by simp [show i < us.length by omega], by simp [hii, hei]⟩
  have hchosen : ∀ I ∈ insts, ∃ run, InstOk I ∧ NativePartFamily I ∧
      ExactNativeWalkProviders (us.map (fun u => (u.pre, u.run.output))) run I ∧ I.ci = run.terminal.ix := by
    intro I hI
    obtain ⟨i, hi, hu, hI'⟩ := hinstl I hI
    obtain ⟨a, -, ex, ci, -, -⟩ := hinst i us[i] I hu hI'
    exact ⟨us[i].run, a.2.2.2.2.1, a.2.2.2.2.2.2.2, ex, ci⟩
  have ho : ∀ I ∈ insts, InstOk I := fun I hI => (hchosen I hI).choose_spec.1
  have hfam : ∀ I ∈ insts, NativePartFamily I := fun I hI => (hchosen I hI).choose_spec.2.1
  have harity : ∀ I ∈ insts, ∀ t < 4, (step I t).mode ≤ 1 → (step I t).e.length = 6 := by
    intro I hI t ht hmo
    obtain ⟨run, ho', -, hp, hci⟩ := hchosen I hI
    exact native_ups_edge_arity _ run I ho' hp hci t ht hmo
  have hcover := native_execution_joint_coverage m steps oldPost writes us insts hpairs hcount
    (fun tau u I hu hI => by
      obtain ⟨a, -, -, ci, dispatch, -⟩ := hinst tau u I hu hI
      exact ⟨a.2.2.2.2.1, dispatch, ci⟩) hforest _ ws hws
  obtain ⟨hedges, hbmaps⟩ := hranges insts (by omega)
  have horigin := TrieUpsOrigin.upsOrigin_of_coverage m steps oldPost writes us insts hpairs
    (fun u hu => (hgood u hu).1) hcount (fun tau u I hu hI => by
      obtain ⟨a, -, ex, ci, -, root, hroot, horig⟩ := hinst tau u I hu hI
      exact ⟨a, ex, ci, root, hroot, horig⟩) hforest
  refine ⟨writes, oldPost, insts, v, ws, hr, hkf, hws, hvvalid, hvreads,
    ⟨⟨nativeWalkTrace (rankWalks [] ws), walkTraffic3 (rankWalks [] ws), hwlocal, hwtraffic,
      by change 22 % 3 = 1; decide⟩, rfl⟩,
    by omega, ho, hfam, horigin, ⟨us, hcount, hlen, fun u hu => ⟨(hgood u hu).1, (hgood u hu).2.2.1⟩, hout, hval,
      fun tau u I hu hI => by
        obtain ⟨a, sha, -⟩ := hinst tau u I hu hI
        exact ⟨sha, a.2.2.2.1, a.1⟩⟩, hedges, hbmaps, ?_⟩
  intro W hW
  -- providers
  obtain ⟨hn0, hvls⟩ := NativeExecutionUsage.inputs hk hw h (by decide) hm hv
  have hids := (StoreClassPartition.combined_metadata _
    (NativeStoreProvenance.valueTau (m.pre :: steps.map ImplicitStepV3.pre)) _ hn0.wf hvls).2.1
  have hprovider := PostNodeLocal.node_ok (forestOldInputs (nativeReplayForest m steps oldPost writes)) _
    (ChainMetadata.node_ok _ _ hn0 hids)
  have hkeys := execution_provider_keys (forestOldInputs (nativeReplayForest m steps oldPost writes))
    (TrieNative.chain m steps) (forestNodes 0 0 0 (m.pre :: steps.map ImplicitStepV3.pre))
  have hheadkeys : headEdgeKeys (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post)))) =
      headEdgeKeys (forestWalkHeads 0 0 ((m.pre, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))) := by
    apply head_keys_fst
    simp [nativeReplayForest, List.map_map, Function.comp_def]
  have hh : ((forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post)))).map HeadE.tau).Nodup := by
    rw [forest_heads_tau]
    exact List.nodup_range'
  have hinstMem : ∀ I ∈ insts, I.mid.length = 32 ∧ I.post.length = 32 := by
    intro I hI
    obtain ⟨i, hi, hu, hI'⟩ := hinstl I hI
    obtain ⟨a, -⟩ := hinst i us[i] I hu hI'
    have hg := hgood us[i] (List.getElem_mem hi)
    refine ⟨by rw [a.2.1, List.length_map]; exact ZkFormal.Near.Prune.hashOf_length _ hg.2.1,
      by rw [a.2.2.1, List.length_map]; exact traceUpsert_output_hash_length hg.1.1⟩
  have hmid : headSends (TrieNative.heads m steps oldPost writes (useReq ws insts W).edges) B_MIDROOT =
      (upsRanked ws insts).map (fun I => [I.tau, I.rid] ++ I.mid) := by
    have hpre' : us.map SchedulerUpsertWitness.pre = (nativeReplayForest m steps oldPost writes).map ReplayTree.post := by
      have hh := congrArg (List.map Prod.fst) hpairs
      simpa [nativeReplayForest, List.map_map, Function.comp_def] using hh
    have hr := native_midroot_records (nativeReplayForest m steps oldPost writes) us insts hforest hpre' hcount
      (fun tau u I hu hI => by
        obtain ⟨a, -, -, -, -, root, hroot, horig⟩ := hinst tau u I hu hI
        exact ⟨a, root, hroot, horig⟩)
    unfold upsRanked
    rw [prefix_midroot_records, ← hr]
    simp [TrieNative.heads, headSends, assignHeadUses, B_MIDROOT]
  have hlens : ∀ J ∈ upsRanked ws insts, J.mid.length = 32 ∧ J.post.length = 32 := by
    intro J hJ
    have hm : J.mid ∈ (upsRanked ws insts).map UpsInst.mid := List.mem_map.mpr ⟨J, hJ, rfl⟩
    have hp : J.post ∈ (upsRanked ws insts).map UpsInst.post := List.mem_map.mpr ⟨J, hJ, rfl⟩
    unfold upsRanked at hm hp
    rw [prefix_mid_digests] at hm
    rw [prefix_post_digests] at hp
    obtain ⟨I, hI, he⟩ := List.mem_map.mp hm
    obtain ⟨I', hI', he'⟩ := List.mem_map.mp hp
    exact ⟨he ▸ (hinstMem I hI).1, he' ▸ (hinstMem I' hI').2⟩
  have hroot1 : headRecvs (TrieNative.heads m steps oldPost writes (useReq ws insts W).edges) B_ROOT =
      Rcpt.Candidates.NodePostUpdate.nativeInputRoots 0 (m.pre :: steps.map ImplicitStepV3.pre) := by
    rw [← replay_head_root_records m steps oldPost writes]
    simp [TrieNative.heads, headRecvs, assignHeadUses, B_ROOT, B_DIGEST]
  have hroot2 : (upsRanked ws insts).map (fun I => [I.tau + 1] ++ I.post) =
      nativeRootRecords 0 (m.result.trie :: steps.map ImplicitStepV3.post) := by
    have houtputs : us.map (fun u => u.run.output) = m.result.trie :: steps.map ImplicitStepV3.post := by
      have hh := congrArg (List.map Prod.snd) hpairs
      simpa only [List.map_map, List.map_cons, Function.comp_def] using hh
    unfold upsRanked
    rw [prefix_root_records, allocated_root_records us insts hcount (fun tau u I hu hI => (hinst tau u I hu hI).1),
      houtputs]
  have hupb : W = Candidates.PhysicalWindowRequests.keys (upsTraceAligned (upsRanked ws insts)) T_UPS →
      R insts + 1 ≤ 2 ^ 22 →
      UpsRows.UpbBal (TrieNative.nodes m steps oldPost writes (useReq ws insts W))
        (viewOf (upsTraceAligned (upsRanked ws insts)) T_UPS (segsOf (upsRanked ws insts))) := by
    intro hWk hcap
    have hok := TrieUps.upsRenderOk_ranked (ws.flatMap (·.steps)) insts (by omega) ho hfam hcap
    let rs := nativeReplayForest m steps oldPost writes
    have hrs : rs.map ReplayTree.pre = m.pre :: steps.map ImplicitStepV3.pre := by
      simp [rs, nativeReplayForest, List.map_map, Function.comp_def]
    have hpreEq : us.map SchedulerUpsertWitness.pre = rs.map ReplayTree.post := by
      have hh := congrArg (List.map Prod.fst) hpairs
      simpa [rs, nativeReplayForest, List.map_map, Function.comp_def] using hh
    have hwf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        exact (hv.input_facts s hs).2.2
    have hwr : ∀ r ∈ rs, r.pre.wf = true := by
      intro r hr
      exact hwf _ (hrs ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hmeta := physicalPrefixUps_origins (us := us) (Is := insts) (fun tau u I hu hI => by
      obtain ⟨a, sha, -, -, -, root, hroot, origin⟩ := hinst tau u I hu hI
      exact ⟨a, sha, root, hroot, origin⟩) (ws.flatMap (·.steps))
    have hcov := TrieUpb.partCov_native rs hforest hwr (hpreEq ▸ hpre) us (upsRanked ws insts) hpreEq
      (fun u hu => ⟨(hgood u hu).1, (hgood u hu).2.1⟩) (hmeta.1.trans hcount)
      (fun tau u I hu hI => ⟨(hmeta.2 tau u I hu hI).1, (hmeta.2 tau u I hu hI).2.2⟩)
    rw [hrs] at hcov
    have hbase := native_window_provider_ok hk hw h hm hv (forestOldInputs rs)
    exact TrieUpb.aligned_upbBal _ hok T_UPS hbase.wf
      (fun s hs x hx => native_window_provider_bytes _ hwf (forestOldInputs rs) s hs true x hx) hcov
      (fun key hk' => by
        have := Candidates.WindowProviderMetadata.member (TrieNative.chain m steps) ⟨[], [], []⟩ _ _ key hk'
        rwa [nodeWindowKeys_assigned] at this)
      (useReq ws insts W) hWk
  have hmemd : ∀ J ∈ upsRanked ws insts, NativeMemdSrc J := by
    have hmeta := physicalPrefixUps_origins (us := us) (Is := insts) (fun tau u I hu hI => by
      obtain ⟨a, sha, -, -, -, root, hroot, origin⟩ := hinst tau u I hu hI
      exact ⟨a, sha, root, hroot, origin⟩) (ws.flatMap (·.steps))
    intro J hJ
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hJ
    have hil : i < us.length := by
      have := hmeta.1; unfold upsRanked at hi; omega
    have hu : us[i]? = some us[i] := List.getElem?_eq_getElem hil
    have hJ' : (physicalPrefixUps (ws.flatMap (·.steps)) insts)[i]? = some J := by
      unfold upsRanked at hi hget
      rw [List.getElem?_eq_getElem hi, hget]
    obtain ⟨a, -, root, hroot, origin⟩ := hmeta.2 i us[i] J hu hJ'
    have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) i
    rw [hroot, List.getElem?_map, hu] at ht
    have heq : root.tree = (us[i]).pre := Option.some.inj ht
    have hg := hgood _ (List.getElem_mem hil)
    have hr' : traceUpsert root.tree [0,15] us[i].value = some us[i].run := by
      simpa only [heq, keyBwState_nibbles] using hg.1.1
    exact ⟨us, i, us[i], root, a, origin, hr', heq ▸ hg.2.1, by have := hg.2.2.2.2; omega⟩
  refine ⟨?_, ?_, fun hcap => TrieUps.upsRenderOk_ranked _ insts (by omega) ho hfam hcap, hmid, hlens, hroot1, hroot2,
    hupb, hmemd⟩
  · intro msg
    have hc : ∀ e ∈ walkEdgeKeys (ws ++ upsWalkInventory insts),
        e ∈ headEdgeKeys (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post)))) ++
          nodeEdgeKeys (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
            (ChainMetadata.assign (TrieNative.chain m steps) 0 (TrieNative.seedNodes m steps))) := by
      rw [hheadkeys]
      have : nodeEdgeKeys (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
          (ChainMetadata.assign (TrieNative.chain m steps) 0 (TrieNative.seedNodes m steps))) =
          nodeEdgeKeys (forestNodes 0 0 0 (m.pre :: steps.map ImplicitStepV3.pre)) := hkeys.1
      rw [this]
      exact hcover.1
    exact TrieUps.edge_records ws insts ho harity _ _ hprovider.wf.wf (useReq ws insts W) rfl hh hc msg
  · intro msg
    have hc : ∀ e ∈ walkBmapKeys (ws ++ upsWalkInventory insts),
        e ∈ nodeBitmapKeys (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
            (ChainMetadata.assign (TrieNative.chain m steps) 0 (TrieNative.seedNodes m steps))) := by
      have : nodeBitmapKeys (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
          (ChainMetadata.assign (TrieNative.chain m steps) 0 (TrieNative.seedNodes m steps))) =
          nodeBitmapKeys (forestNodes 0 0 0 (m.pre :: steps.map ImplicitStepV3.pre)) := hkeys.2
      rw [this]
      exact hcover.2
    exact TrieUps.bmap_records ws insts ho _ (useReq ws insts W) rfl hc msg

end ZkFormal.NearV3.Assembly.TrieUpsNative
