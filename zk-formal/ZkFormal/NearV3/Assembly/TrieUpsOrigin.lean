import ZkFormal.NearV3.Rcpt.Candidates.AcceptedWindowCoverage
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderDepth
import ZkFormal.NearV3.Rcpt.Candidates.UpsRequestInventory
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedDepths
import ZkFormal.NearV3.Rcpt.Candidates.NativePayloadSegments
import ZkFormal.NearV3.Assembly.SchedulerSanityPin

/-!
# ZkFormal.NearV3.Assembly.TrieUpsOrigin — the record ids read by the native ups instances

`UpsOrigin F insts`: there is a forest `ts` with as many node records and values as `F` (the
native pre forest `m.pre :: steps.pre`; `ts` is the rebased forest `oldPost :: steps.pre`) such
that, for the instance `I` at position `tau`:

* `I.tau = tau`, `InstOk I`, `NativePartFamily I`;
* every part of kind `≠ NLF` reads the node record `sN` of `ts`, which has `tau` and the part's
  depth `pdep` (`native_reader_depth_tau`, a `tau`-returning copy of `native_reader_depth`);
* a value step `W3` (`mode = 0`) reads an edge of a node record of `ts`
  (`ups_edge_inventory_coverage`; the `START` head keys are excluded by the symbol).

`upsOrigin_of_coverage` derives it from the outputs of `accepted_window_coverage`.
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsOrigin

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 Render Render.UpsGen UpsRows Assembly
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- The record ids read by the native ups instances (see the module doc). -/
def UpsOrigin (F : List PTrie) (insts : List UpsInst) : Prop :=
  ∃ ts : List PTrie,
    (forestNodes 0 0 0 ts).length = (forestNodes 0 0 0 F).length ∧
    (forestBytes ts).length = (forestBytes F).length ∧
    ∀ tau I, insts[tau]? = some I →
      I.tau = tau ∧ InstOk I ∧ NativePartFamily I ∧
      (∀ k, k < nQ I → (part I k).kind ≠ 8 →
        ∃ s, (forestNodes 0 0 0 ts)[(part I k).sN]? = some s ∧ s.tau = tau ∧ (part I k).pdep = s.depth) ∧
      ((step I 3).mode = 0 → ∃ n s, (forestNodes 0 0 0 ts)[n]? = some s ∧ (step I 3).e ∈ edgesOf3 n s)


/-- The scheduler upsert witnesses behind the native ups instances, with the SHA-job facts
(`NativeShaFamily`), the budgets of `schedulerBatch_rows`, and (for the ups `DIGEST` inventory,
`TrieDigestUps`) the allocation and native reader origin of every instance, and (A7 (b), ups part,
`TrieA7Post.ups_post_bound`) `Σ_u (|u.value| + outputByteCharge u.run) ≤ 2,000,000`. -/
def UpsSha (insts : List UpsInst) : Prop :=
  ∃ us : List SchedulerUpsertWitness,
    insts.length = us.length ∧ us.length ≤ 32 ∧
    (∀ u ∈ us, u.Valid ∧ u.run.parts.length ≤ 403 ∧ u.pre.wf = true) ∧
    (us.map (fun u => outputByteCharge u.run)).sum ≤ 2131072 ∧
    (us.map (fun u => u.value.length)).sum ≤ 3146912 ∧
    (us.map (fun u => u.value.length + outputByteCharge u.run)).sum ≤ 2000000 ∧
    ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
      NativeShaFamily u I ∧ I.v = u.value.map UInt8.toNat ∧ I.tau = tau ∧
      AllocatedNativeInstance us tau u I ∧
      ∃ root, forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau = some root ∧
        NativeReaderOrigin root u.run u.value I

/-- `UpsSha` whose witnesses carry the native sanity inputs (`CallPin`). -/
def UpsShaPin (k : WalkD0) (m : MainExecutionV3) (steps : List ImplicitStepV3) (insts : List UpsInst) : Prop :=
  ∃ us : List SchedulerUpsertWitness, CallPin k m steps us ∧
    insts.length = us.length ∧ us.length ≤ 32 ∧
    (∀ u ∈ us, u.Valid ∧ u.run.parts.length ≤ 403 ∧ u.pre.wf = true) ∧
    (us.map (fun u => outputByteCharge u.run)).sum ≤ 2131072 ∧
    (us.map (fun u => u.value.length)).sum ≤ 3146912 ∧
    (us.map (fun u => u.value.length + outputByteCharge u.run)).sum ≤ 2000000 ∧
    ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
      NativeShaFamily u I ∧ I.v = u.value.map UInt8.toNat ∧ I.tau = tau ∧
      AllocatedNativeInstance us tau u I ∧
      ∃ root, forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau = some root ∧
        NativeReaderOrigin root u.run u.value I

theorem UpsShaPin.sha {k : WalkD0} {m : MainExecutionV3} {steps : List ImplicitStepV3} {insts : List UpsInst}
    (h : UpsShaPin k m steps insts) : UpsSha insts := by
  obtain ⟨us, -, h⟩ := h
  exact ⟨us, h⟩

/-- The scheduler upsert witnesses behind the native ups instances, with the forest facts used by the
A7 (b) node/value accounting (`TrieA7Total.a7_bound`): the scheduler pre trees `us.map pre` (the rebased
forest `oldPost :: steps.pre`) have, occurrence by occurrence, the node-encoding lengths and the value
lengths of the native pre forest `F`; `F` is well formed; and `Σ_u (U(u.pre) + U(u.run.output)) ≤ B0`. -/
def UpsA7 (F : List PTrie) (insts : List UpsInst) : Prop :=
  ∃ us : List SchedulerUpsertWitness,
    insts.length = us.length ∧
    (∀ u ∈ us, u.Valid ∧ u.pre.wf = true) ∧
    (∀ t ∈ F, t.wf = true) ∧
    ((us.map SchedulerUpsertWitness.pre).flatMap ZkFormal.NearV3.occs).map
        (fun o => (ZkFormal.NearV3.nodeEnc o).length) =
      (F.flatMap ZkFormal.NearV3.occs).map (fun o => (ZkFormal.NearV3.nodeEnc o).length) ∧
    (forestBytes (us.map SchedulerUpsertWitness.pre)).map List.length = (forestBytes F).map List.length ∧
    (us.map (fun u => NearSpecV3.unfoldedBytesT u.pre + NearSpecV3.unfoldedBytesT u.run.output)).sum ≤ 2000000 ∧
    ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
      NativeShaFamily u I ∧ I.v = u.value.map UInt8.toNat ∧ AllocatedNativeInstance us tau u I ∧
      ∃ root, forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau = some root ∧
        NativeReaderOrigin root u.run u.value I

private theorem root_depth' : ∀ n v ts tau root,
    forestRootAt n v ts tau = some root → root.depth = 0
  | _, _, [], _, _, h => by simp [forestRootAt] at h
  | _, _, _ :: _, 0, _, h => by cases h; rfl
  | n, v, t :: ts, tau + 1, root, h => root_depth' (n + tsize t) (v + (valsOf t).length) ts tau root h

/-- `native_reader_depth`, also returning the provider's `tau`. -/
theorem native_reader_depth_tau {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau = some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value = some run)
    (baseI : UpsInst) (base : Nat → UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run base = some Qs) (k : Nat) (hk : k < Qs.length)
    (hkind : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs) k).kind ≠ 8) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃ s, (forestStoreViews ts).nodes[(part I k).sN]? = some s ∧ s.tau = tau ∧ (part I k).pdep = s.depth := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨p, Q, hp, hQ, henc, hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hnot : p.kind ≠ .NLF := by
    intro hn
    rw [hpart] at hkind
    change Q.kind ≠ 8 at hkind
    exact hkind ((encodeTreePart_kind henc).trans (by rw [hn]; rfl))
  obtain ⟨a, ha, ht⟩ := native_part_source_position root.tree [0,15] value run hr root.nid root.vid root.depth k p hp hnot
  have ham := List.mem_of_getElem? ha
  have hd := source_address_depth root.nid root.vid root.depth root.tree [0,15] _ a ha
  rw [root_depth' 0 0 ts tau root hroot, Nat.zero_add, sourcePosition_plan hr] at hd
  have hid : recordId p.source = a.nid := ht ▸ extendedRecordId_source ham
  have hs := forestRootAt_view (ns := forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  have hv := sourceAddresses_view _ _ _ _ _ hs a ham
  have hn : isNode a.tree = true := ht ▸ (traceUpsert_nodeParts _ _ _ _ hr p (List.mem_of_getElem? hp)).1
  have hget : (forestStoreViews ts).nodes[a.nid]? = some (seedNodeView tau a.depth a.nid a.vid p.source) := by
    simpa only [forestStoreViews, Nat.zero_add, ht] using hv.get hn
  dsimp only
  rw [hpart]
  change ∃ s, (forestStoreViews ts).nodes[Q.sN]? = some s ∧ s.tau = tau ∧ Q.pdep = s.depth
  have hsid : Q.sN = a.nid := (encodeTreePart_positions henc).2.2.2.1.trans hid
  refine ⟨_, hsid.symm ▸ hget, rfl, ?_⟩
  change Q.pdep = a.depth
  rw [(encodeTreePart_positions henc).1]
  exact hd.symm

theorem mem_nodeEdgeKeys {ss : List NodeS3} {e : ZkFormal.Near.Msg} (h : e ∈ nodeEdgeKeys ss) :
    ∃ n s, ss[n]? = some s ∧ e ∈ edgesOf3 n s := by
  unfold nodeEdgeKeys at h
  obtain ⟨⟨s, n⟩, hp, he⟩ := List.mem_flatMap.mp h
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hp
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hget
  obtain ⟨h1, rfl⟩ := hget
  have hi' : i < ss.length := by simpa using hi
  exact ⟨i, s, by simp [hi', ← h1], he⟩

theorem step3_walkEdgeKey {insts : List UpsInst} {I : UpsInst} (hI : I ∈ insts) (hm : (step I 3).mode = 0) :
    (step I 3).e ∈ walkEdgeKeys (upsWalkInventory insts) := by
  unfold walkEdgeKeys upsWalkInventory
  refine List.mem_filterMap.mpr ⟨step I 3, ?_, by simp [hm]⟩
  refine List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨I, hI, rfl⟩, ?_⟩
  exact List.mem_ofFn.mpr ⟨⟨3, by decide⟩, rfl⟩

theorem forestBytes_replay_length : ∀ rs : List ReplayTree, (∀ r ∈ rs, r.Valid) →
    (forestBytes (rs.map ReplayTree.pre)).length = (forestBytes (rs.map ReplayTree.post)).length
  | [], _ => rfl
  | r :: rs, h => by
    have hl : (valsOf r.pre).length = (valsOf r.post).length :=
      write_vals_count (h r (by simp)).forget.skeleton
    have ih := forestBytes_replay_length rs (fun r hr => h r (by simp [hr]))
    simp only [forestBytes, List.map_cons, List.flatMap_cons, List.length_append] at ih ⊢
    omega

/-- **`UpsOrigin` from the native coverage outputs.** -/
theorem upsOrigin_of_coverage (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hpairs : us.map (fun u => (u.pre, u.run.output)) =
      (oldPost, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))
    (hval : ∀ u ∈ us, u.Valid) (hcount : insts.length = us.length)
    (hinst : ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
      AllocatedNativeInstance us tau u I ∧
      ExactNativeWalkProviders (us.map (fun u => (u.pre, u.run.output))) u.run I ∧
      I.ci = u.run.terminal.ix ∧
      ∃ root, forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau = some root ∧
        NativeReaderOrigin root u.run u.value I)
    (hforest : ∀ r ∈ nativeReplayForest m steps oldPost writes, r.Valid) :
    UpsOrigin (m.pre :: steps.map ImplicitStepV3.pre) insts := by
  let rs := nativeReplayForest m steps oldPost writes
  have hpreEq : us.map SchedulerUpsertWitness.pre = rs.map ReplayTree.post := by
    have hh := congrArg (List.map Prod.fst) hpairs
    simpa [rs, nativeReplayForest, List.map_map, Function.comp_def] using hh
  have hrs : rs.map ReplayTree.pre = m.pre :: steps.map ImplicitStepV3.pre := by
    simp [rs, nativeReplayForest, Function.comp_def]
  refine ⟨us.map SchedulerUpsertWitness.pre, ?_, ?_, ?_⟩
  · have hd := congrArg List.length (replay_forest_depths rs 0 0 0 0 0 hforest)
    simp only [List.length_map] at hd
    rw [hpreEq, ← hd, hrs]
  · rw [hpreEq, ← forestBytes_replay_length rs hforest, hrs]
  intro tau I hI
  have htau : tau < us.length := by
    have := (List.getElem?_eq_some_iff.mp hI).1
    omega
  have hu : us[tau]? = some us[tau] := by simp [htau]
  obtain ⟨a, ex, ci, root, hroot, horig⟩ := hinst tau us[tau] I hu hI
  refine ⟨a.1, a.2.2.2.2.1, a.2.2.2.2.2.2.2, ?_, ?_⟩
  · intro k hk hkind
    have hv := hval us[tau] (List.getElem_mem htau)
    have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) tau
    rw [hroot, List.getElem?_map, hu] at ht
    have htree : root.tree = us[tau].pre := Option.some.inj ht
    have hr : traceUpsert root.tree [0,15] us[tau].value = some us[tau].run := by
      simpa only [htree, keyBwState_nibbles] using hv.1
    obtain ⟨B, base, Qs, he, rfl⟩ := horig
    have hk' : k < Qs.length := by simpa using hk
    simpa only [forestStoreViews] using native_reader_depth_tau hroot hr B _ he k hk' hkind
  · intro hm
    have hc := ups_edge_inventory_coverage (us.map (fun u => (u.pre, u.run.output))) insts (by
      intro J hJ
      obtain ⟨j, hj, hJe⟩ := List.mem_iff_getElem.mp hJ
      have hju : j < us.length := by omega
      obtain ⟨a', ex', ci', -⟩ := hinst j us[j] J (by simp [hju]) (by simp [hj, hJe])
      exact ⟨us[j].run, a'.2.2.2.2.1, ex', ci'⟩) _ (step3_walkEdgeKey (List.mem_of_getElem? hI) hm)
    rcases List.mem_append.mp hc with hh | hn
    · exfalso
      obtain ⟨h, -, he⟩ := List.mem_map.mp hh
      have hs := (a.2.2.2.2.1.walk.stepE 3 (by decide) (by decide) hm).1
      rw [← he] at hs
      revert hs
      simp only [headEdgeKey, UpsGen.wsym, List.getD_cons_succ, List.getD_cons_zero]
      decide
    · have hn' : (step I 3).e ∈ nodeEdgeKeys (forestNodes 0 0 0 (us.map SchedulerUpsertWitness.pre)) := by
        simpa only [forestStoreViews, List.map_map, Function.comp_def] using hn
      exact mem_nodeEdgeKeys hn'

end ZkFormal.NearV3.Assembly.TrieUpsOrigin
