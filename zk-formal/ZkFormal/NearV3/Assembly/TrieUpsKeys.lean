import ZkFormal.NearV3.Rcpt.Candidates.AcceptedWindowCoverage
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedUpsertKeys

/-!
# ZkFormal.NearV3.Assembly.TrieUpsKeys — the native coverage chain with the replay's write keys
and final upsert

Copies of `native_rebased_upserts_keys`, `native_rebased_physical_bounds`,
`accepted_rebased_origin_instances`/`native_rebased_origin_instances` and
`accepted_window_coverage` whose single choice of `writes`/`oldPost` also carries
`KeysFinal`: the replay writes exactly the applied receipts' account keys, and `oldPost`
upserts to the main post trie (`hkeys`/`hup` of `vslot_accepted`, previously dropped by the
chain).  The originals are unchanged (other modules destructure them).
-/

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- The replay's write keys and final upsert. -/
def KeysFinal (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) (writes : List (List Nat × Bytes))
    (oldPost : PTrie) : Prop :=
  writes.map Prod.fst = (appliedReceipts k w).map (fun r => accountKeyPath r.receiverId) ∧
    ∃ state, oldPost.upsert keyBwState state = some m.result.trie

theorem upserts_kf {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.L.numShards≤64) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,
      KeysFinal k w m writes oldPost ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      (∀u∈us,u.Valid ∧ u.value.length≤98341) ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  obtain ⟨writes,oldPost,mid,so,u,hu,hctx,hpre,hvalue,houtput,hvalid,hs,hkeys,hr,hfinal,hforest,hbytes⟩:=
    native_execution_rebased_payloads_keys hm hv
  obtain ⟨us,hpairs,hgood⟩:=implicit_exact_upserts hv hl
  have hlen:=SchedulerUpsertWitness.value_bound hvalid (by rw [hctx];exact hl)
  refine ⟨writes,oldPost,u::us,⟨hkeys,_,hfinal⟩,hr,?_,?_,hforest,hbytes⟩
  · simp only [List.map_cons,hpre,houtput,hpairs]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨hvalid,hlen⟩
    · exact hgood x hx

theorem physical_kf {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length≤31) (hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,
      KeysFinal k w m writes oldPost ∧ SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  have hc : checkD0 cb wb=.ok () := by
    unfold checkD0a at h
    obtain ⟨u,hu,_⟩:=ReexecV3D0.bind_ok' h
    cases u;exact hu
  have hL:=(checkD0_claim_guards hk hw hc).1.layout.2
  obtain ⟨writes,oldPost,us,hkf,hr,hpairs,hvalid,hforest,hbytes⟩:=upserts_kf hm hv hL
  have he : us.map SchedulerUpsertWitness.pre=oldPost::steps.map ImplicitStepV3.pre := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa only [List.map_map,List.map_cons,Function.comp_def] using hh
  have hcount:=congrArg List.length he
  simp only [List.length_map,List.length_cons] at hcount
  have hmem : ∀u∈us,u.pre∈oldPost::steps.map ImplicitStepV3.pre := by
    intro u hu
    rw [←he]
    exact List.mem_map.mpr ⟨u,hu,rfl⟩
  have hwell : ∀u∈us,u.pre.wf=true := by
    intro u hu
    rcases List.mem_cons.mp (hmem u hu) with hp|hp
    · rw [hp]
      exact SizedAccountRun.wf hr (hwf _ (by simp))
    · exact hwf _ (by simp [hp])
  have hdepth : ∀u∈us,fdepth u.pre keyBwState≤400 := by
    intro u hu
    rcases List.mem_cons.mp (hmem u hu) with hp|hp
    · rw [hp,←write_lookup_depth hr.forget.skeleton,hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.2.2 _
    · obtain ⟨s,hs,hp⟩:=List.mem_map.mp hp
      obtain ⟨hpre,hroot,_⟩:=hv.input_facts s hs
      rw [←hp,hpre]
      exact (built_spec s.witness.values trieFuel s.root _ hroot).2.2.2 _
  have hb:=checkD0a_preBytes hk hw h hm hv
  have hb' : preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 := by
    rw [he]
    simpa only [preBytes,List.map_cons,List.sum_cons,SizedAccountRun.unfolded_bytes hr,B0] using hb
  have hout:=schedulerUpserts_output_tight_charge us (fun u hu=>(hvalid u hu).1) hwell
  have hval:=scheduler_value_sum us (fun u hu=>(hvalid u hu).2)
  refine ⟨writes,oldPost,us,hkf,hr,hpairs,by omega,by omega,?_,hb',by omega,by omega,hforest,hbytes⟩
  intro u hu
  have hp:=traceUpsert_count u.pre keyBwState u.value u.run (hvalid u hu).1.1
  exact ⟨(hvalid u hu).1,hwell u hu,by have hh:=hdepth u hu;omega,hdepth u hu,(hvalid u hu).2⟩

theorem coverage_kf {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃insts : List UpsInst,
      KeysFinal k w m writes oldPost ∧ SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      insts.length=us.length ∧
      (∀tau u I,us[tau]?=some u→insts[tau]?=some I→
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
        ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        I.ci=u.run.terminal.ix ∧ DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
          NativeReaderOrigin root u.run u.value I) ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) ∧
      ∀t r,r∈physicalWindowRows (Candidates.CompactHeight.trace insts) t→
        physicalWindowKey (Candidates.CompactHeight.trace insts) t r∈nodeWindowKeys
          (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B0 cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hc
  have hlen : steps.length≤31 := by
    have hs:=hv.length
    simp only [List.length_zip] at hs
    omega
  have hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  obtain ⟨writes,oldPost,us,hkf,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hforest,hbytes⟩:=
    physical_kf hk hw h hm hv hlen hwf
  obtain ⟨insts,hcount,hinst⟩:=chosen_origin_instances hgood hpre hout baseI base
  let rs:=nativeReplayForest m steps oldPost writes
  have hpreEq : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa [rs,nativeReplayForest,List.map_map,Function.comp_def] using hh
  have hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  have hrs : rs.map ReplayTree.pre=m.pre::steps.map ImplicitStepV3.pre := by
    simp [rs,nativeReplayForest,List.map_map,Function.comp_def]
  have hwr : ∀r∈rs,r.pre.wf=true := by
    intro r hr
    exact hwf _ (hrs ▸ List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hn:=native_window_provider_ok hk hw h hm hv (forestOldInputs rs)
  have hb:=native_window_provider_bytes (m.pre::steps.map ImplicitStepV3.pre) hwf (forestOldInputs rs)
  refine ⟨writes,oldPost,us,insts,hkf,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes,?_⟩
  intro t
  apply native_physical_window_coverage rs hforest hwr (hpreEq ▸ hpre) us insts hpreEq
    (fun u hu=>⟨(hgood u hu).1,(hgood u hu).2.1⟩) hcount
  · intro tau u I hu hI
    obtain ⟨a,sha,exactp,ci,dispatch,root,hroot,origin⟩:=hinst tau u I hu hI
    exact ⟨a,root,hroot,origin⟩
  · simpa only [hrs] using hn.wf
  · intro s hs x hx
    rw [hrs] at hs
    exact hb s hs true x hx

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
