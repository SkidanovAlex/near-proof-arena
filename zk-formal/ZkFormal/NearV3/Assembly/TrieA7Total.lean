import ZkFormal.NearV3.Assembly.TrieA7Match
import ZkFormal.NearV3.Candidates.NativePostShaBudget

/-!
# ZkFormal.NearV3.Assembly.TrieA7Total — A7 (b): the honest A7 total fits `B0` (step 3)

**`a7_bound`**: for the native records `ns = TrieNative.nodes m steps oldPost writes q`,
`es = TrieNative.vals m steps`, the ranked ups instances `Js = upsRanked ws insts` with `UpsA7 F insts`
(exported by `trie_all_of`, `F = m.pre :: steps.pre`) and ANY selections `S`/`SV` whose records are the
`RPL`/`RPLV` sends of `Js` (the A7 (a) permutations of `a7_perm_native`):

`nodeA7Total ns S + valA7Total es SV + upsA7Total Js ≤ 2,000,000 (= B0)`.

Proof: `nodeA7Total + Σ_S |ser| = 2·Σ|ser|` and the same for values; `Σ_S |ser| ≥ Σ_u replacedCharge`,
`Σ_SV len ≥ Σ_u oldValCharge` (`rpl_cover`/`rplv_cover`, summed through the permutations); the record
lengths are those of the scheduler pre trees `us.map pre` (`UpsA7`); with the per-upsert identity
`traceUpsert_replaced` the total is at most `Σ_u (U(u.pre) + U(u.run.output)) ≤ 2,000,000`.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Total

open NearSpec Render Render.UpsGen ZkFormal.NearV3.Assembly TrieA7Post TrieA7Repl TrieA7Match

/-! ## Generic sums -/

theorem sum_le_index {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (l1 : List α) (l2 : List β),
    l1.length = l2.length → (∀ i (h1 : i < l1.length) (h2 : i < l2.length), f l1[i] ≤ g l2[i]) →
    (l1.map f).sum ≤ (l2.map g).sum
  | [], [], _, _ => Nat.le_refl _
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l1, b :: l2, hl, h => by
    simp only [List.map_cons, List.sum_cons]
    have h0 := h 0 (by simp) (by simp)
    have ih := sum_le_index f g l1 l2 (by simpa using hl) (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))
    simp only [List.getElem_cons_zero] at h0
    omega

theorem sum_split (S : Nat → Bool) (f : Nat → Nat) (l : List Nat) :
    (l.map fun n => (if S n then 1 else 2) * f n).sum + ((l.filter S).map f).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : S a = true
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ite_true]; omega
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, Bool.false_eq_true, ite_false]; omega

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem perm_sum {L : List (List Nat)} {N : Nat} {S : Nat → Bool}
    (h : L.Perm (((List.range N).filter S).map fun n => [n])) (f : Nat → Nat) :
    (L.map fun b => f (b.getD 0 0)).sum = (((List.range N).filter S).map f).sum := by
  rw [List.Perm.sum_nat (h.map (fun b => f (b.getD 0 0)))]
  simp [List.map_map, Function.comp_def]

theorem perm_mem {L : List (List Nat)} {N : Nat} {S : Nat → Bool}
    (h : L.Perm (((List.range N).filter S).map fun n => [n])) {b : List Nat} (hb : b ∈ L) :
    b.getD 0 0 < N := by
  have := h.mem_iff.mp hb
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp this
  simpa using (List.mem_filter.mp hn).1

theorem getD_map_eq {α β : Type} {l1 : List α} {l2 : List β} {g1 : α → Nat} {g2 : β → Nat} (d1 : α) (d2 : β)
    (E : l1.map g1 = l2.map g2) {n : Nat} (hn : n < l1.length) : g1 (l1.getD n d1) = g2 (l2.getD n d2) := by
  have hl : l1.length = l2.length := by simpa using congrArg List.length E
  have := congrArg (·[n]?) E
  simp only [List.getElem?_map, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem (show n < l2.length by omega),
    Option.map_some, Option.some.injEq] at this
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem (show n < l2.length by omega),
    this]

theorem seedValuesFrom_len : ∀ (v : Nat) (bs : List Bytes), (seedValuesFrom v bs).map ValE.len = bs.map List.length
  | _, [] => rfl
  | v, b :: bs => by simp [seedValuesFrom, seedValue, seedValuesFrom_len (v + 1) bs]

theorem unfolded_sum : ∀ Ts : List PTrie,
    (Ts.map NearSpecV3.unfoldedBytesT).sum =
      ((Ts.flatMap ZkFormal.NearV3.occs).map (fun o => (ZkFormal.NearV3.nodeEnc o).length)).sum +
        ((forestBytes Ts).map List.length).sum
  | [] => rfl
  | t :: Ts => by
    have ih := unfolded_sum Ts
    have ht : NearSpecV3.unfoldedBytesT t =
        ((ZkFormal.NearV3.occs t).map (fun o => (ZkFormal.NearV3.nodeEnc o).length)).sum +
          ((ZkFormal.NearV3.valsOf t).map List.length).sum := by
      simp only [NearSpecV3.unfoldedBytesT, native_occs_eq, native_valsOf_eq, enc_eq]
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, forestBytes] at ih ⊢
    rw [ht]
    omega

/-! ## The bound -/

/-- **A7 (b)**: the honest A7 node + value + ups total is at most `B0 = 2,000,000`. -/
theorem a7_bound {m : MainExecutionV3} {steps : List ImplicitStepV3} {oldPost : PTrie}
    {writes : List (List Nat × Bytes)} {q : Rcpt.Candidates.NodePostUpdate.UseRequests} {insts : List UpsInst} {ws : List WalkR}
    (hA : TrieUpsOrigin.UpsA7 (m.pre :: steps.map ImplicitStepV3.pre) insts)
    (hn : NodeOk (TrieNative.nodes m steps oldPost writes q)) (hvk : ValOk (TrieNative.vals m steps))
    {S SV : Nat → Bool}
    (hS : ((TrieUpsNative.upsRanked ws insts).flatMap TrieA7.upsRplMsgs).Perm
      (((List.range (TrieNative.nodes m steps oldPost writes q).length).filter S).map fun n => [n]))
    (hSV : ((TrieUpsNative.upsRanked ws insts).flatMap TrieA7.upsRplvMsgs).Perm
      (((List.range (TrieNative.vals m steps).length).filter SV).map fun n => [n])) :
    TrieA7.nodeA7Total (TrieNative.nodes m steps oldPost writes q) S + TrieA7.valA7Total (TrieNative.vals m steps) SV +
      TrieA7.upsA7Total (TrieUpsNative.upsRanked ws insts) ≤ 2000000 := by
  obtain ⟨us, hlen, hgood, hFwf, hNL, hVL, hU, hI⟩ := hA
  generalize hns : TrieNative.nodes m steps oldPost writes q = ns at hn hS ⊢
  generalize hes : TrieNative.vals m steps = es at hvk hSV ⊢
  generalize hTs : us.map SchedulerUpsertWitness.pre = Ts at hNL hVL
  have hTwf : ∀ t ∈ Ts, t.wf = true := by
    intro t ht; rw [← hTs] at ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (hgood u hu).2
  -- node record lengths: those of the scheduler pre forest
  have hnsL : ns.map (fun s => (s.v.ser false).length) =
      ((m.pre :: steps.map ImplicitStepV3.pre).flatMap ZkFormal.NearV3.occs).map
        (fun o => (ZkFormal.NearV3.nodeEnc o).length) := by
    rw [← hns]
    exact Candidates.NativePostShaBudget.node_lengths _ hFwf _ _ q
  have hTsL : (forestNodes 0 0 0 Ts).map (fun s => (s.v.ser false).length) =
      (Ts.flatMap ZkFormal.NearV3.occs).map (fun o => (ZkFormal.NearV3.nodeEnc o).length) := by
    have h := congrArg (fun xs : List (List Nat) => xs.map List.length) (forestNodes_bytes false 0 0 0 Ts hTwf)
    simpa only [List.map_map, Function.comp_def, List.length_map] using h
  have hNodesE : ns.map (fun s => (s.v.ser false).length) =
      (forestNodes 0 0 0 Ts).map (fun s => (s.v.ser false).length) := by rw [hnsL, hTsL, hNL]
  have hNlen : (forestNodes 0 0 0 Ts).length = ns.length := by simpa using (congrArg List.length hNodesE).symm
  have hnP : ns.length < ZkFormal.Algebra.P := Nat.lt_of_le_of_lt (TrieA7.length_le_R _) (TrieA7.node_P _ hn)
  -- value lengths
  have hesL : es.map ValE.len = (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).map List.length := by
    rw [← hes]
    simp only [TrieNative.vals, Candidates.ChainMetadata.assignValues, Candidates.ChainMetadata.patchValue,
      List.map_map, Function.comp_def, TrieNative.seedVals, TrieNative.forest]
    exact seedValuesFrom_len 0 _
  have hValsE : es.map ValE.len = (forestBytes Ts).map List.length := by rw [hesL, hVL]
  have hVlen : (forestBytes Ts).length = es.length := by simpa using (congrArg List.length hValsE).symm
  have hvP : es.length < ZkFormal.Algebra.P :=
    Nat.lt_of_le_of_lt (TrieA7.val_length_le _ hvk) (Nat.lt_trans (TrieA7.val_R_lt _ hvk) (by decide))
  -- per-index facts
  have hpairsF : (us.map (fun u => (u.pre, u.run.output))).map Prod.fst = Ts := by
    rw [← hTs]; simp [List.map_map, Function.comp_def]
  have hidx : ∀ i (h1 : i < us.length) (h2 : i < insts.length),
      replacedCharge us[i].run ≤ ((TrieA7.upsRplMsgs insts[i]).map fun b => LT Ts (b.getD 0 0)).sum ∧
      oldValCharge us[i].run ≤ ((TrieA7.upsRplvMsgs insts[i]).map fun b => LV Ts (b.getD 0 0)).sum ∧
      L insts[i] + ((List.range (nQ insts[i])).map fun k => (part insts[i] k).q.length).sum =
        us[i].value.length + outputByteCharge us[i].run := by
    intro i h1 h2
    obtain ⟨sha, hv, alloc, root, hroot, horig⟩ :=
      hI i us[i] insts[i] (List.getElem?_eq_getElem h1) (List.getElem?_eq_getElem h2)
    rw [hTs] at hroot
    have htree : root.tree = us[i].pre := by
      have ht := forestRootAt_tree 0 0 Ts i
      rw [hroot, ← hTs, List.getElem?_map, List.getElem?_eq_getElem h1] at ht
      exact Option.some.inj ht
    have hr : traceUpsert root.tree [0,15] us[i].value = some us[i].run := by
      rw [htree, ← keyBwState_nibbles]; exact (hgood _ (List.getElem_mem h1)).1.1
    have hio := alloc.2.2.2.2.1
    refine ⟨rpl_cover hroot hr horig hio (by omega), ?_, TrieA7Cap.inst_total _ _ sha hv⟩
    rw [← hpairsF] at hroot ⊢
    exact rplv_cover hroot hr horig hio alloc.2.2.2.2.2.1 (by rw [hpairsF]; omega)
  -- nodes
  have hnode := sum_split S (fun n => ((Render.NodeGen3.rec ns n).v.ser false).length) (List.range ns.length)
  have hSumN : ((List.range ns.length).map fun n => ((Render.NodeGen3.rec ns n).v.ser false).length).sum =
      ((Ts.flatMap ZkFormal.NearV3.occs).map (fun o => (ZkFormal.NearV3.nodeEnc o).length)).sum := by
    have := ZkFormal.NearV3.Render.ValGen.map_getD default (fun s : NodeS3 => (s.v.ser false).length) ns
    simp only [Render.NodeGen3.rec]
    rw [this, hnsL, hNL]
  have hRS : (((List.range ns.length).filter S).map fun n => ((Render.NodeGen3.rec ns n).v.ser false).length).sum =
      (((TrieUpsNative.upsRanked ws insts).flatMap TrieA7.upsRplMsgs).map fun b => LT Ts (b.getD 0 0)).sum := by
    rw [← perm_sum hS]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    have hlt := perm_mem hS hb
    exact getD_map_eq default default hNodesE hlt
  rw [TrieA7.rpl_ranked, List.map_flatMap, TrieA7.sum_flatMap_nat] at hRS
  have hRepl : (us.map fun u => replacedCharge u.run).sum ≤
      (insts.map fun I => ((TrieA7.upsRplMsgs I).map fun b => LT Ts (b.getD 0 0)).sum).sum :=
    sum_le_index _ _ us insts hlen.symm (fun i h1 h2 => (hidx i h1 h2).1)
  -- values
  have hval := sum_split SV (fun t => (Render.ValGen.ent es t).len) (List.range es.length)
  have hSumV : ((List.range es.length).map fun t => (Render.ValGen.ent es t).len).sum =
      ((forestBytes Ts).map List.length).sum := by
    have := ZkFormal.NearV3.Render.ValGen.map_getD default ValE.len es
    simp only [Render.ValGen.ent]
    rw [this, hValsE]
  have hRV : (((List.range es.length).filter SV).map fun t => (Render.ValGen.ent es t).len).sum =
      (((TrieUpsNative.upsRanked ws insts).flatMap TrieA7.upsRplvMsgs).map fun b => LV Ts (b.getD 0 0)).sum := by
    rw [← perm_sum hSV]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    have hlt := perm_mem hSV hb
    exact getD_map_eq default [] hValsE hlt
  rw [TrieA7.rplv_ranked, List.map_flatMap, TrieA7.sum_flatMap_nat] at hRV
  have hOld : (us.map fun u => oldValCharge u.run).sum ≤
      (insts.map fun I => ((TrieA7.upsRplvMsgs I).map fun b => LV Ts (b.getD 0 0)).sum).sum :=
    sum_le_index _ _ us insts hlen.symm (fun i h1 h2 => (hidx i h1 h2).2.1)
  -- ups
  have hUps : TrieA7.upsA7Total insts ≤ (us.map fun u => u.value.length + outputByteCharge u.run).sum := by
    unfold TrieA7.upsA7Total
    exact sum_le_index _ _ insts us hlen (fun i h1 h2 => Nat.le_of_eq (hidx i h2 h1).2.2)
  rw [TrieA7.total_ranked]
  -- the per-upsert identity, summed
  have hid : (us.map fun u => NearSpecV3.unfoldedBytesT u.pre + (outputByteCharge u.run + u.value.length)).sum =
      (us.map fun u => NearSpecV3.unfoldedBytesT u.run.output + (replacedCharge u.run + oldValCharge u.run)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro u hu
    have h := traceUpsert_replaced u.pre _ u.value u.run (hgood u hu).1.1 (hgood u hu).2 (by
      rw [keyBwState_nibbles]; intro x hx; simp at hx; omega)
    unfold ReplOk at h
    omega
  have hpre : (us.map fun u => NearSpecV3.unfoldedBytesT u.pre).sum =
      ((Ts.flatMap ZkFormal.NearV3.occs).map (fun o => (ZkFormal.NearV3.nodeEnc o).length)).sum +
        ((forestBytes Ts).map List.length).sum := by
    rw [← unfolded_sum, ← hTs, List.map_map]; rfl
  simp only [sum_map_add] at hid hU hUps hRepl hOld
  unfold TrieA7.nodeA7Total TrieA7.valA7Total
  omega

theorem filter_sum_le {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    by_cases h : p a = true
    · simp only [List.filter_cons, h, ite_true, List.map_cons, List.sum_cons]; omega
    · simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]; omega

/-- **The `SIZE` base totals of the honest records fit `B0`**: the non-duplicate node bytes plus the
non-empty non-duplicate value bytes are at most `Σ_F U ≤ 2,000,000`. -/
theorem size_base {m : MainExecutionV3} {steps : List ImplicitStepV3} {oldPost : PTrie}
    {writes : List (List Nat × Bytes)} {q : Rcpt.Candidates.NodePostUpdate.UseRequests} {insts : List UpsInst}
    (hA : TrieUpsOrigin.UpsA7 (m.pre :: steps.map ImplicitStepV3.pre) insts) :
    (((TrieNative.nodes m steps oldPost writes q).filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum +
      (((TrieNative.vals m steps).filter fun e => !e.vz && !e.dup).map ValE.len).sum ≤ 2000000 := by
  obtain ⟨us, -, hgood, hFwf, hNL, hVL, hU, -⟩ := hA
  have hnsL := Candidates.NativePostShaBudget.node_lengths _ hFwf (TrieNative.chain m steps)
    (Rcpt.Candidates.NodePostUpdate.forestOldInputs (Rcpt.Candidates.NodePostUpdate.nativeReplayForest m steps oldPost writes)) q
  have hn : ((TrieNative.nodes m steps oldPost writes q).map fun s => (s.v.ser false).length).sum =
      (((us.map SchedulerUpsertWitness.pre).flatMap ZkFormal.NearV3.occs).map
        (fun o => (ZkFormal.NearV3.nodeEnc o).length)).sum := by
    rw [hNL]; exact congrArg List.sum hnsL
  have hesL : (TrieNative.vals m steps).map ValE.len =
      (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).map List.length := by
    simp only [TrieNative.vals, Candidates.ChainMetadata.assignValues, Candidates.ChainMetadata.patchValue,
      List.map_map, Function.comp_def, TrieNative.seedVals, TrieNative.forest]
    exact seedValuesFrom_len 0 _
  have hv : ((TrieNative.vals m steps).map ValE.len).sum =
      ((forestBytes (us.map SchedulerUpsertWitness.pre)).map List.length).sum := by rw [hesL, hVL]
  have h1 := filter_sum_le (fun s : NodeS3 => !s.dup) (fun s => (s.v.ser false).length) (TrieNative.nodes m steps oldPost writes q)
  have h2 := filter_sum_le (fun e : ValE => !e.vz && !e.dup) ValE.len (TrieNative.vals m steps)
  have hpre := unfolded_sum (us.map SchedulerUpsertWitness.pre)
  rw [List.map_map] at hpre
  have hsplit := sum_map_add us (fun u => NearSpecV3.unfoldedBytesT u.pre) (fun u => NearSpecV3.unfoldedBytesT u.run.output)
  have hc : (us.map (NearSpecV3.unfoldedBytesT ∘ SchedulerUpsertWitness.pre)).sum =
      (us.map fun u => NearSpecV3.unfoldedBytesT u.pre).sum := rfl
  omega

end ZkFormal.NearV3.Assembly.TrieA7Total
