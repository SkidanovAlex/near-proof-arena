import ZkFormal.NearV3.Assembly.TrieA7Rank
import ZkFormal.NearV3.Assembly.TrieA7Val
import ZkFormal.NearV3.Assembly.TrieUpsOrigin
import ZkFormal.NearV3.Assembly.TrieNative
import ZkFormal.NearV3.Extract.Ups.UpsTermT

/-!
# ZkFormal.NearV3.Assembly.TrieA7Perm — A7 (a), semantic part: the `RPL`/`RPLV` record permutations

For native ups instances with `UpsOrigin F insts` (`TrieUpsOrigin`):

* every `RPL` message of the instance at position `tau` is `[x]` for a node record `x` of the
  rebased forest with `tau`; inside one instance the records have pairwise different depths
  (`N_D` at `dep[D]`, the upper part `k` at `dep[D] − (k + 1 − nT)`), so the messages are
  pairwise distinct (`rpl_inst`);
* the `RPLV` message of a value step is the value id of the node record `N_D`
  (`edge_val_id`, `findIdx_valueId`), distinct across instances by `tau`;
* `rpl_perm` / `rplv_perm`: there are `S`/`SV` with
  `(insts.flatMap upsRplMsgs).Perm (((range N).filter S).map ([·]))` for any `N ≥ |nodes F|`,
  `N < P` (resp. values, `M ≥ |forestBytes F|`);
* **`a7_perm_native`**: for the honest records `ns = TrieNative.nodes …`, `es = TrieNative.vals …`
  and the ranked instances `upsRanked ws insts`: `∃ S SV`, the two permutations of
  `balancedAt_rpl` / `balancedAt_rplv`.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 Render Render.UpsGen UpsRows Assembly
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate TrieUpsOrigin

/-! ## Generic list facts -/

theorem nodup_flatMap_key {α β : Type} (key : β → Nat) (f : α → List β) : ∀ (l : List α) (o : Nat),
    (∀ i a, l[i]? = some a → ∀ b ∈ f a, key b = o + i) → (∀ a ∈ l, (f a).Nodup) → (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | a :: l, o, hk, hn => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hn a (by simp), nodup_flatMap_key key f l (o + 1) (fun i b hb x hx => by
      have := hk (i + 1) b (by simpa using hb) x hx; omega) (fun b hb => hn b (by simp [hb])), ?_⟩
    intro x hx y hy hxy
    subst hxy
    have h0 := hk 0 a rfl x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    have h1 := hk (j + 1) l[j] (by simp [hj]) x hxb
    omega

theorem nodup_flatMap_pairwise {α β : Type} (f : α → List β) : ∀ (l : List α),
    (∀ a ∈ l, (f a).Nodup) → l.Pairwise (fun a b => ∀ x, x ∈ f a → x ∈ f b → False) → (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, hp => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨hpa, hpl⟩ := List.pairwise_cons.mp hp
    refine ⟨hn a (by simp), nodup_flatMap_pairwise f l (fun b hb => hn b (by simp [hb])) hpl, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    exact hpa b hb x hx hxb

theorem perm_of_singletons (L : List ZkFormal.Near.Msg) (N : Nat) (hnd : L.Nodup) (hb : ∀ b ∈ L, ∃ x, x < N ∧ b = [x]) :
    ∃ S : Nat → Bool, L.Perm (((List.range N).filter S).map fun n => [n]) := by
  refine ⟨fun n => decide ([n] ∈ L), (List.perm_ext_iff_of_nodup hnd ?_).mpr ?_⟩
  · exact List.pairwise_map.mpr ((List.nodup_range.filter _).imp fun h e => h (by simpa using e))
  · intro b
    simp only [List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · intro h
      obtain ⟨x, hx, rfl⟩ := hb b h
      exact ⟨x, ⟨hx, decide_eq_true h⟩, rfl⟩
    · rintro ⟨n, ⟨-, h⟩, rfl⟩
      exact of_decide_eq_true h

theorem findIdx_valueId : ∀ {L : List NodeS3}, (L.filterMap seedValueId).Nodup → ∀ {n : Nat} {s : NodeS3} {v : Nat},
    L[n]? = some s → seedValueId s = some v → L.findIdx (fun s => seedValueId s == some v) = n
  | [], _, _, _, _, hs, _ => by simp at hs
  | a :: L, hnd, n, s, v, hs, hv => by
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      simp [List.findIdx_cons, hv]
    | succ n =>
      simp only [List.getElem?_cons_succ] at hs
      have hmem : v ∈ L.filterMap seedValueId := List.mem_filterMap.mpr ⟨s, List.mem_of_getElem? hs, hv⟩
      have ha : seedValueId a ≠ some v := by
        intro ha
        rw [List.filterMap_cons, ha] at hnd
        exact (List.nodup_cons.mp hnd).1 hmem
      have hnd' : (L.filterMap seedValueId).Nodup := by
        rw [List.filterMap_cons] at hnd
        cases h : seedValueId a with
        | none => simpa [h] using hnd
        | some w => rw [h] at hnd; exact (List.nodup_cons.mp hnd).2
      rw [List.findIdx_cons, findIdx_valueId hnd' hs hv]
      simp [ha]

theorem edge_val_id {n : Nat} {r : NodeS3} {e : ZkFormal.Near.Msg} (he : e ∈ edgesOf3 n r) (hk : e.getD 5 0 = EK_VAL) :
    e.getD 0 0 = n ∧ seedValueId r = some (e.getD 3 0) := by
  have hne := ek_ne
  unfold edgesOf3 at he
  cases hv : r.v with
  | leaf k sl m =>
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with (⟨i, -, rfl⟩ | he) | he
    · exfalso; simp at hk; exact hne.2.1 hk
    · cases sl <;> simp at he
      subst he
      simp [seedValueId, hv, NodeV3.value]
    · exfalso; simp at he; subst he; simp at hk; revert hk; decide
  | ext k kid m =>
    exfalso
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with ⟨i, -, rfl⟩ | he
    · simp at hk; exact hne.2.1 hk
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x => cases kid <;> simp [hl] at he <;> subst he <;> simp at hk <;> exact hne.2.1 hk
  | branch sv kids m =>
    rw [hv] at he
    simp only [List.mem_append, List.mem_filterMap] at he
    rcases he with ⟨⟨kd, j⟩, -, he⟩ | he
    · exfalso; cases kd <;> simp at he; subst he; simp at hk; revert hk; decide
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      all_goals first
        | (simp at he; done)
        | (simp at he; subst he; simp [seedValueId, hv, NodeV3.value])

/-! ## Terminal plans -/

theorem term_has_reader : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∃ k, k < UpsRows.nTof ci ti ∧
    2 ≤ ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 8 ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 11 := by
  decide

theorem term_not_upper : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ k, k < UpsRows.nTof ci ti →
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 0 ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 1 ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 11 := by
  decide

/-! ## One instance -/

section Inst

variable {nodes : List NodeS3} {I : UpsInst} {tau : Nat}

/-- The per-instance origin facts (a component of `UpsOrigin`). -/
def InstOrigin (nodes : List NodeS3) (tau : Nat) (I : UpsInst) : Prop :=
  InstOk I ∧ NativePartFamily I ∧
  (∀ k, k < nQ I → (part I k).kind ≠ 8 →
    ∃ s, nodes[(part I k).sN]? = some s ∧ s.tau = tau ∧ (part I k).pdep = s.depth) ∧
  ((step I 3).mode = 0 → ∃ n s, nodes[n]? = some s ∧ (step I 3).e ∈ edgesOf3 n s)

theorem nD_node (h : InstOrigin nodes tau I) :
    ∃ s, nodes[nDOf I]? = some s ∧ s.tau = tau ∧ s.depth = I.dep.getD I.D 0 := by
  obtain ⟨io, fam, orig, -⟩ := h
  obtain ⟨k, hk, h2, h8, h11⟩ := term_has_reader I.ci io.ci I.ti io.ti
  have hkQ : k < nQ I := by rw [io.nQ]; omega
  obtain ⟨-, -, po, -⟩ := fam k hkQ
  have hkind := po.kindT hk
  have hsd := po.sdT (by omega) (by omega)
  have hsN := po.sN (by omega)
  have hpd := po.pdepT hk
  obtain ⟨s, hs, hst, hsd'⟩ := orig k hkQ (by omega)
  have hnD : nDOf I = I.N.getD I.D 0 := by
    have := io.D
    unfold nDOf
    rcases (show I.D = 0 ∨ I.D = 1 ∨ I.D = 2 by omega) with h | h | h <;> simp [h]
  refine ⟨s, ?_, hst, by omega⟩
  rw [hnD, ← hsd, ← hsN]
  exact hs

theorem upper_node (h : InstOrigin nodes tau I) {k : Nat} (hk : k < nQ I) (hu : upperB (part I k) = true) :
    UpsRows.nTof I.ci I.ti ≤ k ∧ ∃ s, nodes[(part I k).sN]? = some s ∧ s.tau = tau ∧
      s.depth + (k + 1 - UpsRows.nTof I.ci I.ti) = I.dep.getD I.D 0 := by
  obtain ⟨io, fam, orig, -⟩ := h
  obtain ⟨-, -, po, -⟩ := fam k hk
  have hkd : (part I k).kind = 0 ∨ (part I k).kind = 1 ∨ (part I k).kind = 11 := by
    simp [upperB] at hu; omega
  have hT : UpsRows.nTof I.ci I.ti ≤ k := by
    rcases Nat.lt_or_ge k (UpsRows.nTof I.ci I.ti) with hlt | hge
    · have := term_not_upper I.ci io.ci I.ti io.ti k hlt
      rw [← po.kindT hlt] at this
      omega
    · exact hge
  obtain ⟨s, hs, hst, hpd⟩ := orig k hk (by omega)
  exact ⟨hT, s, hs, hst, by rw [← hpd]; exact po.pdepU hT⟩

theorem rpl_mem (h : InstOrigin nodes tau I) (hP : nodes.length < ZkFormal.Algebra.P) {b : ZkFormal.Near.Msg}
    (hb : b ∈ upsRplMsgs I) : ∃ (x : Nat) (s : NodeS3), b = [x] ∧ nodes[x]? = some s ∧ s.tau = tau := by
  have hmod : ∀ x s, nodes[x]? = some s → x % ZkFormal.Algebra.P = x := by
    intro x s hs
    have := (List.getElem?_eq_some_iff.mp hs).1
    exact Nat.mod_eq_of_lt (by omega)
  rcases List.mem_cons.mp hb with rfl | hb
  · obtain ⟨s, hs, hst, -⟩ := nD_node h
    exact ⟨_, s, by rw [hmod _ _ hs], hs, hst⟩
  · obtain ⟨k, hk, hb⟩ := List.mem_flatMap.mp hb
    split at hb
    · rename_i hc
      obtain ⟨-, s, hs, hst, -⟩ := upper_node h (List.mem_range.mp hk) hc.1
      simp only [List.mem_singleton] at hb
      exact ⟨_, s, by rw [hb, hmod _ _ hs], hs, hst⟩
    · simp at hb

theorem rpl_inst (h : InstOrigin nodes tau I) (hP : nodes.length < ZkFormal.Algebra.P) :
    (upsRplMsgs I).Nodup := by
  have hmod : ∀ x s, nodes[x]? = some s → x % ZkFormal.Algebra.P = x := by
    intro x s hs
    have := (List.getElem?_eq_some_iff.mp hs).1
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨s0, hs0, -, hd0⟩ := nD_node h
  unfold upsRplMsgs
  rw [List.nodup_cons]
  constructor
  · intro hm
    obtain ⟨k, hk, hb⟩ := List.mem_flatMap.mp hm
    split at hb
    · rename_i hc
      obtain ⟨hT, s, hs, -, hd⟩ := upper_node h (List.mem_range.mp hk) hc.1
      simp only [List.mem_singleton, List.cons.injEq, and_true] at hb
      rw [hmod _ _ hs0, hmod _ _ hs] at hb
      rw [hb, hs] at hs0
      cases hs0
      omega
    · simp at hb
  · refine nodup_flatMap_pairwise _ _ (fun k _ => by split <;> simp) ?_
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro k1 k2 hk1 hk2 hlt b hb1 hb2
    split at hb1
    · split at hb2
      · rename_i hc1 hc2
        obtain ⟨hT1, s1, hs1, -, hd1⟩ := upper_node h (List.mem_range.mp hk1) hc1.1
        obtain ⟨hT2, s2, hs2, -, hd2⟩ := upper_node h (List.mem_range.mp hk2) hc2.1
        simp only [List.mem_singleton] at hb1 hb2
        rw [hb1, List.cons.injEq] at hb2
        have he := hb2.1
        rw [hmod _ _ hs1, hmod _ _ hs2] at he
        rw [he, hs2] at hs1
        cases hs1
        omega
      · simp at hb2
    · simp at hb1

theorem rplv_mem (h : InstOrigin nodes tau I) {b : ZkFormal.Near.Msg} (hb : b ∈ upsRplvMsgs I) :
    ∃ (v : Nat) (s : NodeS3), b = [v % ZkFormal.Algebra.P] ∧ nodes[nDOf I]? = some s ∧ s.tau = tau ∧ seedValueId s = some v := by
  obtain ⟨io, fam, orig, hedge⟩ := h
  unfold upsRplvMsgs at hb
  split at hb
  · rename_i hm
    simp only [List.mem_singleton] at hb
    obtain ⟨n, s, hs, he⟩ := hedge hm
    have hval := (io.walk.stepE 3 (by decide) (by decide) hm).2.2 rfl
    obtain ⟨he0, hsv⟩ := edge_val_id he hval
    -- the terminal row is `W3`
    have hts : I.ts = 3 := by
      have hr := io.ts
      rcases (show I.ts = 1 ∨ I.ts = 2 ∨ I.ts = 3 by omega) with h1 | h1 | h1
      · have h0 := io.walk.tsStep.2.2 (by omega)
        rw [h1] at h0
        have h2 : (step I 2).mode = 3 := io.walk.drain 1 (Nat.le_refl _) (by decide) h0
        have h3 : (step I 3).mode = 3 := io.walk.drain 2 (by decide) (by decide) (by omega)
        omega
      · have h0 := io.walk.tsStep.2.2 (by omega)
        rw [h1] at h0
        have h3 : (step I 3).mode = 3 := io.walk.drain 2 (by decide) (by decide) h0
        omega
      · exact h1
    have hlook := io.walk.look 3 (by decide) (by decide) (by omega)
    have hD := io.walk.termD
    rw [hts] at hD
    have hnD : nDOf I = I.N.getD I.D 0 := by
      have := io.D
      unfold nDOf
      rcases (show I.D = 0 ∨ I.D = 1 ∨ I.D = 2 by omega) with h | h | h <;> simp [h]
    have hn : n = nDOf I := by rw [hnD, hD, ← hlook, he0]
    subst hn
    obtain ⟨s', hs', hst, -⟩ := nD_node ⟨io, fam, orig, hedge⟩
    rw [hs] at hs'
    cases hs'
    exact ⟨_, s, hb, hs, hst, hsv⟩
  · simp at hb

end Inst

/-! ## All instances -/

theorem origin_inst {F : List PTrie} {insts : List UpsInst} {ts : List PTrie}
    (h : ∀ tau I, insts[tau]? = some I →
      I.tau = tau ∧ InstOk I ∧ NativePartFamily I ∧
      (∀ k, k < nQ I → (part I k).kind ≠ 8 →
        ∃ s, (forestNodes 0 0 0 ts)[(part I k).sN]? = some s ∧ s.tau = tau ∧ (part I k).pdep = s.depth) ∧
      ((step I 3).mode = 0 → ∃ n s, (forestNodes 0 0 0 ts)[n]? = some s ∧ (step I 3).e ∈ edgesOf3 n s))
    {tau : Nat} {I : UpsInst} (hI : insts[tau]? = some I) : InstOrigin (forestNodes 0 0 0 ts) tau I :=
  (h tau I hI).2

theorem rpl_perm (F : List PTrie) (insts : List UpsInst) (h : UpsOrigin F insts) (N : Nat)
    (hN : (forestNodes 0 0 0 F).length ≤ N) (hP : N < ZkFormal.Algebra.P) :
    ∃ S : Nat → Bool, (insts.flatMap upsRplMsgs).Perm (((List.range N).filter S).map fun n => [n]) := by
  obtain ⟨ts, hlen, -, hI⟩ := h
  have hP' : (forestNodes 0 0 0 ts).length < ZkFormal.Algebra.P := by omega
  apply perm_of_singletons _ N
  · refine nodup_flatMap_key (fun b => (((forestNodes 0 0 0 ts)[b.getD 0 0]?).map NodeS3.tau).getD 0)
      upsRplMsgs insts 0 ?_ ?_
    · intro i I hi b hb
      obtain ⟨x, s, rfl, hs, hst⟩ := rpl_mem (origin_inst (F := F) hI hi) hP' hb
      simp [hs, hst]
    · intro I hm
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
      exact rpl_inst (origin_inst (F := F) hI (List.getElem?_eq_getElem hi)) hP'
  · intro b hb
    obtain ⟨I, hm, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨x, s, rfl, hs, -⟩ := rpl_mem (origin_inst (F := F) hI (List.getElem?_eq_getElem hi)) hP' hb
    have := (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨x, by omega, rfl⟩

theorem rplv_perm (F : List PTrie) (insts : List UpsInst) (h : UpsOrigin F insts) (M : Nat)
    (hM : (forestBytes F).length ≤ M) (hP : M < ZkFormal.Algebra.P) :
    ∃ SV : Nat → Bool, (insts.flatMap upsRplvMsgs).Perm (((List.range M).filter SV).map fun n => [n]) := by
  obtain ⟨ts, -, hlen, hI⟩ := h
  have hids := forestNodes_valueIds 0 0 0 ts
  have hnd : ((forestNodes 0 0 0 ts).filterMap seedValueId).Nodup := by
    rw [hids]; exact List.nodup_range'
  have hlt : ∀ s v, s ∈ forestNodes 0 0 0 ts → seedValueId s = some v → v < (forestBytes F).length := by
    intro s v hs hv
    have hm : v ∈ (forestNodes 0 0 0 ts).filterMap seedValueId := List.mem_filterMap.mpr ⟨s, hs, hv⟩
    rw [hids, List.mem_range'] at hm
    omega
  apply perm_of_singletons _ M
  · refine nodup_flatMap_key (fun b => (((forestNodes 0 0 0 ts)[(forestNodes 0 0 0 ts).findIdx
        (fun s => seedValueId s == some (b.getD 0 0))]?).map NodeS3.tau).getD 0) upsRplvMsgs insts 0 ?_ ?_
    · intro i I hi b hb
      obtain ⟨v, s, rfl, hs, hst, hsv⟩ := rplv_mem (origin_inst (F := F) hI hi) hb
      have hv := hlt s v (List.mem_of_getElem? hs) hsv
      have hmod : v % ZkFormal.Algebra.P = v := Nat.mod_eq_of_lt (by omega)
      simp only [hmod, List.getD_cons_zero]
      rw [findIdx_valueId hnd hs hsv, hs]
      simp [hst]
    · intro I _
      unfold upsRplvMsgs
      split <;> simp
  · intro b hb
    obtain ⟨I, hm, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨v, s, rfl, hs, -, hsv⟩ := rplv_mem (origin_inst (F := F) hI (List.getElem?_eq_getElem hi)) hb
    have hv := hlt s v (List.mem_of_getElem? hs) hsv
    exact ⟨v, by omega, by rw [Nat.mod_eq_of_lt (by omega)]⟩

/-! ## The honest records -/

theorem nodes_length (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) :
    (TrieNative.nodes m steps oldPost writes q).length =
      (forestNodes 0 0 0 (m.pre :: steps.map ImplicitStepV3.pre)).length := by
  simp [TrieNative.nodes, assignList_length, records, Candidates.ChainMetadata.assign_length, TrieNative.seedNodes,
    initializeList_length, TrieNative.forest]

theorem vals_length (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    (TrieNative.vals m steps).length = (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length := by
  simp [TrieNative.vals, Candidates.ChainMetadata.assignValues, TrieNative.seedVals, TrieNative.forest]

/-- **A7 (a), semantic part.**  For the honest native choice (`trie_all_accepted` exports
`UpsOrigin`), the ups `RPL`/`RPLV` sends are permutations of selected node / value records. -/
theorem a7_perm_native (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (insts : List UpsInst) (ws : List WalkR) (q : UseRequests)
    (h : UpsOrigin (m.pre :: steps.map ImplicitStepV3.pre) insts)
    (hn : NodeOk (TrieNative.nodes m steps oldPost writes q)) (hv : ValOk (TrieNative.vals m steps)) :
    ∃ S SV : Nat → Bool,
      ((TrieUpsNative.upsRanked ws insts).flatMap upsRplMsgs).Perm
        (((List.range (TrieNative.nodes m steps oldPost writes q).length).filter S).map fun n => [n]) ∧
      ((TrieUpsNative.upsRanked ws insts).flatMap upsRplvMsgs).Perm
        (((List.range (TrieNative.vals m steps).length).filter SV).map fun n => [n]) := by
  rw [rpl_ranked, rplv_ranked]
  have hnP := Nat.lt_of_le_of_lt (length_le_R _) (node_P _ hn)
  have hvP : (TrieNative.vals m steps).length < ZkFormal.Algebra.P :=
    Nat.lt_of_le_of_lt (val_length_le _ hv) (Nat.lt_trans (val_R_lt _ hv) (by decide))
  obtain ⟨S, hS⟩ := rpl_perm _ insts h _ (by rw [nodes_length]; exact Nat.le_refl _) hnP
  obtain ⟨SV, hSV⟩ := rplv_perm _ insts h _ (by rw [vals_length]; exact Nat.le_refl _) hvP
  exact ⟨S, SV, hS, hSV⟩

end ZkFormal.NearV3.Assembly.TrieA7
