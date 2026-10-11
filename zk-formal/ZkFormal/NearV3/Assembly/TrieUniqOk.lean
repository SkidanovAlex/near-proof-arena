import ZkFormal.NearV3.Assembly.TrieUniqDup
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestByteBounds

/-!
# ZkFormal.NearV3.Assembly.TrieUniqOk — `UOk` of the honest `uniqV3` entries

* `occ_count` — every revealed occurrence other than a root is referenced by a 32-byte hash
  in its parent's encoding, every revealed value by a 36-byte value reference:
  `32 · (#occurrences + #values) ≤ Σ |nodeEnc| + 32` per well-formed tree.  With A7
  (`preBytes ≤ B0 = 2,000,000`) and `≤ 32` trees: at most `62,532` store entries, below the
  `uniqV3` cap `2^17` (`uniqNative_cap`);
* `Adj` (adjacent pairs) on block lists and on the sorted classes (instances step by 0 or 1
  because every tree has a revealed root);
* **`uniqNative_ok`**: `UOk (uniqNative m steps)` for every accepted witness, hence
  `uniqRenderTrie` applies.
-/

namespace ZkFormal.NearV3.Assembly.TrieUniqOk

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives StoreClassPartition TrieUniqOcc TrieEnt TrieUniqDup

/-! ## Counting -/

def encSum (os : List PTrie) : Nat := (os.map fun o => (nodeEnc o).length).sum

theorem encSum_append (a b : List PTrie) : encSum (a ++ b) = encSum a + encSum b := by
  simp [encSum, List.sum_append]

mutual
theorem occ_count : ∀ t : PTrie, t.wf = true →
    32 * ((occs t).length + (valsOf t).length) ≤ encSum (occs t) + 32
  | .hash _, _ => by simp [occs, valsOf, encSum]
  | .leaf k s m, hw => by
    have hv : (slotVal s).length ≤ 1 := by cases s <;> simp [slotVal]
    rw [valsOf_leaf]
    simp only [occs, List.length_singleton, encSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have : 32 * (slotVal s).length ≤ (nodeEnc (.leaf k s m)).length := by
      cases s with
      | val v => simp [slotVal, nodeEnc, Slot.valueRef, u32, u64, NearSpec.leN_length, ArenaCore.sha256_length]; omega
      | ref l h => simp [slotVal]
    omega
  | .ext k c m, hw => by
    have hc : c.wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.1.2
    have ih := occ_count c hc
    rw [valsOf_ext]
    have henc : 32 ≤ (nodeEnc (.ext k c m)).length := by
      have := hashOf_len_of_wf c hc
      simp [nodeEnc, u32, u64, NearSpec.leN_length, this]
      omega
    simp only [occs, List.length_cons, encSum, List.map_cons, List.sum_cons] at ih ⊢
    omega
  | .branch v cs m, hw => by
    have hk : Kids.wf cs 16 = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.2
    have ih := kids_count cs 16 hk
    rw [valsOf_branch]
    have henc : 32 * (optSlotVal v).length + (Kids.hashes cs).length ≤ (nodeEnc (.branch v cs m)).length := by
      cases v with
      | none => simp [optSlotVal, nodeEnc, u16, u64, NearSpec.leN_length]; omega
      | some s =>
        cases s with
        | val x => simp [optSlotVal, slotVal, nodeEnc, Slot.valueRef, u32, u16, u64, NearSpec.leN_length,
            ArenaCore.sha256_length]; omega
        | ref l h => simp [optSlotVal, slotVal, nodeEnc, Slot.valueRef, u32, u16, u64, NearSpec.leN_length]; omega
    simp only [occs, List.length_cons, List.length_append, encSum, List.map_cons, List.sum_cons] at ih ⊢
    omega
theorem kids_count : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    32 * ((kOccs cs).length + (kvals cs).length) ≤ encSum (kOccs cs) + (Kids.hashes cs).length
  | .nil, _, _ => by simp [kOccs, kvals_nil, encSum, Kids.hashes]
  | .none r, n, hw => by
    have hr : Kids.wf r (n - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact hw.2
    simpa [kOccs, kvals_none, Kids.hashes] using kids_count r (n - 1) hr
  | .some c r, n, hw => by
    have h2 : c.wf = true ∧ Kids.wf r (n - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact ⟨hw.1.2, hw.2⟩
    have ihc := occ_count c h2.1
    have ihr := kids_count r (n - 1) h2.2
    have hl := hashOf_len_of_wf c h2.1
    rw [kvals_some]
    simp only [kOccs, Kids.hashes, List.length_append, encSum_append] at ihr ⊢
    omega
end

theorem forest_count (ts : List PTrie) (hw : ∀ t ∈ ts, t.wf = true) :
    32 * ((ts.flatMap occs).length + (forestBytes ts).length) ≤ encSum (ts.flatMap occs) + 32 * ts.length := by
  induction ts with
  | nil => simp [encSum, forestBytes]
  | cons t ts ih =>
    have h1 := occ_count t (hw t (by simp))
    have h2 := ih (fun t' h => hw t' (by simp [h]))
    simp only [List.flatMap_cons, List.length_append, encSum_append, forestBytes, List.length_cons] at h1 h2 ⊢
    omega

/-! ## Adjacent pairs -/

def Adj {α : Type} (R : α → α → Prop) : List α → Prop
  | a :: b :: l => R a b ∧ Adj R (b :: l)
  | _ => True

theorem adj_get {α : Type} (R : α → α → Prop) :
    ∀ (L : List α), Adj R L → ∀ t (h : t + 1 < L.length), R L[t] L[t + 1]
  | [], _, t, h => by simp at h
  | [a], _, t, h => by simp at h
  | a :: b :: l, hA, 0, _ => hA.1
  | a :: b :: l, hA, t + 1, h => by
    have := adj_get R (b :: l) hA.2 t (by simpa using h)
    simpa using this

theorem adj_of_get {α : Type} (R : α → α → Prop) :
    ∀ (L : List α), (∀ t (h : t + 1 < L.length), R L[t] L[t + 1]) → Adj R L
  | [], _ => trivial
  | [a], _ => trivial
  | a :: b :: l, h => ⟨h 0 (by simp), adj_of_get R (b :: l) (fun t ht => by
      have := h (t + 1) (by simpa using ht)
      simpa using this)⟩

theorem adj_append {α : Type} (R : α → α → Prop) :
    ∀ (l1 l2 : List α), Adj R l1 → Adj R l2 → (∀ a ∈ l1.getLast?, ∀ b ∈ l2.head?, R a b) → Adj R (l1 ++ l2)
  | [], l2, _, h2, _ => by simpa using h2
  | [a], [], _, _, _ => trivial
  | [a], b :: l2, _, h2, hb => ⟨hb a (by simp) b (by simp), h2⟩
  | a :: b :: l1, l2, h1, h2, hb => by
    have ih := adj_append R (b :: l1) l2 h1.2 h2 (fun x hx y hy => hb x (by
      simp only [List.getLast?_cons_cons] at hx ⊢; exact hx) y hy)
    exact ⟨h1.1, by simpa using ih⟩

theorem adj_flatMap {α β : Type} (R : α → α → Prop) (RK : β → β → Prop) (f : β → List α) :
    ∀ (Ks : List β), Adj RK Ks → (∀ K ∈ Ks, f K ≠ [] ∧ Adj R (f K)) →
      (∀ K K', RK K K' → ∀ a ∈ (f K).getLast?, ∀ b ∈ (f K').head?, R a b) → Adj R (Ks.flatMap f)
  | [], _, _, _ => trivial
  | [K], _, hf, _ => by simpa using (hf K (by simp)).2
  | K :: K' :: Ks, hA, hf, hb => by
    have ih := adj_flatMap R RK f (K' :: Ks) hA.2 (fun x hx => hf x (by simp [hx])) hb
    rw [List.flatMap_cons]
    apply adj_append R _ _ (hf K (by simp)).2 ih
    intro a ha b hb'
    apply hb K K' hA.1 a ha b
    obtain ⟨c, cs, hc⟩ : ∃ c cs, f K' = c :: cs := by
      cases h : f K' with
      | nil => exact absurd h (hf K' (by simp)).1
      | cons c cs => exact ⟨c, cs, rfl⟩
    simp only [List.flatMap_cons, hc, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hb' ⊢
    exact hb'

/-! ## `UOk` -/

/-- The adjacency `uniqV3` needs between consecutive entries. -/
def RU (a b : UEnt) : Prop :=
  (b.tau = a.tau ∨ b.tau = a.tau + 1) ∧ (b.tau = a.tau → le256 a.bytes ≤ le256 b.bytes)

def RKey (K K' : Key) : Prop :=
  (K'.1 = K.1 ∨ K'.1 = K.1 + 1) ∧ (K'.1 = K.1 → le256 (dig K.2) ≤ le256 (dig K'.2))

theorem adj_const (K : Key) : ∀ (l : List UEnt), (∀ e ∈ l, e.tau = K.1 ∧ e.bytes = dig K.2) → Adj RU l
  | [], _ => trivial
  | [a], _ => trivial
  | a :: b :: l, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    refine ⟨⟨Or.inl (by rw [ha.1, hb.1]), fun _ => by rw [ha.2, hb.2]; exact Nat.le_refl _⟩,
      adj_const K (b :: l) ?_⟩
    intro e he; exact h e (by simp [he])

theorem blk_mem (rs : List Occurrence) (K : Key) (e : UEnt) (he : e ∈ blk rs K) :
    e.tau = K.1 ∧ e.bytes = dig K.2 := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
  have hk : o.key = K := by
    have := (List.mem_filter.mp ho).2
    simpa using this
  simp [occEnt, hk, dig]

/-- Sorted classes with instance coverage step by `0` or `1` and are digest-sorted inside an
instance. -/
theorem sortedKeys_adj (rs : List Occurrence)
    (hcov : ∀ K ∈ keys rs, ∀ τ', τ' ≤ K.1 → ∃ K' ∈ keys rs, K'.1 = τ') :
    Adj RKey (sortedKeys rs) := by
  have hmem : ∀ K, K ∈ sortedKeys rs ↔ K ∈ keys rs := fun K => List.mem_mergeSort
  have hs := List.pairwise_iff_getElem.mp
    (show (sortedKeys rs).Pairwise (fun a b => kle a b = true) from
      List.pairwise_mergeSort kle_trans kle_total (keys rs))
  apply adj_of_get
  intro t ht
  have h1 := hs t (t + 1) (by omega) ht (by omega)
  simp only [kle, decide_eq_true_eq] at h1
  refine ⟨?_, fun heq => by omega⟩
  apply Classical.byContradiction
  intro hne
  obtain ⟨K'', hK'', hτ⟩ := hcov _ ((hmem _).mp (List.getElem_mem ht)) ((sortedKeys rs)[t].1 + 1) (by omega)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem K'').mpr hK'')
  by_cases hit : i ≤ t
  · rcases Nat.lt_or_eq_of_le hit with hlt | heq
    · have := hs i t hi (by omega) hlt
      simp only [kle, decide_eq_true_eq] at this; omega
    · subst heq; omega
  · have hle : t + 1 ≤ i := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have := hs (t + 1) i ht hi hlt
      simp only [kle, decide_eq_true_eq] at this; omega
    · subst heq; omega

theorem uniqBlocks_adj (rs : List Occurrence)
    (hcov : ∀ K ∈ keys rs, ∀ τ', τ' ≤ K.1 → ∃ K' ∈ keys rs, K'.1 = τ') : Adj RU (uniqBlocks rs) := by
  apply adj_flatMap RU RKey (blk rs) (sortedKeys rs) (sortedKeys_adj rs hcov)
  · intro K hK
    refine ⟨?_, adj_const K _ (blk_mem rs K)⟩
    simp only [blk, ne_eq, List.map_eq_nil_iff]
    exact group_nonempty rs K (List.mem_mergeSort.mp hK)
  · intro K K' hKK a ha b hb
    have ha' := blk_mem rs K a (List.mem_of_getLast? ha)
    have hb' := blk_mem rs K' b (List.mem_of_mem_head? hb)
    refine ⟨by rw [ha'.1, hb'.1]; exact hKK.1, fun h => by rw [ha'.2, hb'.2]; exact hKK.2 (by rw [← ha'.1, ← hb'.1]; exact h)⟩

/-- **`UOk` of a class-ordered list** from explicit facts about its occurrences. -/
theorem uniqBlocks_ok (rs : List Occurrence) (hpos : 0 < rs.length) (hcap : rs.length ≤ 2 ^ 17)
    (heid : ∀ o ∈ rs, o.eid < ZkFormal.Algebra.P) (htau : ∀ o ∈ rs, o.key.1 + 1 < ZkFormal.Algebra.P)
    (hcov : ∀ K ∈ keys rs, ∀ τ', τ' ≤ K.1 → ∃ K' ∈ keys rs, K'.1 = τ') : UOk (uniqBlocks rs) := by
  have hp := uniqBlocks_perm rs
  have hlen : (uniqBlocks rs).length = rs.length := by rw [hp.length_eq, List.length_map]
  have hadj := adj_get RU _ (uniqBlocks_adj rs hcov)
  refine ⟨by omega, by omega, ?_, fun t ht => (hadj t ht).1, fun t ht heq => (hadj t ht).2 heq⟩
  intro e he
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp he)
  refine ⟨by simp [occEnt, ArenaCore.sha256_length], ?_, heid o ho, htau o ho⟩
  intro y hy
  simp only [occEnt, List.mem_map] at hy
  obtain ⟨b, -, rfl⟩ := hy
  exact UInt8.toNat_lt b

end ZkFormal.NearV3.Assembly.TrieUniqOk

namespace ZkFormal.NearV3.Assembly.TrieUniqOk

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives StoreClassPartition TrieUniqOcc TrieEnt TrieUniqDup

theorem seedNodesT_root (tau d n v : Nat) (t : PTrie) (hn : isNode t = true) :
    ∃ s ∈ seedNodesT tau d n v t, s.tau = tau := by
  cases t with
  | hash _ => simp [isNode] at hn
  | leaf k s m => exact ⟨seedNodeView tau d n v (.leaf k s m), by simp [seedNodesT], rfl⟩
  | ext k c m => exact ⟨seedNodeView tau d n v (.ext k c m), by simp [seedNodesT], rfl⟩
  | branch sv cs m => exact ⟨seedNodeView tau d n v (.branch sv cs m), by simp [seedNodesT], rfl⟩

theorem seedValuesFrom_length' (v : Nat) (bs : List Bytes) : (seedValuesFrom v bs).length = bs.length := by
  simpa using congrArg List.length (seedValuesFrom_vids v bs)

theorem forestNodes_cover : ∀ (ts : List PTrie) (tau nid vid : Nat), (∀ t ∈ ts, isNode t = true) →
    ∀ τ', tau ≤ τ' → τ' < tau + ts.length → ∃ s ∈ forestNodes tau nid vid ts, s.tau = τ'
  | [], _, _, _, _, τ', h1, h2 => by simp at h2; omega
  | t :: ts, tau, nid, vid, hn, τ', h1, h2 => by
    by_cases he : τ' = tau
    · subst he
      obtain ⟨s, hs, ht⟩ := seedNodesT_root τ' 0 nid vid t (hn t (by simp))
      exact ⟨s, by simp [forestNodes, hs], ht⟩
    · obtain ⟨s, hs, ht⟩ := forestNodes_cover ts (tau + 1) (nid + tsize t) (vid + (valsOf t).length)
        (fun t' h => hn t' (by simp [h])) τ' (by omega) (by simp at h2; omega)
      exact ⟨s, by simp [forestNodes, hs], ht⟩

theorem occsOf_eq (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    occsOf m steps = CombinedStoreOccurrences.allOccurrences (forestNodes 0 0 0 (TrieNative.forest m steps))
      (NativeStoreProvenance.valueTau (TrieNative.forest m steps))
      (seedValuesFrom 0 (forestBytes (TrieNative.forest m steps))) := by
  unfold occsOf CombinedStoreOccurrences.allOccurrences TrieNative.seedNodes TrieNative.seedVals
  rw [nodeOccurrences_initialize]

theorem occsOf_tau (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (hw : ∀ t ∈ TrieNative.forest m steps, t.wf = true) :
    ∀ o ∈ occsOf m steps, o.key.1 < (TrieNative.forest m steps).length := by
  intro o ho
  rw [occsOf_eq] at ho
  have hk := NativeStoreProvenance.combined_keys (TrieNative.forest m steps) hw (List.mem_map.mpr ⟨o, ho, rfl⟩)
  simp only [NativeStoreProvenance.nativeKeys, List.mem_flatMap, List.mem_map] at hk
  obtain ⟨⟨t, i⟩, hti, b, -, hbk⟩ := hk
  rw [← hbk]
  have := List.mem_zipIdx_iff_getElem?.mp hti
  simp only at this
  exact (List.getElem?_eq_some_iff.mp this).1

/-- **`UOk` of the honest `uniqV3` entries from acceptance.** -/
theorem uniqNative_ok {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    UOk (uniqNative m steps) := by
  have hwf := forest_wf hm hv
  have hnode := TrieParent.accepted_forest_isNode hk hw h hm hv
  obtain ⟨hn0, hval⟩ := NativeExecutionUsage.inputs hk hw h (by decide) hm hv
  have hlenF : (TrieNative.forest m steps).length ≤ 32 := by
    obtain ⟨_, _, _, _, _, hcount⟩ := checkD0_native_steps hk hw (by
      have hh := ((relD0a_iff B0 cb wb).mpr h).1
      unfold RelD0 acceptsD0 at hh
      split at hh <;> simp_all)
    have hs := hv.length
    simp only [List.length_zip] at hs
    simp only [TrieNative.forest, List.length_cons, List.length_map]
    omega
  have hrsl : (occsOf m steps).length =
      ((TrieNative.forest m steps).flatMap occs).length + (forestBytes (TrieNative.forest m steps)).length := by
    rw [occsOf_eq]
    simp [CombinedStoreOccurrences.allOccurrences, CombinedStoreOccurrences.nodeOccurrences,
      CombinedStoreOccurrences.valueOccurrences, forest_length, seedValuesFrom_length']
  apply uniqBlocks_ok
  · rw [hrsl]
    have hm0 := hnode m.pre (by simp [TrieNative.forest])
    have : 0 < (occs m.pre).length := by
      cases hp : m.pre with
      | hash _ => rw [hp] at hm0; simp [isNode] at hm0
      | _ => simp [occs]
    simp only [TrieNative.forest, List.flatMap_cons, List.length_append]
    omega
  · rw [hrsl]
    have hc := forest_count _ hwf
    have hb := node_occurrence_byte_sum (TrieNative.forest m steps)
    have hp := checkD0a_preBytes hk hw h hm hv
    simp only [encSum] at hc
    change preBytes (TrieNative.forest m steps) ≤ 2000000 at hp
    omega
  · intro o ho
    exact StoreOccurrenceIds.entity_ids_small _ _ _ hn0.wf hval o ho
  · intro o ho
    have := occsOf_tau m steps hwf o ho
    change o.key.1 + 1 < 2013265921
    omega
  · intro K hK τ' hτ
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ((covers _ _).mp hK)
    have hlt := occsOf_tau m steps hwf o ho
    obtain ⟨s, hs, hst⟩ := forestNodes_cover (TrieNative.forest m steps) 0 0 0 hnode τ' (by omega) (by omega)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    refine ⟨nodeKey (forestNodes 0 0 0 (TrieNative.forest m steps))[i], (covers _ _).mpr ?_, hst⟩
    rw [occsOf_eq]
    apply List.mem_map.mpr
    refine ⟨⟨nodeKey (forestNodes 0 0 0 (TrieNative.forest m steps))[i], eidN i⟩, ?_, rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨((forestNodes 0 0 0 (TrieNative.forest m steps))[i], i), ?_, rfl⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])

end ZkFormal.NearV3.Assembly.TrieUniqOk
