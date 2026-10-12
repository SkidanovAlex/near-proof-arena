import ZkFormal.NearV3.Rcpt.Link.Mem3

/-!
# ZkFormal.NearV3.Rcpt.Link.MemOf — `MemHyp` from `HoldsP` and the records

* `rv ls` — the flattened receipts as v1 `RcptV`;
* `memW3_eq`, `memR3_eq` — `MemBal`'s lists are `Mem3`'s;
* **`memHyp_of`** — `MemHyp (rv r.lists) r.accts` from `HoldsP nearAirV3`, the exact traffic,
  the views' well-formedness and the distinctness of the account slots (`hknd`; the `VSLOT`
  side of the trie link).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly

/-- The applied receipts as v1 receipt views. -/
def rv (ls : RcptV3Vs) : List RcptV := (flatR ls).map (·.toRcptV)

theorem rv_length (ls : RcptV3Vs) : (rv ls).length = (flatR ls).length := by simp [rv]

theorem R_rv (ls : RcptV3Vs) (r : Nat) : R (rv ls) r = ((flatR ls).getD r default).toRcptV := by
  simp only [R, rv, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (flatR ls)[r]? <;> rfl

theorem zipIdx_flatMap_eq {α β : Type} [Inhabited α] (xs : List α) (f : α × Nat → List β) :
    xs.zipIdx.flatMap f = (List.range xs.length).flatMap fun r => f (xs.getD r default, r) := by
  rw [← LinkRids.zip_range' xs 0, List.flatMap_map]
  simp

theorem memW3_eq (ls : RcptV3Vs) (as : List AcctV) : memW3 ls as = wrs (rv ls) ++ aws as := by
  simp only [memW3, wrs, aws, rv_length, R_rv]
  rw [zipIdx_flatMap_eq]

theorem memR3_eq (ls : RcptV3Vs) (as : List AcctV) : memR3 ls as = rds (rv ls) ++ ars as := by
  simp only [memR3, rds, ars, rv_length, R_rv]
  rw [zipIdx_flatMap_eq]

theorem getD_lt' {l : List Nat} (h : ∀ y ∈ l, y < P) (i : Nat) : l.getD i 0 < P := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp; unfold P; omega
  | some y => exact h y (List.mem_of_getElem? hi)

theorem getElem_flatR_mem {ls : RcptV3Vs} {r : Nat} (hr : r < (flatR ls).length) :
    (flatR ls).getD r default ∈ flatR ls := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem hr

theorem mem_raw_of {x : RcptV} {y : Nat} (h : y ∈ x.bef ∨ y ∈ x.lk ∨ y ∈ x.st) : y ∈ x.raw := by
  unfold RcptV.raw; rcases h with h | h | h <;> simp [h]

theorem mem_raw3_of {x : RcptE} {y : Nat} (h : y ∈ x.raw) : y ∈ x.raw3 := by
  unfold RcptE.raw3; simp [h]

/-- **`MemHyp` from the trace.** -/
theorem memHyp_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) (hknd : (r.accts.map (·.k)).Nodup) :
    MemHyp (rv r.lists) r.accts := by
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hlen : (flatR r.lists).length ≤ 2 ^ 22 := W.listsCount.2
  have hwfR : ∀ q, q < (flatR r.lists).length → ∃ a b c, ((flatR r.lists).getD q default).Wf q a b c := by
    intro q hq
    have := hwf q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact ⟨_, _, _, this⟩
  have hraw : ∀ q, q < (flatR r.lists).length → ∀ y ∈ ((flatR r.lists).getD q default).raw, y < P :=
    fun q hq y hy => W.lists.canon.2 _ (getElem_flatR_mem hq) y (mem_raw3_of hy)
  have hacc : ∀ a ∈ r.accts, (a.k < P ∧ a.tlast < P) ∧ ∀ y ∈ a.pre ++ a.post, y < P := by
    intro a ha
    rcases W.accts with he | hw
    · rw [he] at ha; cases ha
    · exact ⟨⟨(hw.v1.len a ha).2.2.1, (hw.v1.len a ha).2.2.2⟩, hw.v1.canon a ha⟩
  have hlane : ∀ a ∈ r.accts, ∀ (l : List Nat), (∀ y ∈ l, y < P) → ∀ i, ∀ y ∈ acctLane a l i, y < P := by
    intro a ha l hl i y hy
    simp only [acctLane, List.mem_cons, List.not_mem_nil, or_false] at hy
    have hpre : ∀ y ∈ a.pre, y < P := fun y hy => (hacc a ha).2 y (by simp [hy])
    rcases hy with rfl | rfl | rfl
    · exact getD_lt' hl i
    · exact getD_lt' hpre _
    · split
      · exact getD_lt' hpre _
      · unfold P; omega
  refine ⟨?_, hknd, ?_⟩
  · have hp := mem_bal hH T
    rw [memW3_eq, memR3_eq] at hp
    apply perm_nat _ _ hp
    · intro m hm
      rcases mem_W.mp hm with ⟨q, hq, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
      · rw [rv_length] at hq
        obtain ⟨_, _, _, w⟩ := hwfR q hq
        rw [R_rv]
        intro y hy
        simp only [wrMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · exact w.small.1
        · unfold P; omega
        · unfold P; omega
        · exact getD_lt' (fun y hy => by have := w.aft8 y hy; unfold P; omega) i
        · exact getD_lt' (fun y hy => hraw q hq y (mem_raw_of (.inr (.inl hy)))) i
        · exact getD_lt' (fun y hy => hraw q hq y (mem_raw_of (.inr (.inr hy)))) i
      · intro y hy
        simp only [awMsg, List.cons_append, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact (hacc a ha).1.1
        · unfold P; omega
        · unfold P; omega
        · exact hlane a ha _ (fun y hy => (hacc a ha).2 y (by simp [hy])) i y hy
    · intro m hm
      simp only [rds, ars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hm
      rcases hm with ⟨q, hq, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
      · rw [rv_length] at hq
        obtain ⟨_, _, _, w⟩ := hwfR q hq
        rw [R_rv]
        intro y hy
        simp only [rdMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · exact w.small.1
        · exact w.small.2.1
        · unfold P; omega
        · exact getD_lt' (fun y hy => hraw q hq y (mem_raw_of (.inl hy))) i
        · exact getD_lt' (fun y hy => hraw q hq y (mem_raw_of (.inr (.inl hy)))) i
        · exact getD_lt' (fun y hy => hraw q hq y (mem_raw_of (.inr (.inr hy)))) i
      · intro y hy
        simp only [arMsg, List.cons_append, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact (hacc a ha).1.1
        · exact (hacc a ha).1.2
        · unfold P; omega
        · exact hlane a ha _ (fun y hy => (hacc a ha).2 y (by simp [hy])) i y hy
  · intro q hq ht
    rw [rv_length] at hq ht
    obtain ⟨_, _, _, w⟩ := hwfR q hq
    rw [R_rv] at ht ⊢
    exact w.tprev_le (by unfold P; omega)

end ZkFormal.NearV3.RcptLink
