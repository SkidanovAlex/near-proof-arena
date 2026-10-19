import WasmBase.Prelude
/-!
# WasmBase.Bus — from mod-p LogUp balance to lookups and multiset equalities

`Holds` only gives, for each message, equality of the summed counts **mod p**, plus the verifier's
per-bus height bound `busLoad < p`.  When every count on one side of a bus is a bit, the sums are
`< p` and the mod-p equation becomes exact (permutation buses), and a message absent from the
table side cannot be queried (lookups, whatever the table multiplicities).
-/
namespace WasmBase
open ZkFormal.Algebra
set_option linter.unusedSimpArgs false

theorem le_sum_of_mem_nat {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem sum_eq_zero_of_all {l : List Nat} (h : ∀ a ∈ l, a = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.sum_cons]
    rw [h x (List.mem_cons_self), ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem sum_le_length {l : List Nat} (h : ∀ a ∈ l, a ≤ 1) : l.sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.length_cons]
    have := h x (List.mem_cons_self)
    have := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    omega

theorem length_filter_mono {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · simp only [hp, h x hp, ite_true, List.length_cons]; omega
    · simp only [hp, Bool.false_eq_true, ite_false]
      split <;> (try simp only [List.length_cons]) <;> omega

theorem mem_occs {A : Air} {tr : Trace} {pub : List F} {o : Occ} :
    o ∈ occs A tr pub ↔ ∃ t, ∃ ht : t < A.tables.length, ∃ r, r < tr.height t ∧
      ∃ i ∈ (A.tables[t]'ht).inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) := by
  simp only [occs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨T, t⟩, hT, r, hr, i, hi, rfl⟩
    simp only at hT
    have ht : t < A.tables.length := by
      rcases h : A.tables[t]? with _ | T'
      · simp [h] at hT
      · exact (List.getElem?_eq_some_iff.mp h).1
    have hT' : A.tables[t]'ht = T := by
      have := List.getElem?_eq_getElem ht
      rw [hT] at this; exact (Option.some.inj this).symm
    exact ⟨t, ht, r, hr, i, hT' ▸ hi, rfl⟩
  · rintro ⟨t, ht, r, hr, i, hi, rfl⟩
    exact ⟨(A.tables[t]'ht, t), by simp [List.getElem?_eq_getElem ht], r, hr, i, hi, rfl⟩

/-- A matching occurrence's count is at most the bus sum. -/
theorem count_le_busNat {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F}
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = s) (hm : o.2.2.1 = m) :
    o.2.2.2 ≤ busNat A tr pub b s m := by
  unfold busNat
  apply le_sum_of_mem_nat
  exact List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, by simp [hb, hs, hm]⟩, rfl⟩

theorem busNat_zero {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F}
    (h : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = s → o.2.2.1 = m → o.2.2.2 = 0) :
    busNat A tr pub b s m = 0 := by
  unfold busNat
  apply sum_eq_zero_of_all
  intro a ha
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
  obtain ⟨ho, hf⟩ := List.mem_filter.mp ho
  simp only [decide_eq_true_eq] at hf
  exact h o ho hf.1 hf.2.1 hf.2.2

theorem length_filter_flatMap_le {β : Type} (l : List β) (f : β → List Occ) (p : Occ → Bool)
    (g : β → Nat) (h : ∀ x ∈ l, ((f x).filter p).length ≤ g x) :
    ((l.flatMap f).filter p).length ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem length_filter_occs_le (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s).length ≤ busLoad A tr b := by
  unfold occs busLoad
  apply length_filter_flatMap_le
  rintro ⟨T, t⟩ _
  simp only
  have : (List.map (fun _ => (T.inters.filter (·.bus = b)).length) (List.range (tr.height t))).sum =
      tr.height t * (T.inters.filter (·.bus = b)).length := by
    generalize tr.height t = n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Nat.succ_mul]
  rw [← this]
  apply length_filter_flatMap_le
  intro r _
  rw [List.filter_map, List.length_map]
  apply length_filter_mono
  intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq] at hx ⊢
  exact hx.1

/-- Bits on one side of a bus: the summed count of any message is below `p`. -/
theorem busNat_lt {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat) (s : Bool)
    (m : List F) (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = s → o.2.2.2 ≤ 1) :
    busNat A tr pub b s m < P := by
  have h1 : busNat A tr pub b s m ≤ ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length := by
    unfold busNat
    have := sum_le_length (l := ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map (·.2.2.2))
      (by
        intro a ha
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ho, hf⟩ := List.mem_filter.mp ho
        simp only [decide_eq_true_eq] at hf
        exact hbit o ho hf.1 hf.2.1)
    simpa using this
  have h2 : ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length ≤
      ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s).length := by
    apply length_filter_mono
    intro x hx; simp only [decide_eq_true_eq] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have h3 := length_filter_occs_le A tr pub b s
  have h4 := H.busBound b
  omega

/-- **Lookup soundness.** If every table-side (receive) occurrence with a nonzero count carries a
message satisfying `Q`, and query (send) counts are bits, then every query with count 1 satisfies
`Q` — whatever the table multiplicities are. -/
theorem lookup_sound {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (Q : List F → Prop)
    (hrecv : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≠ 0 → Q o.2.2.1)
    (hsend : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    Q o.2.2.1 := by
  refine Classical.byContradiction fun hq => ?_
  have h0 : busNat A tr pub b false o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' => Classical.byContradiction fun hc' => hq (hm' ▸ hrecv o' ho' hb' hs' hc')
  have hbal := H.balance b o.2.2.1
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_lt H b true o.2.2.1 hsend
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

/-- **Permutation buses.** With bit counts on both sides, the mod-p balance is exact. -/
theorem perm_exact {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) (m : List F) :
    busNat A tr pub b true m = busNat A tr pub b false m := by
  have h := H.balance b m
  rwa [Nat.mod_eq_of_lt (busNat_lt H b true m (fun o ho hb _ => hbit o ho hb)),
    Nat.mod_eq_of_lt (busNat_lt H b false m (fun o ho hb _ => hbit o ho hb))] at h

/-- The messages carried with count 1 in direction `s` on bus `b`. -/
def msgs (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) : List (List F) :=
  ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.2 = 1).map (·.2.2.1)

theorem busNat_eq_count {A : Air} {tr : Trace} {pub : List F} (b : Nat) (s : Bool)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = s → o.2.2.2 ≤ 1) (m : List F) :
    busNat A tr pub b s m = (msgs A tr pub b s).count m := by
  unfold busNat msgs
  revert hbit
  generalize occs A tr pub = l
  intro hbit
  induction l with
  | nil => simp
  | cons o l ih =>
    have ih' := ih (fun o' ho' => hbit o' (List.mem_cons_of_mem _ ho'))
    have ho := hbit o List.mem_cons_self
    by_cases p1 : o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m
    · have hc := ho p1.1 p1.2.1
      rw [List.filter_cons_of_pos (by simpa using p1), List.map_cons, List.sum_cons, ih']
      by_cases h3 : o.2.2.2 = 1
      · rw [List.filter_cons_of_pos (by simp [p1.1, p1.2.1, h3]), List.map_cons, List.count_cons, p1.2.2]
        simp [h3]; omega
      · rw [List.filter_cons_of_neg (by simp [h3])]
        omega
    · rw [List.filter_cons_of_neg (by simpa using p1), ih']
      by_cases h3 : o.1 = b ∧ o.2.1 = s ∧ o.2.2.2 = 1
      · rw [List.filter_cons_of_pos (by simpa using h3), List.map_cons, List.count_cons]
        have : o.2.2.1 ≠ m := fun h => p1 ⟨h3.1, h3.2.1, h⟩
        simp [this]
      · rw [List.filter_cons_of_neg (by simpa using h3)]

theorem msgs_perm {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) :
    (msgs A tr pub b true).Perm (msgs A tr pub b false) := by
  rw [List.perm_iff_count]
  intro m
  rw [← busNat_eq_count b true (fun o ho hb _ => hbit o ho hb),
    ← busNat_eq_count b false (fun o ho hb _ => hbit o ho hb)]
  exact perm_exact H b hbit m

end WasmBase
