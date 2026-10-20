import WasmBase.Prelude
/-!
# WasmBase.Channel — soundness of the value channel (P-PERF-5, stack temporaries and locals)

Events `k = 0 .. n-1` execute at times `k + 1`.  Event `k` consumes the messages `cons[k]` (each
with producer time `< k + 1`, range-checked in the AIR) and produces `prod[k]` (producer time
`k + 1`); the boundary produces `init` (time 0) and consumes `fin` at the end.  The channel bus
gives `init ++ flatten prod ~ fin ++ flatten cons`, and produced messages are pairwise distinct
(their `(space, slot, time)` differ).

`live k x` := `x` produced before time `k + 1` and not consumed before.  Then: everything event `k`
consumes is live (no message is consumed twice, none before it is produced); liveness evolves as
`live (k+1) = (live k \ cons k) ∪ prod k`; and at the end the live set is exactly `fin`.
This is the "Hall's condition" argument sketched in PERF P-PERF-5, here a theorem.
-/
namespace WasmBase
set_option linter.unusedSimpArgs false

variable {α : Type}

def prodBefore (init : List α) (prod : List (List α)) (k : Nat) : List α := init ++ (prod.take k).flatten
def consBefore (cons : List (List α)) (k : Nat) : List α := (cons.take k).flatten

def live (init : List α) (prod cons : List (List α)) (k : Nat) (x : α) : Prop :=
  x ∈ prodBefore init prod k ∧ x ∉ consBefore cons k

structure ChanOK (init fin : List α) (prod cons : List (List α)) (tp : α → Nat) : Prop where
  len : prod.length = cons.length
  perm : (init ++ prod.flatten).Perm (fin ++ cons.flatten)
  nodup : (init ++ prod.flatten).Nodup
  initTp : ∀ x ∈ init, tp x = 0
  prodTp : ∀ k (hk : k < prod.length), ∀ x ∈ prod[k], tp x = k + 1
  consTp : ∀ k (hk : k < cons.length), ∀ x ∈ cons[k], tp x < k + 1

theorem mem_flatten_iff {L : List (List α)} {x : α} :
    x ∈ L.flatten ↔ ∃ j, ∃ hj : j < L.length, x ∈ L[j] := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hx⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
    exact ⟨j, hj, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨L[j], List.getElem_mem hj, hx⟩

theorem mem_flatten_take {L : List (List α)} {k : Nat} {x : α} :
    x ∈ (L.take k).flatten ↔ ∃ j, ∃ hj : j < L.length, j < k ∧ x ∈ L[j] := by
  rw [mem_flatten_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    simp only [List.length_take] at hj
    exact ⟨j, by omega, by omega, by simpa using hx⟩
  · rintro ⟨j, hj, hjk, hx⟩
    exact ⟨j, by simp; omega, by simpa using hx⟩

/-- In a duplicate-free flattening, an element lies in at most one block. -/
theorem nodup_flatten_unique {L : List (List α)} (h : L.flatten.Nodup) {x : α} {j k : Nat}
    (hj : j < L.length) (hk : k < L.length) (hxj : x ∈ L[j]) (hxk : x ∈ L[k]) : j = k := by
  induction L generalizing j k with
  | nil => simp at hj
  | cons l L ih =>
    simp only [List.flatten_cons, List.nodup_append] at h
    obtain ⟨_, h2, h3⟩ := h
    cases j with
    | zero =>
      cases k with
      | zero => rfl
      | succ k =>
        exfalso
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hxj hxk
        exact h3 x hxj x (mem_flatten_iff.mpr ⟨k, by simpa using hk, hxk⟩) rfl
    | succ j =>
      cases k with
      | zero =>
        exfalso
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hxj hxk
        exact h3 x hxk x (mem_flatten_iff.mpr ⟨j, by simpa using hj, hxj⟩) rfl
      | succ k =>
        simp only [List.getElem_cons_succ] at hxj hxk
        have := ih h2 (by simpa using hj) (by simpa using hk) hxj hxk
        omega

variable {init fin : List α} {prod cons : List (List α)} {tp : α → Nat}

theorem ChanOK.cons_nodup (C : ChanOK init fin prod cons tp) : (fin ++ cons.flatten).Nodup :=
  C.perm.nodup_iff.mp C.nodup

/-- Everything event `k` consumes is live at time `k`. -/
theorem ChanOK.consumed_live (C : ChanOK init fin prod cons tp) {k : Nat} (hk : k < cons.length)
    {x : α} (hx : x ∈ cons[k]) : live init prod cons k x := by
  constructor
  · have hxc : x ∈ fin ++ cons.flatten := List.mem_append_right _ (mem_flatten_iff.mpr ⟨k, hk, hx⟩)
    have hxp := C.perm.symm.subset hxc
    rcases List.mem_append.mp hxp with h | h
    · exact List.mem_append_left _ h
    · obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp h
      have t1 := C.prodTp j hj x hxj
      have t2 := C.consTp k hk x hx
      exact List.mem_append_right _ (mem_flatten_take.mpr ⟨j, hj, by omega, hxj⟩)
  · intro hb
    obtain ⟨j, hj, hjk, hxj⟩ := mem_flatten_take.mp hb
    have hnd := (List.nodup_append.mp C.cons_nodup).2.1
    have := nodup_flatten_unique hnd hj hk hxj hx
    omega

/-- Liveness after event `k`. -/
theorem ChanOK.live_succ (C : ChanOK init fin prod cons tp) {k : Nat} (hk : k < cons.length) (x : α) :
    live init prod cons (k + 1) x ↔
      (live init prod cons k x ∧ x ∉ cons[k]) ∨ x ∈ prod[k]'(by rw [C.len]; exact hk) := by
  have hkp : k < prod.length := by rw [C.len]; exact hk
  simp only [live, prodBefore, consBefore, List.take_succ, List.getElem?_eq_getElem hkp,
    List.getElem?_eq_getElem hk, Option.toList_some, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.mem_append, ← List.append_assoc]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · left; exact ⟨⟨h1, fun h => h2 (Or.inl h)⟩, fun h => h2 (Or.inr h)⟩
    · right; exact h1
  · rintro (⟨⟨h1, h2⟩, h3⟩ | h1)
    · exact ⟨Or.inl h1, fun h => h.elim h2 h3⟩
    · refine ⟨Or.inr h1, ?_⟩
      have t := C.prodTp k hkp x h1
      rintro (h | h)
      · obtain ⟨j, hj, hjk, hxj⟩ := mem_flatten_take.mp h
        have := C.consTp j hj x hxj; omega
      · have := C.consTp k hk x h; omega

/-- At the end, the live messages are exactly the boundary's final consumptions. -/
theorem ChanOK.live_final (C : ChanOK init fin prod cons tp) (x : α) :
    live init prod cons cons.length x ↔ x ∈ fin := by
  simp only [live, prodBefore, consBefore, List.take_length, ← C.len]
  rw [C.len, List.take_length]
  constructor
  · rintro ⟨h1, h2⟩
    rcases List.mem_append.mp (C.perm.subset h1) with h | h
    · exact h
    · exact absurd h h2
  · intro hx
    refine ⟨C.perm.symm.subset (List.mem_append_left _ hx), fun h => ?_⟩
    exact (List.nodup_append.mp C.cons_nodup).2.2 x hx x h rfl

end WasmBase
