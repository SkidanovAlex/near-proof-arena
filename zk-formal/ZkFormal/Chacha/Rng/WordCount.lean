import ZkFormal.Chacha.Rng.Row

/-!
# ZkFormal.Chacha.Rng.WordCount — the A9 word counter of `table22` (soundness view)

`table22` appends the running count `w` of active rows and a 20-bit range check of `W0 − w` on
the last row (`Rng.Table.cW0`).  **`activeRows_le`**: on any trace where `table22`'s constraints
hold (heights `≤ 2^22`), the number of active rows (`a = 1`, one per drawn word) is `≤ W0`.
-/

namespace ZkFormal.Chacha.Rng

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E ZkFormal.Chacha.Rng.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp} {bc bg : Nat}

/-- Active rows among `0..r`. -/
def activeUpTo (tr : Trace Fp) (t r : Nat) : Nat :=
  ((List.range (r + 1)).filter fun r' => cv tr t r' colA = 1).length

/-- Active rows of table `t` (one per drawn word). -/
def activeRows (tr : Trace Fp) (t : Nat) : Nat :=
  ((List.range (tr.height t)).filter fun r => cv tr t r colA = 1).length

theorem activeUpTo_zero : activeUpTo tr t 0 = if cv tr t 0 colA = 1 then 1 else 0 := by
  unfold activeUpTo; split <;> simp_all

theorem activeUpTo_succ (r : Nat) :
    activeUpTo tr t (r + 1) = activeUpTo tr t r + (if cv tr t (r + 1) colA = 1 then 1 else 0) := by
  unfold activeUpTo
  rw [List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

theorem activeUpTo_le (r : Nat) : activeUpTo tr t r ≤ r + 1 := by
  unfold activeUpTo
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem activeRows_eq {h : Nat} (hh : tr.height t = h + 1) : activeRows tr t = activeUpTo tr t h := by
  unfold activeRows activeUpTo; rw [hh]

theorem mem_base22 {e : Expr} (h : e ∈ constraints) : e ∈ (table22 bc bg).constraints :=
  List.mem_append_left _ h

theorem mem_w0 {e : Expr} (h : e ∈ cW0) : e ∈ (table22 bc bg).constraints :=
  List.mem_append_right _ h

section
variable (hL : Local (table22 bc bg).constraints tr t pub)
include hL

theorem a_le {r : Nat} (hr : r < tr.height t) : cv tr t r colA ≤ 1 :=
  hL.bool hr (mem_base22 (mem_cB (by unfold boolCols colA; simp only [List.mem_append, List.mem_range'_1]; omega)))

theorem wb_le {r e : Nat} (hr : r < tr.height t) (he : e < 20) : cv tr t r (colWb e) ≤ 1 :=
  hL.bool hr (mem_w0 (by
    unfold cW0
    exact List.mem_append_left _ (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))

/-- **The counter column is the running count of active rows.** -/
theorem w_eq (hH : tr.height t ≤ 2 ^ 22) : ∀ r, r < tr.height t → cv tr t r colW = activeUpTo tr t r
  | 0, h0 => by
    have he : Expr.mul .isFirst (sub (c colW) (c colA)) ∈ (table22 bc bg).constraints :=
      mem_w0 (by unfold cW0; simp)
    have hv : zev (tenv tr t 0 pub) (Expr.mul .isFirst (sub (c colW) (c colA))) =
        (cv tr t 0 colW : Int) - cv tr t 0 colA := by
      simp [tenv, cv]
    have ha := a_le hL h0
    have hw := cv_lt (tr := tr) (t := t) 0 colW
    have hz := hL.zc h0 he (by rw [hv]; omega) (by rw [hv]; omega)
    rw [hv] at hz
    rw [activeUpTo_zero]
    split <;> omega
  | r + 1, h1 => by
    have ih := w_eq hH r (by omega)
    have he : Expr.mul .isTransition (sub (n colW) (.add (c colW) (n colA))) ∈ (table22 bc bg).constraints :=
      mem_w0 (by unfold cW0; simp)
    have hv : zev (tenv tr t r pub) (Expr.mul .isTransition (sub (n colW) (.add (c colW) (n colA)))) =
        (cv tr t (r + 1) colW : Int) - (cv tr t r colW + cv tr t (r + 1) colA) := by
      have hl : (tenv tr t r pub).last = 0 := by simp [tenv]; omega
      simp only [zev, zev_sub, hl, zev_n, zev_c, nxt_cv h1, cur_cv]
      simp
    have ha := a_le hL h1
    have hw := cv_lt (tr := tr) (t := t) (r + 1) colW
    have hle := activeUpTo_le (tr := tr) (t := t) r
    have hz := hL.zc (show r < tr.height t by omega) he (by rw [hv]; omega) (by rw [hv]; omega)
    rw [hv] at hz
    rw [activeUpTo_succ]
    split <;> omega

/-- **A9 in the AIR**: at most `W0` active rows. -/
theorem activeRows_le (hH : tr.height t ≤ 2 ^ 22) (h1 : 1 ≤ tr.height t) : activeRows tr t ≤ W0 := by
  obtain ⟨h, hh⟩ : ∃ h, tr.height t = h + 1 := ⟨tr.height t - 1, by omega⟩
  have hr : h < tr.height t := by omega
  have hw := w_eq hL hH h hr
  have he : Expr.mul .isLast (sub (num colWb 20) (sub (k W0) (c colW))) ∈ (table22 bc bg).constraints :=
    mem_w0 (by unfold cW0; simp)
  have hv : zev (tenv tr t h pub) (Expr.mul .isLast (sub (num colWb 20) (sub (k W0) (c colW)))) =
      (numv tr t h colWb 20 : Int) - ((W0 : Int) - cv tr t h colW) := by
    have hl : (tenv tr t h pub).last = 1 := by simp [tenv]; omega
    simp only [zev_mul, zev_sub, zev_k, zev_c, cur_cv, zev_num]
    simp only [zev, hl, Int.one_mul]
  have hn := numv_lt (hL := fun r hr e he => hL r hr e (mem_base22 he)) hr
    (col := colWb) (len := 20) (fun b hb => wb_le hL hr hb)
  have hle := activeUpTo_le (tr := tr) (t := t) h
  have hz := hL.zc hr he (by rw [hv]; unfold W0 at *; omega) (by rw [hv]; unfold W0 at *; omega)
  rw [hv] at hz
  rw [activeRows_eq hh, ← hw]
  omega

end

end ZkFormal.Chacha.Rng
