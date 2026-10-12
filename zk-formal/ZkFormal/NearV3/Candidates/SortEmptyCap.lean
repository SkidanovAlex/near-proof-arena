import ZkFormal.NearV3.Candidates.SortEmptySound
import ZkFormal.NearV3.Assembly.NearAir

/-!
# `sortV3` soundness at the `nearAirV3` cap 19 (`sortTableV3 = {SortEmpty.table with maxLog := 19}`)

`SortEmptySound` proves the empty-or-old split for `SortEmpty.table` at its definitional cap
18.  The split never uses the height bound, so it holds at every cap; here it is restated for
`sortTableV3`: a locally legal `sortV3` table is either silent (every bus count `0`: no receipt
ids, the empty-chunk case) or locally legal for the original v1 constraints `Sort.table` at
cap 19 (first row active), to which the v1 segment/sortedness view applies.
-/
namespace ZkFormal.NearV3.Candidates.SortEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra
open ZkFormal.NearV3.Assembly

private theorem replace_eval' (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (h : tr.cell t 0 Sort.act = 1) (e : Expr) :
    (replaceFirst e).eval tr t r pub = e.eval tr t r pub := by
  unfold replaceFirst
  split
  · subst e
    by_cases hr : r = 0
    · subst r; simp [firstSegment, sub, Dsl.not, c, k, Expr.eval, Expr.evalWith, rowEnv, h]; rfl
    · simp [firstSegment, sub, Dsl.not, c, k, Expr.eval, Expr.evalWith, rowEnv, hr]; grind
  · split
    · subst e
      by_cases hr : r = 0
      · subst r; simp [firstFlag, sub, Dsl.not, c, k, Expr.eval, Expr.evalWith, rowEnv, h]; rfl
      · simp [firstFlag, sub, Dsl.not, c, k, Expr.eval, Expr.evalWith, rowEnv, hr]; grind
    · rfl

theorem v3_active_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal sortTableV3 tr t pub) (ha : tr.cell t 0 Sort.act = 1) :
    TableLocal {Sort.table with maxLog := 19} tr t pub := by
  refine ⟨h.log_ge, h.log_le, ?_, h.bits⟩
  intro r hr e he
  have hh := h.constr r hr (replaceFirst e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  rw [replace_eval' tr t r pub ha] at hh
  exact hh

theorem v3_inactive_all (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal sortTableV3 tr t pub) (ha : tr.cell t 0 Sort.act = 0) :
    ∀ r, r < tr.height t → tr.cell t r Sort.act = 0 := by
  intro r
  induction r with
  | zero => intro _; exact ha
  | succ r ih =>
    intro hr
    have hi := ih (by omega)
    let e : Expr := mul3 .isTransition (Dsl.not (c Sort.act)) (n Sort.act)
    have he : e ∈ sortTableV3.constraints := by
      apply List.mem_map.mpr
      refine ⟨e, ?_, ?_⟩
      · simp [e, Sort.constraints]
      · rfl
    have hh := h.constr r (by omega) e he
    simp only [e, mul3, Dsl.not, sub, c, n, k, Expr.eval, Expr.evalWith, rowEnv, hi,
      Nat.mod_eq_of_lt hr, show r + 1 ≠ tr.height t by omega, ite_false] at hh
    grind

theorem v3_inactive_count (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal sortTableV3 tr t pub) (ha : tr.cell t 0 Sort.act = 0)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount sortTableV3.interactions tr t pub bus sd msg = 0 := by
  rw [tableBusCount_eq]
  have hz : (List.range (tr.height t)).flatMap
      (fun r => rowTraffic sortTableV3.interactions tr t r pub bus sd) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have ha := v3_inactive_all tr t pub h ha r (List.mem_range.mp hr)
    simp [sortTableV3, table, Sort.table, Sort.interactions, rowTraffic, recv, Interaction.multNat,
      Interaction.multNat.go, c, Expr.eval, Expr.evalWith, rowEnv, ha]
  rw [hz]
  rfl

/-- **`sortV3` soundness split at cap 19**: silent (no ids) or the v1 sort table. -/
theorem sortV3_empty_or_old (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal sortTableV3 tr t pub) :
    (∀ bus sd msg, tableBusCount sortTableV3.interactions tr t pub bus sd msg = 0) ∨
      TableLocal {Sort.table with maxLog := 19} tr t pub := by
  have hb := h.bits 0 (Nat.two_pow_pos _) (recv B_RIDS (c Sort.act) [c Sort.rr, c Sort.i, c Sort.bb])
    (by simp [sortTableV3, table, Sort.table, Sort.interactions]) (c Sort.act) (by simp [recv])
  change tr.cell t 0 Sort.act = 0 ∨ tr.cell t 0 Sort.act = 1 at hb
  rcases hb with hb | hb
  · exact Or.inl (v3_inactive_count tr t pub h hb)
  · exact Or.inr (v3_active_local tr t pub h hb)

/-- The v1 constraints at cap 19 imply the repaired ones (completeness transfer). -/
theorem v3_old_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal {Sort.table with maxLog := 19} tr t pub) : TableLocal sortTableV3 tr t pub := by
  have ha : tr.cell t 0 Sort.act = 1 := by
    have hr : 0 < tr.height t := Nat.two_pow_pos _
    have hs := h.constr 0 hr firstSegment (by simp [Sort.table, Sort.constraints, firstSegment])
    have hf := h.constr 0 hr (.mul (c Sort.sf) (Dsl.not (c Sort.act))) (by simp [Sort.table, Sort.constraints])
    simp only [firstSegment, Dsl.not, sub, k, c, Expr.eval, Expr.evalWith, rowEnv] at hs hf
    grind
  refine ⟨h.log_ge, h.log_le, ?_, h.bits⟩
  intro r hr e he
  change e ∈ Sort.constraints.map replaceFirst at he
  obtain ⟨e', hm, heq⟩ := List.mem_map.mp he
  rw [← heq, replace_eval' tr t r pub ha]
  exact h.constr r hr e' hm

end ZkFormal.NearV3.Candidates.SortEmpty
