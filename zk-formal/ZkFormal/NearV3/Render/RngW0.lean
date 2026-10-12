import ZkFormal.NearV3.Render.PaddedChacha
import ZkFormal.NearV3.Render.UnfoldA7Ext
import ZkFormal.Chacha.Rng.WordCount

/-!
# ZkFormal.NearV3.Render.RngW0 — the honest `rngV3` render with the A9 word counter

`nearAirV3`'s table 9 is `Rng.Table.table22` = the base stream table (cap 22) extended by the
word counter `w` (col 137) and the 20 bits of `W0 − w` (cols 138..157), `Rng.Table.cW0`.
The honest trace is the aligned base render with those columns filled (`Trace.withCols`):
`w_r` = active rows among `0..r`, the bits = `W0 − (active rows)` (constant).  The active rows
are among the honest draw rows, so **`rngRows calls ≤ W0`** (A9) makes the range check hold.
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table
open ZkFormal.NearV3.Sched ZkFormal.NearV3.UnfoldA7

/-- The honest counter columns of table `t` of `tr`. -/
def rngW0Cols (tr : Trace Fp) (t r col : Nat) : Fp :=
  if col = colW then Fp.ofNat (Rng.activeUpTo tr t r)
  else Fp.ofNat (bt (W0 - Rng.activeRows tr t) (col - 138))

/-- The honest `rngV3` trace with the A9 counter. -/
def rngTraceW0 (calls : List Chacha.Rng.Gen.Call) (t : Nat) : Trace Fp :=
  Trace.withCols (rngTraceAligned calls) t 137 (rngW0Cols (rngTraceAligned calls) t)

/-- The base (cap 22) stream table. -/
def rngBase22 (bc bg : Nat) : ZkFormal.Air.Table := { ZkFormal.Chacha.Rng.Table.table bc bg with maxLog := 22 }

theorem table22_eq (bc bg : Nat) :
    Chacha.Rng.Table.table22 bc bg = extTable (rngBase22 bc bg) widthW0 cW0 [] := by
  simp [Chacha.Rng.Table.table22, extTable, rngBase22, Chacha.Rng.Table.table,
    Chacha.Rng.Table.interactions]

theorem rngBase_colBound : ∀ e ∈ (rngBase22 B_SCHACHA B_SGEN).exprs, e.colBound ≤ 137 := by
  have h : (rngBase22 B_SCHACHA B_SGEN).exprs.all (fun e => decide (e.colBound ≤ 137)) = true := by
    decide +kernel
  intro e he; simpa using List.all_eq_true.1 h e he

section
variable (calls : List Chacha.Rng.Gen.Call) (t : Nat)

theorem rngAligned_cv {r : Nat} (hr : r < (rngTraceAligned calls).height t) (c : Nat) :
    Chacha.cv (rngTraceAligned calls) t r c = Chacha.Rng.Gen.honestCell calls r c % ZkFormal.Algebra.P := by
  unfold Chacha.cv rngTraceAligned
  dsimp only
  rw [rowsTrace_cells (ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (rngRows calls))) _ _
    (fun r c h => rng_cell_ge calls r c h) t r hr c, Fp.toNat_ofNat]

/-- Padding rows are inactive: at most `rngRows calls` active rows. -/
theorem activeUpTo_le_rows : ∀ r, r < (rngTraceAligned calls).height t →
    Rng.activeUpTo (rngTraceAligned calls) t r ≤ rngRows calls
  | 0, h0 => by
    rw [Rng.activeUpTo_zero]
    split
    · rename_i ha
      rcases Nat.eq_zero_or_pos (rngRows calls) with hc | hc
      · have : rngRows calls = 0 := hc
        rw [rngAligned_cv calls t h0] at ha
        unfold Chacha.Rng.Gen.honestCell at ha
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by unfold rngRows at this; omega)] at ha
        simp [Chacha.Rng.Gen.rowCell] at ha
      · omega
    · omega
  | r + 1, h1 => by
    have ih := activeUpTo_le_rows r (by omega)
    have hle := Rng.activeUpTo_le (tr := rngTraceAligned calls) (t := t) r
    rw [Rng.activeUpTo_succ]
    split
    · rename_i ha
      by_cases hR : r + 1 < rngRows calls
      · omega
      · rw [rngAligned_cv calls t h1] at ha
        unfold Chacha.Rng.Gen.honestCell at ha
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by unfold rngRows at hR; omega)] at ha
        simp [Chacha.Rng.Gen.rowCell] at ha
    · omega

theorem activeRows_le_rows : Rng.activeRows (rngTraceAligned calls) t ≤ rngRows calls := by
  have h1 : 1 ≤ (rngTraceAligned calls).height t := Nat.one_le_two_pow
  obtain ⟨h, hh⟩ : ∃ h, (rngTraceAligned calls).height t = h + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  rw [Rng.activeRows_eq hh]
  exact activeUpTo_le_rows calls t h (by omega)

end

/-- **`rngV3` (table 9 of `nearAirV3`) aligned completeness with the A9 counter.** -/
theorem rng_v3_aligned_complete (calls : List Chacha.Rng.Gen.Call)
    (hok : ∀ C ∈ calls, Chacha.Rng.Gen.CallOk C) (hrows : rngRows calls ≤ 2 ^ 22)
    (hW : rngRows calls ≤ W0) (t : Nat) (pub : List Fp) :
    TableLocal (Chacha.Rng.Table.table22 B_SCHACHA B_SGEN) (rngTraceW0 calls t) t pub ∧
    TableTraffic (Chacha.Rng.Table.table22 B_SCHACHA B_SGEN).interactions (rngTraceW0 calls t) t pub
      (rngTraffic calls) ∧
    (rngTraceW0 calls t).log t % 3 = 1 := by
  obtain ⟨hL, hT, hlog⟩ := rng_aligned_complete22 calls hok hrows t pub
  have hL' : TableLocal (rngBase22 B_SCHACHA B_SGEN) (rngTraceAligned calls) t pub := hL
  have hloc : Local Chacha.Rng.Table.constraints (rngTraceAligned calls) t pub :=
    fun r hr e he => hL.constr r hr e he
  have hA := activeRows_le_rows calls t
  have hH : (rngTraceW0 calls t).height t = (rngTraceAligned calls).height t := by rfl
  have hH : (rngTraceW0 calls t).height t = (rngTraceAligned calls).height t := by rfl
  have hH22 : (rngTraceAligned calls).height t ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) hL'.log_le
  -- the cells read by `cW0`
  have cvA : ∀ r, Chacha.cv (rngTraceW0 calls t) t r colA = Chacha.cv (rngTraceAligned calls) t r colA := by
    intro r; unfold Chacha.cv rngTraceW0; rw [cell_withCols_lt (by decide)]
  have cvW : ∀ r, r < (rngTraceAligned calls).height t → Chacha.cv (rngTraceW0 calls t) t r colW = Rng.activeUpTo (rngTraceAligned calls) t r := by
    intro r hr; unfold Chacha.cv rngTraceW0; rw [cell_withCols_ge (by decide)]
    simp only [rngW0Cols, ite_true, Fp.toNat_ofNat]
    have := Rng.activeUpTo_le (tr := (rngTraceAligned calls)) (t := t) r
    exact Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)
  have cvB : ∀ r b, b < 20 → Chacha.cv (rngTraceW0 calls t) t r (colWb b) = bt (W0 - Rng.activeRows (rngTraceAligned calls) t) b := by
    intro r b hb; unfold Chacha.cv rngTraceW0; rw [cell_withCols_ge (by unfold colWb; omega)]
    simp only [rngW0Cols, colWb, colW, show 138 + b ≠ 137 by omega, ite_false, Fp.toNat_ofNat,
      show 138 + b - 138 = b by omega]
    have : bt (W0 - Rng.activeRows (rngTraceAligned calls) t) b ≤ 1 := by unfold bt; omega
    exact Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)
  have aLe : ∀ r, r < (rngTraceAligned calls).height t → Chacha.cv (rngTraceAligned calls) t r colA ≤ 1 := fun r hr =>
    hloc.bool hr (Rng.mem_cB (by unfold Chacha.Rng.Table.boolCols colA; simp only [List.mem_append, List.mem_range'_1]; omega))
  have hAW : Rng.activeRows (rngTraceAligned calls) t ≤ W0 := Nat.le_trans hA hW
  rw [table22_eq]
  refine ⟨tableLocal_withCols hL' rngBase_colBound ?_ (by simp), ?_, hlog⟩
  · intro r hr e he
    change Expr.eval e (rngTraceW0 calls t) t r pub = 0
    apply eval_zero_of
    have hcur : ∀ x, (tenv (rngTraceW0 calls t) t r pub).cur x = Chacha.cv (rngTraceW0 calls t) t r x := fun _ => rfl
    unfold cW0 at he
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨b, hb, rfl⟩ | rfl | rfl | rfl
    · have hx := cvB r b hb
      have hx1 : bt (W0 - Rng.activeRows (rngTraceAligned calls) t) b ≤ 1 := by unfold bt; omega
      simp only [ZkFormal.Chacha.Table.boolC, zev_mul, zev_sub, zev_c, zev_k, hcur, hx]
      rcases (by omega : bt (W0 - Rng.activeRows (rngTraceAligned calls) t) b = 0 ∨ bt (W0 - Rng.activeRows (rngTraceAligned calls) t) b = 1)
        with h0 | h0 <;> rw [h0] <;> simp
    · simp only [zev_mul, zev_isFirst, zev_sub, zev_c, hcur, cvA, cvW r hr]
      by_cases h0 : r = 0
      · subst h0
        have := aLe 0 hr
        rw [Rng.activeUpTo_zero]
        simp only [tenv, ite_true]
        split <;> push_cast <;> omega
      · simp [tenv, h0]
    · by_cases hl : r + 1 = (rngTraceAligned calls).height t
      · have hl1 : (tenv (rngTraceW0 calls t) t r pub).last = 1 := by
          simp only [tenv]; rw [hH, ite_cond_eq_true _ _ (eq_true hl)]
        simp [zev, hl1]
      · have hr1 : r + 1 < (rngTraceW0 calls t).height t := by rw [hH]; omega
        have hnx : ∀ x, (tenv (rngTraceW0 calls t) t r pub).nxt x = Chacha.cv (rngTraceW0 calls t) t (r + 1) x :=
          fun x => nxt_cv hr1 x
        have hl0 : (tenv (rngTraceW0 calls t) t r pub).last = 0 := by
          simp only [tenv]; rw [hH, ite_cond_eq_false _ _ (eq_false hl)]
        simp only [zev, zev_sub, zev_n, zev_c, hcur, hnx, hl0, cvA, cvW r hr, cvW (r + 1) (by omega)]
        rw [Rng.activeUpTo_succ]
        have := aLe (r + 1) (by omega)
        split <;> push_cast <;> omega
    · by_cases hl : r + 1 = (rngTraceAligned calls).height t
      · have hl1 : (tenv (rngTraceW0 calls t) t r pub).last = 1 := by
          simp only [tenv]; rw [hH, ite_cond_eq_true _ _ (eq_true hl)]
        have hnum : zev (tenv (rngTraceW0 calls t) t r pub) (Chacha.Rng.Table.num colWb 20) =
            ((W0 - Rng.activeRows (rngTraceAligned calls) t : Nat) : Int) := by
          rw [Rng.zev_num, Chacha.numv, nbits_congr (fun b hb => cvB r b hb), nbits_bt]
          unfold W0 at hAW ⊢
          rw [Nat.mod_eq_of_lt (by omega)]
        have hw := cvW r hr
        rw [Rng.activeRows_eq (h := r) (by omega)] at hAW hnum
        simp only [zev_mul, zev_sub, zev_k, zev_c, hcur, hl1, hnum, hw]
        push_cast [hAW]
        omega
      · have hl0 : (tenv (rngTraceW0 calls t) t r pub).last = 0 := by
          simp only [tenv]; rw [hH, ite_cond_eq_false _ _ (eq_false hl)]
        simp [zev, hl0]
  · intro b m
    have hw : ∀ i ∈ (rngBase22 B_SCHACHA B_SGEN).interactions, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ 137 :=
      fun i hi e he => rngBase_colBound e (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hi, he⟩))
    simp only [extTable, List.append_nil]
    unfold rngTraceW0
    rw [tableBusCount_withCols _ _ _ _ _ _ hw, tableBusCount_withCols _ _ _ _ _ _ hw]
    exact hT b m

end ZkFormal.NearV3.Render
