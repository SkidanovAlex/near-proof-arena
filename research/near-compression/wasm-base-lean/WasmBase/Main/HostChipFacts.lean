import WasmBase.Main.RowHostSpec
import WasmBase.Main.ExecHost
import WasmBase.StepHost

/-!
# WasmBase.Main.HostChipFacts — an inactive HOST row emits nothing

`results/pq-host-gas/RESULTS.md` §3.3 records a real constraint gap that commit `edae7a53d` closed:
the HOST row's CH interactions are counted with `pf j` / `nres`, and `Host.constraints` had no
`act`–`pf` link, so an **inactive** HOST row (`act = 0`, `pf 0 = 1`) still emitted count-1 CH
receives.  The base `ChipFacts.inactive` premise therefore did not hold for table 22, which is the
premise `Exec`'s bus decomposition needs.

`edae7a53d` added `(1 − act)·pf j = 0` and `(1 − act)·nres = 0`.  This file proves the consequence:
on an inactive HOST row the row's `cons` and `prod` are both empty, so every CH interaction of that
row has count 0.  That is exactly the table-22 instance of `ChipFacts.inactive`, and it is a
prerequisite for re-running `exec_of_rows` on `wasmBaseHostAir`.

The second prerequisite (threading `S_seg`/`segb` through the induction) is *not* attempted here;
`Main/Host.lean` states it.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- **An inactive HOST row emits nothing.**  From `Holds` plus the `act`-gating constraints: `act`
is a bit and `rowAct` false means `act ≠ 1`, hence `act = 0`, and then `(1 − act)·pf j = 0` (for every
`j < nArgs`) and `(1 − act)·nres = 0` force `pf j = 0` and `nres = 0`.  With `host_row_cons` /
`host_row_prod` the row's `cons` and `prod` are empty. -/
theorem host_row_inactive_emits_nothing {nloc ngl : Nat} {pub : List F} {tr : Trace} {r : Nat}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hr : r < tr.height 22)
    (hneg : ¬ rowAct Host.table tr pub 22 r) :
    rowCons Host.table tr pub 22 r = [] ∧ rowProd Host.table tr pub 22 r = [] := by
  have ht : 22 < (wasmBaseHostAir nloc ngl).tables.length := by simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hbA := hcon Host.cAct host_cAct_mem
  have hgR := hcon Host.cActNres host_cActNres_mem
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col,
    Expr.eval_ofNat', natRow, Host.act, Host.nres, Host.cAct, Host.cActNres] at hbA hgR
  -- `act` is a bit; `rowAct` false means `act ≠ 1`; hence `act = 0`
  have hactNe : rowNat tr 22 r Host.act ≠ 1 := by
    intro hv
    exact hneg (by
      simp only [rowAct, Host.table, Host.inters, stateIn, List.cons_append, List.getD_cons_zero,
        Chips.v, Expr.eval_col, Trace.row, rowNat]
      exact hv)
  have hact0 : rowNat tr 22 r Host.act = 0 := by
    have hb := bool_nat (rowNat_lt tr 22 r Host.act) hbA
    rcases hb with h | h
    · exact h
    · exact absurd h hactNe
  -- `1 - act = 1` as a field element once `act = 0`
  have hactIdx : rowNat tr 22 r 5 = 0 := by simpa [Host.act] using hact0
  have hone : ((1 : Nat) : F) - (rowNat tr 22 r 5 : F) = 1 := by rw [hactIdx]; rfl
  have hnrF : (rowNat tr 22 r Host.nres : F) = 0 := by
    rw [hone, Lean.Grind.Semiring.one_mul] at hgR; exact hgR
  have hnr : rowNat tr 22 r Host.nres = 0 :=
    (cast_inj_iff (rowNat_lt tr 22 r Host.nres) (by decide : (0 : Nat) < P)).mp hnrF
  have hpf0 : ∀ j, j ∈ Host.argRange → rowNat tr 22 r (Host.pf j) = 0 := by
    intro j hj
    have h := hcon (Host.cActPf j) (host_cActPf_mem j (argRange_lt hj))
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
      Host.act, Host.cActPf] at h
    rw [hone, Lean.Grind.Semiring.one_mul] at h
    exact (cast_inj_iff (rowNat_lt tr 22 r (Host.pf j)) (by decide : (0 : Nat) < P)).mp h
  refine ⟨?_, ?_⟩
  · exact host_row_cons_inactive (fun j hj => hpf0 j hj)
  · rw [host_row_prod, hnr]
    simp

end WasmBase
