import WasmBase.Bus
import WasmBase.Local.Add
/-!
# WasmBase.Extract.Row — rows of a `wasmBaseAir` trace as natural-number cells
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

/-- The natural-number cells of row `r` of table `t`. -/
def rowNat (tr : Trace) (t r : Nat) : Nat → Nat := fun i => (tr.cell t r i).toNat

theorem rowNat_lt (tr : Trace) (t r i : Nat) : rowNat tr t r i < P := (tr.cell t r i).toNat_lt

theorem row_eq_natRow (tr : Trace) (pub : List F) (t r : Nat) :
    tr.row pub t r = natRow (rowNat tr t r) (tr.row pub t r) := by
  simp only [natRow, rowNat, Trace.row, Fp.cast_toNat]

theorem table_constr {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) {r : Nat} (hr : r < tr.height t) :
    ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro e he
  rw [← row_eq_natRow]
  exact H.constr t ht r hr e he

section
variable (nloc ncode : Nat)
theorem air_len : (wasmBaseAir nloc ncode).tables.length = 12 := rfl
theorem air_t0 : (wasmBaseAir nloc ncode).tables[0]'(by simp [air_len]) = Boundary.table nloc ncode := rfl
theorem air_t1 : (wasmBaseAir nloc ncode).tables[1]'(by simp [air_len]) = Add.table := rfl
theorem air_t2 : (wasmBaseAir nloc ncode).tables[2]'(by simp [air_len]) = Bit.table := rfl
theorem air_t3 : (wasmBaseAir nloc ncode).tables[3]'(by simp [air_len]) = Mul.table := rfl
theorem air_t4 : (wasmBaseAir nloc ncode).tables[4]'(by simp [air_len]) = Shift.table := rfl
theorem air_t5 : (wasmBaseAir nloc ncode).tables[5]'(by simp [air_len]) = Cmp.table := rfl
theorem air_t6 : (wasmBaseAir nloc ncode).tables[6]'(by simp [air_len]) = Const.table := rfl
theorem air_t7 : (wasmBaseAir nloc ncode).tables[7]'(by simp [air_len]) = Stack.table := rfl
theorem air_t8 : (wasmBaseAir nloc ncode).tables[8]'(by simp [air_len]) = Ctrl.table := rfl
theorem air_t9 : (wasmBaseAir nloc ncode).tables[9]'(by simp [air_len]) = Local.table := rfl
theorem air_t10 : (wasmBaseAir nloc ncode).tables[10]'(by simp [air_len]) = Range16.table := rfl
theorem air_t11 : (wasmBaseAir nloc ncode).tables[11]'(by simp [air_len]) = Byte.table := rfl
end

/-! ## The RANGE16 table is exactly `0 .. 2^16 - 1` -/

theorem range16_values {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = Range16.table) :
    tr.height t = 65536 ∧ ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
  have hc := fun r hr => table_constr H ht (r := r) hr
  rw [hT] at hc
  have hh := H.heightLe t ht
  have hpos := H.heightPos t ht
  unfold maxLogHeight at hh
  have hP' := P_val
  -- v_r = r by induction
  have hv : ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
    simp only [Range16.val]
    intro r
    induction r with
    | zero =>
      intro h0
      have := hc 0 h0 (.first * v Range16.val) (by simp [Range16.table, Range16.constraints])
      simp only [Expr.eval, natRow, Trace.row, v, Range16.val, beq_self_eq_true, ite_true] at this
      exact natEq (by rw [show ((0 : Nat) : F) = 0 from rfl]; grind) (rowNat_lt _ _ _ _) (by decide)
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      have := hc r (by omega) (.trans * (nv Range16.val - v Range16.val - 1))
        (by simp [Range16.table, Range16.constraints])
      have hne : (r + 1 == tr.height t) = false := by simp; omega
      simp only [Expr.eval, Expr.eval_sub', Expr.eval_nxt, Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, nv, Range16.val, Nat.mod_eq_of_lt hr, hne,
        Bool.false_eq_true, ite_false] at this
      have e : (tr.cell t (r + 1) 0) = ((r + 1 : Nat) : F) := by
        have h1 : ((rowNat tr t r 0 : Nat) : F) = (r : F) := by rw [ih']
        simp only [rowNat, Fp.cast_toNat] at h1
        rw [Lean.Grind.Semiring.natCast_add, ← h1]
        grind
      have := congrArg Fp.toNat e
      rw [Fp.toNat_cast_of_lt (by omega)] at this
      exact this
  refine ⟨?_, hv⟩
  have := hc (tr.height t - 1) (by omega) (.last * (v Range16.val - 65535))
    (by simp [Range16.table, Range16.constraints])
  simp only [Expr.eval, Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, Range16.val, show tr.height t - 1 + 1 = tr.height t by omega,
    beq_self_eq_true, ite_true] at this
  have hv' := hv (tr.height t - 1) (by omega)
  have e : ((rowNat tr t (tr.height t - 1) 0 : Nat) : F) = ((65535 : Nat) : F) := by grind
  have := natEq e (rowNat_lt _ _ _ _) (by decide)
  simp only [Range16.val] at hv'
  omega

end WasmBase
