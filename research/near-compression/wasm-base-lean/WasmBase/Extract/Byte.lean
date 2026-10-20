import WasmBase.Extract.Row
import WasmBase.Extract.Bits
/-!
# WasmBase.Extract.Byte — the BYTE table is exactly all byte pairs with their and/or/xor
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

theorem cast_and_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a : F) * (b : F) = ((a &&& b : Nat) : F) := by
  rw [and_bit ha hb, Lean.Grind.Semiring.natCast_mul]

theorem cast_or_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a : F) + (b : F) - (a : F) * (b : F) = ((a ||| b : Nat) : F) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
  rfl

theorem cast_xor_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a : F) + (b : F) - ((2 : Nat) : F) * (a : F) * (b : F) = ((a ^^^ b : Nat) : F) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
  rfl

/-- `Σ 2^i · c_i` (as produced by the BYTE expressions) is the cast of `bits8`. -/
theorem cast_bits8 (x : Nat → Nat) :
    ((0 : Nat) : F) + ((1 : Nat) : F) * (x 0 : F) + ((2 : Nat) : F) * (x 1 : F) + ((4 : Nat) : F) * (x 2 : F) +
      ((8 : Nat) : F) * (x 3 : F) + ((16 : Nat) : F) * (x 4 : F) + ((32 : Nat) : F) * (x 5 : F) +
      ((64 : Nat) : F) * (x 6 : F) + ((128 : Nat) : F) * (x 7 : F) = ((bits8 x : Nat) : F) := by
  simp only [bits8, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  grind

theorem byte_bits {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = Byte.table) {r : Nat} (hr : r < tr.height t) :
    ∀ i, i < 16 → rowNat tr t r i ≤ 1 := by
  intro i hi
  have hc := table_constr H ht hr
  rw [hT] at hc
  have := hc (Chips.bool (v i)) (by
    simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨i, hi, rfl⟩)
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at this
  rcases bool_nat (rowNat_lt _ _ _ _) this with h | h <;> omega

def byteKey (tr : Trace) (t r : Nat) : Nat :=
  bits8 (fun i => rowNat tr t r i) + 256 * bits8 (fun i => rowNat tr t r (8 + i))

theorem byte_key_eval (tr : Trace) (pub : List F) (t r : Nat) :
    Byte.key.eval (natRow (rowNat tr t r) (tr.row pub t r)) = ((byteKey tr t r : Nat) : F) := by
  simp only [Byte.key, Byte.X, Byte.Y, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
    Expr.eval_mul', Expr.eval_c, Expr.eval_col, natRow, v, Byte.xb, Byte.yb, Nat.reducePow, Nat.reduceAdd,
    Expr.eval_ofNat']
  rw [cast_bits8 (fun i => rowNat tr t r i), show ((0 : Nat) : F) + ((1 : Nat) : F) * (rowNat tr t r 8 : F) +
      ((2 : Nat) : F) * (rowNat tr t r 9 : F) + ((4 : Nat) : F) * (rowNat tr t r 10 : F) +
      ((8 : Nat) : F) * (rowNat tr t r 11 : F) + ((16 : Nat) : F) * (rowNat tr t r 12 : F) +
      ((32 : Nat) : F) * (rowNat tr t r 13 : F) + ((64 : Nat) : F) * (rowNat tr t r 14 : F) +
      ((128 : Nat) : F) * (rowNat tr t r 15 : F) = ((bits8 fun i => rowNat tr t r (8 + i) : Nat) : F) from
      cast_bits8 (fun i => rowNat tr t r (8 + i))]
  simp only [byteKey, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

theorem byte_rows {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = Byte.table) :
    tr.height t = 65536 ∧ ∀ r, r < tr.height t → byteKey tr t r = r := by
  have hc := fun r (hr : r < tr.height t) => table_constr H ht (r := r) hr
  rw [hT] at hc
  have hh := H.heightLe t ht
  have hpos := H.heightPos t ht
  unfold maxLogHeight at hh
  have hP' := P_val
  have hkl : ∀ r, r < tr.height t → byteKey tr t r < 65536 := by
    intro r hr
    have hb := byte_bits H ht hT hr
    have h1 := bits8_lt (fun i => rowNat tr t r i) (fun i hi => hb i (by omega))
    have h2 := bits8_lt (fun i => rowNat tr t r (8 + i)) (fun i hi => hb (8 + i) (by omega))
    simp only [byteKey]; omega
  have hv : ∀ r, r < tr.height t → byteKey tr t r = r := by
    intro r
    induction r with
    | zero =>
      intro h0
      have := hc 0 h0 (.first * Byte.key) (by simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_cons]; simp)
      simp only [Expr.eval_mul'] at this
      rw [byte_key_eval tr pub t 0] at this
      simp only [Expr.eval, natRow, Trace.row, beq_self_eq_true, ite_true] at this
      exact natEq (by rw [show ((0 : Nat) : F) = 0 from rfl]; grind) (by have := hkl 0 h0; omega) (by decide)
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      have := hc r (by omega) (.trans * (Byte.nkey - Byte.key - 1)) (by simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_cons]; simp)
      have hne : (r + 1 == tr.height t) = false := by simp; omega
      have hk := byte_key_eval tr pub t r
      simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at this
      rw [hk] at this
      have hk1 := byte_key_eval tr pub t (r + 1)
      have hn : Byte.nkey.eval (natRow (rowNat tr t r) (tr.row pub t r)) =
          Byte.key.eval (natRow (rowNat tr t (r + 1)) (tr.row pub t (r + 1))) := by
        simp only [Byte.nkey, Byte.key, Byte.X, Byte.Y, List.range, List.range.loop, List.map, List.foldl,
          Expr.eval_add', Expr.eval_mul', Expr.eval_c, Expr.eval_col, Expr.eval_nxt, natRow, v, nv, Byte.xb,
          Byte.yb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat', Trace.row, Nat.mod_eq_of_lt hr, rowNat,
          Fp.cast_toNat]
      rw [hn, hk1] at this
      simp only [Expr.eval, natRow, Trace.row, hne, Bool.false_eq_true, ite_false] at this
      have e : ((byteKey tr t (r + 1) : Nat) : F) = ((r + 1 : Nat) : F) := by
        rw [ih'] at this; rw [Lean.Grind.Semiring.natCast_add]; grind
      exact natEq e (by have := hkl (r + 1) hr; omega) (by omega)
  refine ⟨?_, hv⟩
  have := hc (tr.height t - 1) (by omega) (.last * (Byte.key - 65535)) (by simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_cons]; simp)
  have hk := byte_key_eval tr pub t (tr.height t - 1)
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at this
  rw [hk] at this
  simp only [Expr.eval, natRow, Trace.row, show tr.height t - 1 + 1 = tr.height t by omega,
    beq_self_eq_true, ite_true] at this
  have e : ((byteKey tr t (tr.height t - 1) : Nat) : F) = ((65535 : Nat) : F) := by grind
  have := natEq e (by have := hkl (tr.height t - 1) (by omega); omega) (by decide)
  have hv' := hv (tr.height t - 1) (by omega)
  omega

end WasmBase
