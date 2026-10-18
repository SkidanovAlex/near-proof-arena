import WasmBase.Prelude
import WasmBase.Chips
import NearSpecV3.Wasm.Numerics
/-!
# Local soundness of ADD (i32/i64 add, sub)

From the ADD constraints on one active row, the 16-bit range facts of the operand limbs
(channel invariant) and of the result limbs (RANGE16 lookups), the produced value is exactly
`Num.binop w k a b` of the spec (`k = 0` add, `k = 1` sub).
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm


/-- The row environment of a row given by natural-number cells. -/
def natRow (c : Nat → Nat) (rw : Row) : Row := { rw with cur := fun i => (c i : F) }

theorem add_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Add.constraints, e.eval (natRow c rw) = 0)
    (hact : c Add.fAdd + c Add.fSub = 1)
    (ha : ∀ i, i < 4 → c (Add.a + i) < 65536) (hb : ∀ i, i < 4 → c (Add.b + i) < 65536)
    (hr : ∀ i, i < 4 → c (Add.r + i) < 65536) :
    (c Add.is64 = 0 ∨ c Add.is64 = 1) ∧
    (c Add.is64 = 0 → c (Add.a + 2) = 0 ∧ c (Add.a + 3) = 0 ∧ c (Add.b + 2) = 0 ∧ c (Add.b + 3) = 0 ∧
      c (Add.r + 2) = 0 ∧ c (Add.r + 3) = 0) ∧
    Num.binop (32 + 32 * c Add.is64) (c Add.fSub)
      (val4 (c Add.a) (c (Add.a + 1)) (c (Add.a + 2)) (c (Add.a + 3)))
      (val4 (c Add.b) (c (Add.b + 1)) (c (Add.b + 2)) (c (Add.b + 3))) =
      some (val4 (c Add.r) (c (Add.r + 1)) (c (Add.r + 2)) (c (Add.r + 3))) := by
  simp only [Add.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, Add.X, Add.Z, v, B16, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow, Nat.add_zero] at hc
  obtain ⟨bA, bS, b64, hAS, za2, za3, zb2, zb3, zr2, zr3, bc0, bc1, bc2, bc3, zc2, zc3, e0, e1, e2, e3⟩ := hc
  have a0 := ha 0 (by decide); have a1 := ha 1 (by decide); have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide); have b0 := hb 0 (by decide); have b1 := hb 1 (by decide)
  have b2 := hb 2 (by decide); have b3 := hb 3 (by decide); have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide); have r2 := hr 2 (by decide); have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at a0 b0 r0
  have hP' := P_val
  have cb0 := bool_nat (hP _) bc0; have cb1 := bool_nat (hP _) bc1
  have cb2 := bool_nat (hP _) bc2; have cb3 := bool_nat (hP _) bc3
  refine ⟨bool_nat (hP _) b64, ?_⟩
  rcases bool_nat (hP _) b64 with w | w <;>
  rcases (show (c Add.fAdd = 1 ∧ c Add.fSub = 0) ∨ (c Add.fAdd = 0 ∧ c Add.fSub = 1) by omega)
    with ⟨fa, fs⟩ | ⟨fa, fs⟩ <;>
  simp only [w, fa, fs] at e0 e1 e2 e3 za2 za3 zb2 zb3 zr2 zr3 ⊢
  · -- i32 add
    have := zero_of_sel0 (hP _) za2; have := zero_of_sel0 (hP _) za3; have := zero_of_sel0 (hP _) zb2
    have := zero_of_sel0 (hP _) zb3; have := zero_of_sel0 (hP _) zr2; have := zero_of_sel0 (hP _) zr3
    have E0 : c Add.a + c Add.b = c Add.r + 65536 * c Add.cy := natEq (by fp_ring) (by omega) (by omega)
    have E1 : c (Add.a + 1) + c (Add.b + 1) + c Add.cy = c (Add.r + 1) + 65536 * c (Add.cy + 1) :=
      natEq (by fp_ring) (by omega) (by omega)
    refine ⟨fun _ => by omega, ?_⟩
    simp only [Num.binop, val4, Option.some.injEq]
    omega
  · -- i32 sub
    have := zero_of_sel0 (hP _) za2; have := zero_of_sel0 (hP _) za3; have := zero_of_sel0 (hP _) zb2
    have := zero_of_sel0 (hP _) zb3; have := zero_of_sel0 (hP _) zr2; have := zero_of_sel0 (hP _) zr3
    have E0 : c Add.r + c Add.b = c Add.a + 65536 * c Add.cy := natEq (by fp_ring) (by omega) (by omega)
    have E1 : c (Add.r + 1) + c (Add.b + 1) + c Add.cy = c (Add.a + 1) + 65536 * c (Add.cy + 1) :=
      natEq (by fp_ring) (by omega) (by omega)
    refine ⟨fun _ => by omega, ?_⟩
    simp only [Num.binop, val4, Option.some.injEq]
    omega
  · -- i64 add
    have E0 : c Add.a + c Add.b = c Add.r + 65536 * c Add.cy := natEq (by fp_ring) (by omega) (by omega)
    have E1 : c (Add.a + 1) + c (Add.b + 1) + c Add.cy = c (Add.r + 1) + 65536 * c (Add.cy + 1) :=
      natEq (by fp_ring) (by omega) (by omega)
    have E2 : c (Add.a + 2) + c (Add.b + 2) + c (Add.cy + 1) = c (Add.r + 2) + 65536 * c (Add.cy + 2) :=
      natEq (by fp_ring) (by omega) (by omega)
    have E3 : c (Add.a + 3) + c (Add.b + 3) + c (Add.cy + 2) = c (Add.r + 3) + 65536 * c (Add.cy + 3) :=
      natEq (by fp_ring) (by omega) (by omega)
    refine ⟨fun h => absurd h (by decide), ?_⟩
    simp only [Num.binop, val4, Option.some.injEq]
    omega
  · -- i64 sub
    have E0 : c Add.r + c Add.b = c Add.a + 65536 * c Add.cy := natEq (by fp_ring) (by omega) (by omega)
    have E1 : c (Add.r + 1) + c (Add.b + 1) + c Add.cy = c (Add.a + 1) + 65536 * c (Add.cy + 1) :=
      natEq (by fp_ring) (by omega) (by omega)
    have E2 : c (Add.r + 2) + c (Add.b + 2) + c (Add.cy + 1) = c (Add.a + 2) + 65536 * c (Add.cy + 2) :=
      natEq (by fp_ring) (by omega) (by omega)
    have E3 : c (Add.r + 3) + c (Add.b + 3) + c (Add.cy + 2) = c (Add.a + 3) + 65536 * c (Add.cy + 3) :=
      natEq (by fp_ring) (by omega) (by omega)
    refine ⟨fun h => absurd h (by decide), ?_⟩
    simp only [Num.binop, val4, Option.some.injEq]
    omega
