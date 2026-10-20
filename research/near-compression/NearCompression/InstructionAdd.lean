import NearSpecV3.Wasm.Exec
import ZkFormal.Air.Basic
import ZkFormal.Algebra.Fp

/-! Concrete BabyBear polynomial constraints for i32.add. Range checks and
stack/code buses are separate obligations: this is an arithmetic
subtable, not yet a complete instruction AIR. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

/-- Columns: a.low, a.high, b.low, b.high, out.low, out.high, carry.low, carry.high. -/
def instructionAdd32Constraints : List Expr := [
  .add (.add (.col 0 false) (.col 2 false))
    (.neg (.add (.col 4 false) (.mul (.const 65536) (.col 6 false)))),
  .add (.add (.add (.col 1 false) (.col 3 false)) (.col 6 false))
    (.neg (.add (.col 5 false) (.mul (.const 65536) (.col 7 false)))),
  .mul (.col 6 false) (.add (.col 6 false) (.neg (.const 1))),
  .mul (.col 7 false) (.add (.col 7 false) (.neg (.const 1)))]

def instructionAdd32Table : Table :=
  ⟨8, instructionAdd32Constraints, [], 22⟩

def instructionAddEnv (row : Nat → Fp) : Env Fp :=
  ⟨Fp.ofNat, (· + ·), (· * ·), Neg.neg, fun c _ => row c,
    fun _ => 0, 0, 0, 0⟩

/-- External range obligation until connected to a range-check table. -/
def instructionAdd32Ranges (row : Nat → Fp) : Prop :=
  ∀ i, i < 6 → (row i).toNat < 65536

def instructionAdd32Holds (row : Nat → Fp) : Prop :=
  ∀ e ∈ instructionAdd32Constraints, e.evalWith (instructionAddEnv row) = 0

/-- Small bounded field sums do not wrap modulo BabyBear. -/
theorem instruction_add_limb_sound (a b ci out co : Fp)
    (ha : a.toNat < 65536) (hb : b.toNat < 65536)
    (hi : ci.toNat ≤ 1) (ho : out.toNat < 65536) (hc : co.toNat ≤ 1)
    (h : a + b + ci = out + (65536 : Fp) * co) :
    a.toNat + b.toNat + ci.toNat = out.toNat + 65536 * co.toNat := by
  have hn := congrArg Fp.toNat h
  change Fp.toNat (Fp.add (Fp.add a b) ci) =
    Fp.toNat (Fp.add out (Fp.mul (Fp.ofNat 65536) co)) at hn
  simp only [Fp.toNat_add, Fp.toNat_mul, Fp.toNat_ofNat] at hn
  have h1 : a.toNat + b.toNat < ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P; omega
  have h2 : a.toNat + b.toNat + ci.toNat < ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P; omega
  have h3 : 65536 * co.toNat < ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P; omega
  have h4 : out.toNat + 65536 * co.toNat < ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P; omega
  change ((a.toNat + b.toNat) % ZkFormal.Algebra.P + ci.toNat) % ZkFormal.Algebra.P =
    (out.toNat + (65536 * co.toNat) % ZkFormal.Algebra.P) % ZkFormal.Algebra.P at hn
  simpa only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] using hn

theorem instruction_add_boolean_bound (x : Fp)
    (h : x * (x + -(1 : Fp)) = 0) : x.toNat ≤ 1 := by
  have hx : x = 0 ∨ x = 1 := by grind
  rcases hx with hx | hx <;> subst x <;> decide

/-- The actual AIR expressions imply the two bounded integer carry equations. -/
theorem instruction_add32_equations (row : Nat → Fp)
    (ranges : instructionAdd32Ranges row) (holds : instructionAdd32Holds row) :
    (row 0).toNat + (row 2).toNat = (row 4).toNat + 65536 * (row 6).toNat ∧
    (row 1).toNat + (row 3).toNat + (row 6).toNat =
      (row 5).toNat + 65536 * (row 7).toNat := by
  have h := holds
  simp only [instructionAdd32Holds, instructionAdd32Constraints,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, implies_true, and_true,
    Expr.evalWith, instructionAddEnv] at h
  rcases h with ⟨h0, h1, h6, h7⟩
  change row 0 + row 2 + -(row 4 + (65536 : Fp) * row 6) = 0 at h0
  change row 1 + row 3 + row 6 + -(row 5 + (65536 : Fp) * row 7) = 0 at h1
  have c6 := instruction_add_boolean_bound (row 6) h6
  have c7 := instruction_add_boolean_bound (row 7) h7
  have e0 : row 0 + row 2 + (0 : Fp) = row 4 + (65536 : Fp) * row 6 := by grind
  have e1 : row 1 + row 3 + row 6 = row 5 + (65536 : Fp) * row 7 := by grind
  have l0 := instruction_add_limb_sound (row 0) (row 2) 0 (row 4) (row 6)
    (ranges 0 (by decide)) (ranges 2 (by decide)) (by decide)
    (ranges 4 (by decide)) c6 e0
  have l1 := instruction_add_limb_sound (row 1) (row 3) (row 6) (row 5) (row 7)
    (ranges 1 (by decide)) (ranges 3 (by decide)) c6
    (ranges 5 (by decide)) c7 e1
  change (row 0).toNat + (row 2).toNat + 0 = _ at l0
  exact ⟨by simpa using l0, l1⟩

def instructionAddWord (row : Nat → Fp) (low high : Nat) : Nat :=
  (row low).toNat + 65536 * (row high).toNat

/-- Arithmetic soundness against the actual Wasm i32 addition helper. -/
theorem instruction_add32_binop (row : Nat → Fp)
    (ranges : instructionAdd32Ranges row) (holds : instructionAdd32Holds row) :
    Num.binop 32 0 (instructionAddWord row 0 1) (instructionAddWord row 2 3) =
      some (instructionAddWord row 4 5) := by
  obtain ⟨h0, h1⟩ := instruction_add32_equations row ranges holds
  have r4 := ranges 4 (by decide)
  have r5 := ranges 5 (by decide)
  have total : instructionAddWord row 0 1 + instructionAddWord row 2 3 =
      instructionAddWord row 4 5 + 4294967296 * (row 7).toNat := by
    unfold instructionAddWord
    omega
  have bound : instructionAddWord row 4 5 < 4294967296 := by
    unfold instructionAddWord
    omega
  simp only [Num.binop, total]
  congr 1
  change (instructionAddWord row 4 5 + 4294967296 * (row 7).toNat) % 4294967296 = _
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]

/-- Instruction-level bridge with explicit stack-pop bindings. Code fetch, type
validation and stack bus enforcement must supply these bindings in the full AIR. -/
theorem instruction_add32_exec_num (row : Nat → Fp)
    (ranges : instructionAdd32Ranges row) (holds : instructionAdd32Holds row)
    (s s₁ s₂ : St)
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂)) :
    execNum s 0x6A = .ok (pushI32 s₂ (instructionAddWord row 4 5)) := by
  have hb := instruction_add32_binop row ranges holds
  simp [execNum, popRight, popLeft, hb, pure, Except.pure]

/-- Honest row constructor using two 16-bit limbs, including both carries. -/
def instructionAdd32Witness (a b : UInt32) : Nat → Fp :=
  let lo := a.toNat % 65536 + b.toNat % 65536
  let hi := a.toNat / 65536 + b.toNat / 65536 + lo / 65536
  fun i => Fp.ofNat (match i with
    | 0 => a.toNat % 65536
    | 1 => a.toNat / 65536
    | 2 => b.toNat % 65536
    | 3 => b.toNat / 65536
    | 4 => lo % 65536
    | 5 => hi % 65536
    | 6 => lo / 65536
    | 7 => hi / 65536
    | _ => 0)

/-- Natural carry equations imply the actual field polynomials vanish. -/
theorem instruction_add32_from_carries (r : Nat → Nat)
    (h0 : r 0 + r 2 = r 4 + 65536 * r 6)
    (h1 : r 1 + r 3 + r 6 = r 5 + 65536 * r 7)
    (h6 : r 6 ≤ 1) (h7 : r 7 ≤ 1) :
    instructionAdd32Holds (fun i => Fp.ofNat (r i)) := by
  have ca (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_add a b
  have cm (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_mul a b
  have e0 := congrArg Fp.ofNat h0
  have e1 := congrArg Fp.ofNat h1
  simp only [ca, cm] at e0 e1
  have c6 : r 6 = 0 ∨ r 6 = 1 := by omega
  have c7 : r 7 = 0 ∨ r 7 = 1 := by omega
  simp only [instructionAdd32Holds, instructionAdd32Constraints,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, implies_true, and_true,
    Expr.evalWith, instructionAddEnv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]; change (Fp.ofNat (r 4) + Fp.ofNat 65536 * Fp.ofNat (r 6)) +
      -(Fp.ofNat (r 4) + Fp.ofNat 65536 * Fp.ofNat (r 6)) = 0
    grind
  · rw [e1]; grind
  · rcases c6 with c6 | c6 <;> rw [c6] <;> decide
  · rcases c7 with c7 | c7 <;> rw [c7] <;> decide

/-- Every pair of i32 inputs has an accepted arithmetic witness. -/
theorem instruction_add32_witness_holds (a b : UInt32) :
    instructionAdd32Holds (instructionAdd32Witness a b) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have al := Nat.mod_lt a.toNat (show 0 < 65536 by decide)
  have bl := Nat.mod_lt b.toNat (show 0 < 65536 by decide)
  unfold instructionAdd32Witness
  apply instruction_add32_from_carries
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega

/-- Honest witnesses also meet the separate limb range obligation. -/
theorem instruction_add32_witness_ranges (a b : UInt32) :
    instructionAdd32Ranges (instructionAdd32Witness a b) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  intro i hi
  have ci : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases ci with ci | ci | ci | ci | ci | ci <;> subst i <;>
    simp only [instructionAdd32Witness, Fp.toNat_ofNat]
  all_goals unfold ZkFormal.Algebra.P
  all_goals omega

theorem instruction_add32_witness_inputs (a b : UInt32) :
    instructionAddWord (instructionAdd32Witness a b) 0 1 = a.toNat ∧
    instructionAddWord (instructionAdd32Witness a b) 2 3 = b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [instructionAddWord, instructionAdd32Witness, Fp.toNat_ofNat]
  unfold ZkFormal.Algebra.P
  omega

end NearCompression
