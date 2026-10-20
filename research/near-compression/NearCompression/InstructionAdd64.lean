import NearCompression.InstructionAddRange

/-! Four-limb i64.add arithmetic AIR over BabyBear. This also supplies a
modular-addition building block for SHA-512, not a complete hash circuit.
Code/stack/gas bindings remain external. -/
namespace NearCompression
set_option maxRecDepth 8192
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def instructionAdd64LimbConstraint (limb : Nat) : Expr :=
  .add (.add (.add (.col limb false) (.col (4 + limb) false))
      (if limb = 0 then .const 0 else .col (11 + limb) false))
    (.neg (.add (.col (8 + limb) false) (.mul (.const 65536) (.col (12 + limb) false))))

def instructionAdd64RangeConstraints (limb : Nat) : List Expr :=
  .add (.col limb false) (.neg (instructionBitExpr (16 + 16 * limb) 16)) ::
    (List.range 16).map (fun bit => instructionBitConstraint (16 + 16 * limb + bit))

def instructionAdd64Constraints : List Expr :=
  (List.range 4).map instructionAdd64LimbConstraint ++
  (List.range 4).map (fun limb => instructionBitConstraint (12 + limb)) ++
  (List.range 12).flatMap instructionAdd64RangeConstraints

def instructionAdd64Table : Table := ⟨208, instructionAdd64Constraints, [], 22⟩

def instructionAdd64Holds (row : Nat → Fp) : Prop :=
  ∀ e ∈ instructionAdd64Constraints, e.evalWith (instructionAddEnv row) = 0

def instructionAdd64Word (row : Nat → Fp) (base : Nat) : Nat :=
  (row base).toNat + 65536 * (row (base + 1)).toNat +
    4294967296 * (row (base + 2)).toNat + 281474976710656 * (row (base + 3)).toNat

theorem instruction_add64_ranges (row : Nat → Fp) (h : instructionAdd64Holds row)
    (limb : Nat) (hl : limb < 12) : (row limb).toNat < 65536 := by
  have localH : ∀ e ∈ instructionAdd64RangeConstraints limb,
      e.evalWith (instructionAddEnv row) = 0 := by
    intro e he
    exact h e (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨limb, List.mem_range.mpr hl, he⟩))
  have bits : ∀ k, k < 16 → (row (16 + 16 * limb + k)).toNat ≤ 1 := by
    intro k hk
    exact instruction_add_boolean_bound _ (localH (instructionBitConstraint (16 + 16 * limb + k))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))
  have bound := instruction_bit_expr_bound row 16 (16 + 16 * limb) (by decide) bits
  have recH := localH _ (List.mem_cons_self ..)
  change row limb + -((instructionBitExpr (16 + 16 * limb) 16).evalWith (instructionAddEnv row)) = 0 at recH
  have eq : row limb = (instructionBitExpr (16 + 16 * limb) 16).evalWith (instructionAddEnv row) := by grind
  rw [eq]
  exact bound

theorem instruction_add64_carry (row : Nat → Fp) (h : instructionAdd64Holds row)
    (limb : Nat) (hl : limb < 4) : (row (12 + limb)).toNat ≤ 1 := by
  exact instruction_add_boolean_bound _ (h (instructionBitConstraint (12 + limb)) (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨limb, List.mem_range.mpr hl, rfl⟩))))

theorem instruction_add64_equation (row : Nat → Fp) (h : instructionAdd64Holds row)
    (limb : Nat) (hl : limb < 4) :
    (row limb).toNat + (row (4 + limb)).toNat + (if limb = 0 then 0 else (row (11 + limb)).toNat) =
      (row (8 + limb)).toNat + 65536 * (row (12 + limb)).toNat := by
  have eq := h _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨limb, List.mem_range.mpr hl, rfl⟩)))
  have ha := instruction_add64_ranges row h limb (by omega)
  have hb := instruction_add64_ranges row h (4 + limb) (by omega)
  have ho := instruction_add64_ranges row h (8 + limb) (by omega)
  have hc := instruction_add64_carry row h limb hl
  by_cases zero : limb = 0
  · subst limb
    change row 0 + row 4 + (0 : Fp) + -(row 8 + (65536 : Fp) * row 12) = 0 at eq
    have e : row 0 + row 4 + (0 : Fp) = row 8 + (65536 : Fp) * row 12 := by grind
    exact instruction_add_limb_sound (row 0) (row 4) 0 (row 8) (row 12) ha hb (by decide) ho hc e
  · have prev := instruction_add64_carry row h (limb - 1) (by omega)
    have idx : 12 + (limb - 1) = 11 + limb := by omega
    rw [idx] at prev
    simp only [instructionAdd64LimbConstraint, if_neg zero, Expr.evalWith, instructionAddEnv] at eq
    change row limb + row (4 + limb) + row (11 + limb) +
      -(row (8 + limb) + (65536 : Fp) * row (12 + limb)) = 0 at eq
    have e : row limb + row (4 + limb) + row (11 + limb) =
        row (8 + limb) + (65536 : Fp) * row (12 + limb) := by grind
    simp only [if_neg zero]
    exact instruction_add_limb_sound _ _ _ _ _ ha hb prev ho hc e

theorem instruction_add64_binop (row : Nat → Fp) (h : instructionAdd64Holds row) :
    Num.binop 64 0 (instructionAdd64Word row 0) (instructionAdd64Word row 4) =
      some (instructionAdd64Word row 8) := by
  have e0 := instruction_add64_equation row h 0 (by decide)
  have e1 := instruction_add64_equation row h 1 (by decide)
  have e2 := instruction_add64_equation row h 2 (by decide)
  have e3 := instruction_add64_equation row h 3 (by decide)
  have r0 := instruction_add64_ranges row h 8 (by decide)
  have r1 := instruction_add64_ranges row h 9 (by decide)
  have r2 := instruction_add64_ranges row h 10 (by decide)
  have r3 := instruction_add64_ranges row h 11 (by decide)
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, if_true, if_false] at e0 e1 e2 e3
  have total : instructionAdd64Word row 0 + instructionAdd64Word row 4 =
      instructionAdd64Word row 8 + 18446744073709551616 * (row 15).toNat := by
    unfold instructionAdd64Word; simp only [Nat.reduceAdd]; omega
  have bound : instructionAdd64Word row 8 < 18446744073709551616 := by
    unfold instructionAdd64Word; simp only [Nat.reduceAdd]; omega
  simp only [Num.binop, total]
  congr 1
  change (_ + 18446744073709551616 * _) % 18446744073709551616 = _
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]

theorem instruction_add64_exec_num (row : Nat → Fp) (h : instructionAdd64Holds row)
    (s s₁ s₂ : St) (right : popN s = (instructionAdd64Word row 4, s₁))
    (left : popN s₁ = (instructionAdd64Word row 0, s₂)) :
    execNum s 0x7C = .ok (pushI64 s₂ (instructionAdd64Word row 8)) := by
  have hb := instruction_add64_binop row h
  simp [execNum, right, left, hb, pure, Except.pure]

set_option maxRecDepth 8192 in
theorem instruction_add64_table_wf :
    instructionAdd64Table.wf ⟨[instructionAdd64Table], 0, 0⟩ 2 = true := by decide

set_option maxRecDepth 8192 in
theorem instruction_add64_table_size :
    instructionAdd64Table.width = 208 ∧ instructionAdd64Table.constraints.length = 212 := by decide

def instructionAdd64Digit (a : UInt64) (limb : Nat) : Nat :=
  a.toNat / 65536 ^ limb % 65536

def instructionAdd64Carry (a b : UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => (instructionAdd64Digit a n + instructionAdd64Digit b n + instructionAdd64Carry a b n) / 65536

def instructionAdd64Nat (a b : UInt64) (col : Nat) : Nat :=
  if col < 4 then instructionAdd64Digit a col else
  if col < 8 then instructionAdd64Digit b (col - 4) else
  if col < 12 then
    (instructionAdd64Digit a (col - 8) + instructionAdd64Digit b (col - 8) +
      instructionAdd64Carry a b (col - 8)) % 65536 else
  if col < 16 then instructionAdd64Carry a b (col - 11) else 0

def instructionAdd64Witness (a b : UInt64) (col : Nat) : Fp :=
  if col < 16 then Fp.ofNat (instructionAdd64Nat a b col) else
    let slot := col - 16
    Fp.ofNat (instructionAdd64Nat a b (slot / 16) / 2 ^ (slot % 16) % 2)

theorem instruction_add64_carry_bound (a b : UInt64) (n : Nat) :
    instructionAdd64Carry a b n ≤ 1 := by
  induction n with
  | zero => change 0 ≤ 1; decide
  | succ n ih =>
    have ha : instructionAdd64Digit a n < 65536 := Nat.mod_lt _ (by decide)
    have hb : instructionAdd64Digit b n < 65536 := Nat.mod_lt _ (by decide)
    change (_ + _ + _) / 65536 ≤ 1
    omega

theorem instruction_add64_nat_range (a b : UInt64) (col : Nat) (hc : col < 12) :
    instructionAdd64Nat a b col < 65536 := by
  by_cases h4 : col < 4
  · simp only [instructionAdd64Nat, if_pos h4]
    exact Nat.mod_lt _ (by decide)
  · by_cases h8 : col < 8
    · simp only [instructionAdd64Nat, if_neg h4, if_pos h8]
      exact Nat.mod_lt _ (by decide)
    · simp only [instructionAdd64Nat, if_neg h4, if_neg h8, if_pos hc]
      exact Nat.mod_lt _ (by decide)

theorem instruction_add64_witness_prefix (a b : UInt64) (col : Nat) (hc : col < 16) :
    instructionAdd64Witness a b col = Fp.ofNat (instructionAdd64Nat a b col) := by
  simp only [instructionAdd64Witness, if_pos hc]

theorem instruction_add64_witness_bit (a b : UInt64) (limb bit : Nat) (hb : bit < 16) :
    instructionAdd64Witness a b (16 + 16 * limb + bit) =
      Fp.ofNat (instructionAdd64Nat a b limb / 2 ^ bit % 2) := by
  have h : ¬16 + 16 * limb + bit < 16 := by omega
  have hd : (16 + 16 * limb + bit - 16) / 16 = limb := by omega
  have hm : (16 + 16 * limb + bit - 16) % 16 = bit := by omega
  simp only [instructionAdd64Witness, if_neg h, hd, hm]

/-- Honest integer carry equations, before mapping into BabyBear. -/
theorem instruction_add64_nat_equation (a b : UInt64) (limb : Nat) (hl : limb < 4) :
    instructionAdd64Nat a b limb + instructionAdd64Nat a b (4 + limb) +
      (if limb = 0 then 0 else instructionAdd64Nat a b (11 + limb)) =
      instructionAdd64Nat a b (8 + limb) + 65536 * instructionAdd64Nat a b (12 + limb) := by
  have cases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases cases with hl | hl | hl | hl <;> subst limb
  all_goals simp [instructionAdd64Nat, instructionAdd64Carry]
  all_goals omega

theorem instruction_add64_witness_holds (a b : UInt64) :
    instructionAdd64Holds (instructionAdd64Witness a b) := by
  have ca (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_add a b
  have cm (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_mul a b
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨limb, hl, he⟩ := List.mem_map.mp he
      subst e
      have hl' := List.mem_range.mp hl
      have hn := instruction_add64_nat_equation a b limb hl'
      have hf := congrArg Fp.ofNat hn
      by_cases zero : limb = 0
      · subst limb
        change instructionAdd64Witness a b 0 + instructionAdd64Witness a b 4 + Fp.ofNat 0 +
          -(instructionAdd64Witness a b 8 + Fp.ofNat 65536 * instructionAdd64Witness a b 12) = 0
        rw [instruction_add64_witness_prefix a b 0 (by decide),
          instruction_add64_witness_prefix a b 4 (by decide),
          instruction_add64_witness_prefix a b 8 (by decide),
          instruction_add64_witness_prefix a b 12 (by decide)]
        simp only [ite_true, Nat.add_zero, ca, cm] at hf
        rw [hf, show Fp.ofNat 0 = (0 : Fp) from rfl]; grind
      · simp only [instructionAdd64LimbConstraint, if_neg zero, Expr.evalWith, instructionAddEnv]
        rw [instruction_add64_witness_prefix a b limb (by omega),
          instruction_add64_witness_prefix a b (4 + limb) (by omega),
          instruction_add64_witness_prefix a b (11 + limb) (by omega),
          instruction_add64_witness_prefix a b (8 + limb) (by omega),
          instruction_add64_witness_prefix a b (12 + limb) (by omega)]
        simp only [if_neg zero, ca, cm] at hf
        rw [hf]; grind
    · obtain ⟨limb, hl, he⟩ := List.mem_map.mp he
      subst e
      have hl' := List.mem_range.mp hl
      have h0 : ¬12 + limb < 4 := by omega
      have h1 : ¬12 + limb < 8 := by omega
      have h2 : ¬12 + limb < 12 := by omega
      have h3 : 12 + limb < 16 := by omega
      change instructionAdd64Witness a b (12 + limb) *
        (instructionAdd64Witness a b (12 + limb) + -Fp.ofNat 1) = 0
      rw [instruction_add64_witness_prefix a b _ h3]
      simp only [instructionAdd64Nat, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
      have hc := instruction_add64_carry_bound a b (12 + limb - 11)
      have cases : instructionAdd64Carry a b (12 + limb - 11) = 0 ∨
        instructionAdd64Carry a b (12 + limb - 11) = 1 := by omega
      rcases cases with hc | hc <;> rw [hc] <;> decide
  · obtain ⟨limb, hl, he⟩ := List.mem_flatMap.mp he
    have hl' := List.mem_range.mp hl
    rcases List.mem_cons.mp he with he | he
    · subst e
      have eq := instruction_bit_expr_complete (instructionAdd64Witness a b) 16
        (16 + 16 * limb) (instructionAdd64Nat a b limb)
        (instruction_add64_nat_range a b limb hl') (instruction_add64_witness_bit a b limb)
      change instructionAdd64Witness a b limb +
        -(instructionBitExpr (16 + 16 * limb) 16).evalWith
          (instructionAddEnv (instructionAdd64Witness a b)) = 0
      rw [eq, instruction_add64_witness_prefix a b limb (by omega)]
      grind
    · obtain ⟨bit, hb, he⟩ := List.mem_map.mp he
      subst e
      change instructionAdd64Witness a b (16 + 16 * limb + bit) *
        (instructionAdd64Witness a b (16 + 16 * limb + bit) + -Fp.ofNat 1) = 0
      rw [instruction_add64_witness_bit a b limb bit (List.mem_range.mp hb)]
      have cases : instructionAdd64Nat a b limb / 2 ^ bit % 2 = 0 ∨
        instructionAdd64Nat a b limb / 2 ^ bit % 2 = 1 := by omega
      rcases cases with hc | hc <;> rw [hc] <;> decide

theorem instruction_add64_witness_inputs (a b : UInt64) :
    instructionAdd64Word (instructionAdd64Witness a b) 0 = a.toNat ∧
    instructionAdd64Word (instructionAdd64Witness a b) 4 = b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp [instructionAdd64Word, instructionAdd64Witness, instructionAdd64Nat,
    instructionAdd64Digit, Fp.toNat_ofNat]
  unfold ZkFormal.Algebra.P
  omega

end NearCompression
