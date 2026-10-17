import NearCompression.InstructionAdd

/-! Bit-decomposition baseline closing all six limb-range obligations in the
actual BabyBear addition AIR. The table is intentionally wide (104 columns):
96 boolean bit columns, six reconstruction constraints and four arithmetic
constraints. Stack/code buses and execution scheduling are still separate. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

/-- Little-endian Horner expression for `n` adjacent bit columns. -/
def instructionBitExpr (base : Nat) : Nat → Expr
  | 0 => .const 0
  | n + 1 => .add (.col base false)
      (.mul (.const 2) (instructionBitExpr (base + 1) n))

def instructionBitConstraint (col : Nat) : Expr :=
  .mul (.col col false) (.add (.col col false) (.neg (.const 1)))

def instructionLimbConstraints (limb : Nat) : List Expr :=
  .add (.col limb false) (.neg (instructionBitExpr (8 + 16 * limb) 16)) ::
    (List.range 16).map (fun bit => instructionBitConstraint (8 + 16 * limb + bit))

def instructionAdd32RangeConstraints : List Expr :=
  instructionAdd32Constraints ++ (List.range 6).flatMap instructionLimbConstraints

def instructionAdd32RangeTable : Table :=
  ⟨104, instructionAdd32RangeConstraints, [], 22⟩

def instructionAdd32RangeHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ instructionAdd32RangeConstraints, e.evalWith (instructionAddEnv row) = 0

/-- Up to sixteen boolean columns reconstruct a canonical bounded field value. -/
theorem instruction_bit_expr_bound (row : Nat → Fp) (n base : Nat)
    (hn : n ≤ 16) (bits : ∀ k, k < n → (row (base + k)).toNat ≤ 1) :
    ((instructionBitExpr base n).evalWith (instructionAddEnv row)).toNat < 2 ^ n := by
  induction n generalizing base with
  | zero => change (0 : Fp).toNat < 1; decide
  | succ n ih =>
    have hn' : n ≤ 16 := by omega
    have hb := bits 0 (by omega)
    simp only [Nat.add_zero] at hb
    have ht := ih (base + 1) hn' (by
      intro k hk
      have h := bits (k + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h)
    have hp : 2 ^ n ≤ 65536 := Nat.pow_le_pow_right (by decide) hn'
    let tail := (instructionBitExpr (base + 1) n).evalWith (instructionAddEnv row)
    change tail.toNat < 2 ^ n at ht
    have hm : 2 * tail.toNat < ZkFormal.Algebra.P := by
      unfold ZkFormal.Algebra.P; omega
    have hs : (row base).toNat + 2 * tail.toNat < ZkFormal.Algebra.P := by
      unfold ZkFormal.Algebra.P; omega
    change (Fp.add (row base) (Fp.mul (Fp.ofNat 2) tail)).toNat < 2 ^ (n + 1)
    simp only [Fp.toNat_add, Fp.toNat_mul, Fp.toNat_ofNat]
    change ((row base).toNat + (2 * tail.toNat) % ZkFormal.Algebra.P) %
      ZkFormal.Algebra.P < 2 ^ (n + 1)
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hs, Nat.pow_succ]
    omega

theorem instruction_add32_range_arithmetic (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) : instructionAdd32Holds row := by
  intro e he
  exact h e (List.mem_append_left _ he)

/-- The range premise is now derived from concrete polynomial vanishing. -/
theorem instruction_add32_range_sound (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) : instructionAdd32Ranges row := by
  intro limb hl
  have localH : ∀ e ∈ instructionLimbConstraints limb,
      e.evalWith (instructionAddEnv row) = 0 := by
    intro e he
    exact h e (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨limb, List.mem_range.mpr hl, he⟩))
  have bits : ∀ k, k < 16 → (row (8 + 16 * limb + k)).toNat ≤ 1 := by
    intro k hk
    have hb := localH (instructionBitConstraint (8 + 16 * limb + k))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    exact instruction_add_boolean_bound _ hb
  have bound := instruction_bit_expr_bound row 16 (8 + 16 * limb) (by decide) bits
  have recH := localH _ (List.mem_cons_self ..)
  change row limb + -((instructionBitExpr (8 + 16 * limb) 16).evalWith
    (instructionAddEnv row)) = 0 at recH
  have eq : row limb = (instructionBitExpr (8 + 16 * limb) 16).evalWith
      (instructionAddEnv row) := by grind
  rw [eq]
  exact bound

theorem instruction_add32_range_binop (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) :
    Num.binop 32 0 (instructionAddWord row 0 1) (instructionAddWord row 2 3) =
      some (instructionAddWord row 4 5) :=
  instruction_add32_binop row (instruction_add32_range_sound row h)
    (instruction_add32_range_arithmetic row h)

theorem instruction_add32_range_exec_num (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) (s s₁ s₂ : St)
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂)) :
    execNum s 0x6A = .ok (pushI32 s₂ (instructionAddWord row 4 5)) :=
  instruction_add32_exec_num row (instruction_add32_range_sound row h)
    (instruction_add32_range_arithmetic row h) s s₁ s₂ popRight popLeft

/-- Exact bit reconstruction, proved before specializing to sixteen bits. -/
theorem instruction_bit_expr_complete (row : Nat → Fp) (n base value : Nat)
    (bound : value < 2 ^ n)
    (bits : ∀ k, k < n → row (base + k) = Fp.ofNat (value / 2 ^ k % 2)) :
    (instructionBitExpr base n).evalWith (instructionAddEnv row) = Fp.ofNat value := by
  induction n generalizing base value with
  | zero =>
    have hv : value = 0 := by simpa using bound
    subst value
    rfl
  | succ n ih =>
    have bound' : value / 2 < 2 ^ n := by rw [Nat.pow_succ] at bound; omega
    have hb := bits 0 (by omega)
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at hb
    have ht := ih (base + 1) (value / 2) bound' (by
      intro k hk
      have h := bits (k + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k, Nat.div_div_eq_div_mul,
        Nat.pow_succ'] using h)
    change row base + Fp.ofNat 2 *
      (instructionBitExpr (base + 1) n).evalWith (instructionAddEnv row) = _
    rw [hb, ht]
    have ca (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
      Lean.Grind.Semiring.natCast_add a b
    have cm (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b :=
      Lean.Grind.Semiring.natCast_mul a b
    rw [← cm, ← ca, Nat.mod_add_div]

def instructionAdd32RangeWitness (a b : UInt32) (col : Nat) : Fp :=
  if col < 8 then instructionAdd32Witness a b col else
    let slot := col - 8
    Fp.ofNat ((instructionAdd32Witness a b (slot / 16)).toNat / 2 ^ (slot % 16) % 2)

theorem instruction_add32_range_witness_prefix (a b : UInt32) (col : Nat)
    (h : col < 8) :
    instructionAdd32RangeWitness a b col = instructionAdd32Witness a b col := by
  simp only [instructionAdd32RangeWitness, if_pos h]

theorem instruction_add32_range_witness_bit (a b : UInt32) (limb bit : Nat)
    (hb : bit < 16) :
    instructionAdd32RangeWitness a b (8 + 16 * limb + bit) =
      Fp.ofNat ((instructionAdd32Witness a b limb).toNat / 2 ^ bit % 2) := by
  have hn : ¬8 + 16 * limb + bit < 8 := by omega
  have hd : (8 + 16 * limb + bit - 8) / 16 = limb := by omega
  have hm : (8 + 16 * limb + bit - 8) % 16 = bit := by omega
  simp only [instructionAdd32RangeWitness, if_neg hn, hd, hm]

/-- Honest extended witnesses satisfy all arithmetic and range polynomials. -/
theorem instruction_add32_range_witness_holds (a b : UInt32) :
    instructionAdd32RangeHolds (instructionAdd32RangeWitness a b) := by
  have ar := instruction_add32_witness_holds a b
  have rr := instruction_add32_witness_ranges a b
  have hprefix := instruction_add32_range_witness_prefix a b
  intro e he
  rcases List.mem_append.mp he with he | he
  · have h := ar e he
    simp only [instructionAdd32Constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he <;> subst e
    all_goals simpa only [Expr.evalWith, instructionAddEnv,
      instructionAdd32RangeWitness, show 0 < 8 by decide, show 1 < 8 by decide,
      show 2 < 8 by decide, show 3 < 8 by decide, show 4 < 8 by decide,
      show 5 < 8 by decide, show 6 < 8 by decide, show 7 < 8 by decide, if_true] using h
  · obtain ⟨limb, hl, he⟩ := List.mem_flatMap.mp he
    have hl' := List.mem_range.mp hl
    rcases List.mem_cons.mp he with he | he
    · subst e
      have bits := instruction_add32_range_witness_bit a b limb
      have eq := instruction_bit_expr_complete (instructionAdd32RangeWitness a b)
        16 (8 + 16 * limb) (instructionAdd32Witness a b limb).toNat (rr limb hl') bits
      change instructionAdd32RangeWitness a b limb +
        -(instructionBitExpr (8 + 16 * limb) 16).evalWith
          (instructionAddEnv (instructionAdd32RangeWitness a b)) = 0
      rw [eq, Fp.ofNat_toNat, hprefix limb (by omega)]
      grind
    · obtain ⟨bit, hb, he⟩ := List.mem_map.mp he
      subst e
      change instructionAdd32RangeWitness a b (8 + 16 * limb + bit) *
        (instructionAdd32RangeWitness a b (8 + 16 * limb + bit) + -(1 : Fp)) = 0
      rw [instruction_add32_range_witness_bit a b limb bit (List.mem_range.mp hb)]
      have hv : (instructionAdd32Witness a b limb).toNat / 2 ^ bit % 2 = 0 ∨
          (instructionAdd32Witness a b limb).toNat / 2 ^ bit % 2 = 1 := by omega
      rcases hv with hv | hv <;> rw [hv] <;> decide

set_option maxRecDepth 4096 in
theorem instruction_add32_range_table_wf :
    instructionAdd32RangeTable.wf ⟨[instructionAdd32RangeTable], 0, 0⟩ 2 = true := by
  decide

theorem instruction_add32_range_table_size :
    instructionAdd32RangeTable.width = 104 ∧
      instructionAdd32RangeTable.constraints.length = 106 := by
  decide

end NearCompression
