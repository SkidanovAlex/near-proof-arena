import NearCompression.InstructionAddRange

/-! Local instruction metadata constraints. PC is two 16-bit limbs. Heights
are restricted to [2,65536); linking that bound to validated execution is still
required. Local pre/post values are not cross-row sequencing or code/stack
bus authentication. Gas is not constrained by this gadget. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def instructionControlRangeColumn (slot : Nat) : Nat :=
  if slot < 4 then 105 + slot else 106 + slot

def instructionControlRangeConstraints (slot : Nat) : List Expr :=
  .add (.col (instructionControlRangeColumn slot) false)
    (.neg (instructionBitExpr (113 + 16 * slot) 16)) ::
  (List.range 16).map (fun bit => instructionBitConstraint (113 + 16 * slot + bit))

def instructionControlMetadataConstraints : List Expr := [
  .add (.col 104 false) (.neg (.const 106)),
  .add (.add (.col 105 false) (.const 1))
    (.neg (.add (.col 107 false) (.mul (.const 65536) (.col 109 false)))),
  .add (.add (.col 106 false) (.col 109 false)) (.neg (.col 108 false)),
  instructionBitConstraint 109,
  .add (.add (.col 112 false) (.const 2)) (.neg (.col 110 false)),
  .add (.add (.col 111 false) (.const 1)) (.neg (.col 110 false))]

def instructionAdd32ControlConstraints : List Expr :=
  instructionAdd32RangeConstraints ++ instructionControlMetadataConstraints ++
    (List.range 7).flatMap instructionControlRangeConstraints

def instructionAdd32ControlTable : Table :=
  ⟨225, instructionAdd32ControlConstraints, [], 22⟩

def instructionAdd32ControlHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ instructionAdd32ControlConstraints, e.evalWith (instructionAddEnv row) = 0

theorem instruction_control_range_sound (row : Nat → Fp)
    (h : instructionAdd32ControlHolds row) (slot : Nat) (hs : slot < 7) :
    (row (instructionControlRangeColumn slot)).toNat < 65536 := by
  have localH : ∀ e ∈ instructionControlRangeConstraints slot,
      e.evalWith (instructionAddEnv row) = 0 := by
    intro e he
    exact h e (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨slot, List.mem_range.mpr hs, he⟩))
  have bits : ∀ k, k < 16 → (row (113 + 16 * slot + k)).toNat ≤ 1 := by
    intro k hk
    have hb := localH (instructionBitConstraint (113 + 16 * slot + k))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    exact instruction_add_boolean_bound _ hb
  have bound := instruction_bit_expr_bound row 16 (113 + 16 * slot) (by decide) bits
  have recH := localH _ (List.mem_cons_self ..)
  change row (instructionControlRangeColumn slot) +
    -((instructionBitExpr (113 + 16 * slot) 16).evalWith (instructionAddEnv row)) = 0 at recH
  have eq : row (instructionControlRangeColumn slot) =
      (instructionBitExpr (113 + 16 * slot) 16).evalWith (instructionAddEnv row) := by grind
  rw [eq]
  exact bound

theorem instruction_control_small_sum (a b out : Fp)
    (ha : a.toNat < 65536) (hb : b.toNat < 65536) (ho : out.toNat < 65536)
    (eq : a + b = out) : a.toNat + b.toNat = out.toNat := by
  have hn := congrArg Fp.toNat eq
  change Fp.toNat (Fp.add a b) = _ at hn
  rw [Fp.toNat_add] at hn
  have bound : a.toNat + b.toNat < ZkFormal.Algebra.P := by
    unfold ZkFormal.Algebra.P; omega
  rwa [Nat.mod_eq_of_lt bound] at hn

theorem instruction_control_addition_holds (row : Nat → Fp)
    (h : instructionAdd32ControlHolds row) : instructionAdd32RangeHolds row := by
  intro e he
  exact h e (List.mem_append_left _ (List.mem_append_left _ he))

/-- Every accepted local row carries the correct opcode, a nonwrapping PC
increment and a nonunderflowing binary-operation stack-height decrement. -/
theorem instruction_control_metadata_sound (row : Nat → Fp)
    (h : instructionAdd32ControlHolds row) :
    (row 104).toNat = 106 ∧
    instructionAddWord row 105 106 + 1 = instructionAddWord row 107 108 ∧
    instructionAddWord row 105 106 < 4294967296 ∧
    instructionAddWord row 107 108 < 4294967296 ∧
    2 ≤ (row 110).toNat ∧ (row 111).toNat + 1 = (row 110).toNat ∧
    (row 110).toNat < 65536 := by
  have mr : ∀ e ∈ instructionControlMetadataConstraints,
      e.evalWith (instructionAddEnv row) = 0 := by
    intro e he
    exact h e (List.mem_append_left _ (List.mem_append_right _ he))
  simp only [instructionControlMetadataConstraints, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false, implies_true, and_true,
    instructionBitConstraint, Expr.evalWith, instructionAddEnv] at mr
  rcases mr with ⟨hop, hlo, hhi, hc, hs, hn⟩
  have r0 := instruction_control_range_sound row h 0 (by decide)
  have r1 := instruction_control_range_sound row h 1 (by decide)
  have r2 := instruction_control_range_sound row h 2 (by decide)
  have r3 := instruction_control_range_sound row h 3 (by decide)
  have r4 := instruction_control_range_sound row h 4 (by decide)
  have r5 := instruction_control_range_sound row h 5 (by decide)
  have r6 := instruction_control_range_sound row h 6 (by decide)
  simp only [instructionControlRangeColumn] at r0 r1 r2 r3 r4 r5 r6
  change (row 105).toNat < 65536 at r0
  change (row 106).toNat < 65536 at r1
  change (row 107).toNat < 65536 at r2
  change (row 108).toNat < 65536 at r3
  change (row 110).toNat < 65536 at r4
  change (row 111).toNat < 65536 at r5
  change (row 112).toNat < 65536 at r6
  have carry := instruction_add_boolean_bound (row 109) hc
  change row 104 + -(106 : Fp) = 0 at hop
  change row 105 + (1 : Fp) + -(row 107 + (65536 : Fp) * row 109) = 0 at hlo
  change row 106 + row 109 + -row 108 = 0 at hhi
  change row 112 + (2 : Fp) + -row 110 = 0 at hs
  change row 111 + (1 : Fp) + -row 110 = 0 at hn
  have opcode : row 104 = (106 : Fp) := by grind
  have loweq : row 105 + (1 : Fp) + 0 = row 107 + (65536 : Fp) * row 109 := by grind
  have low := instruction_add_limb_sound (row 105) 1 0 (row 107) (row 109)
    r0 (by decide) (by decide) r2 carry loweq
  have high := instruction_control_small_sum (row 106) (row 109) (row 108)
    r1 (by omega) r3 (by grind)
  have height := instruction_control_small_sum (row 112) 2 (row 110)
    r6 (by decide) r4 (by grind)
  have next := instruction_control_small_sum (row 111) 1 (row 110)
    r5 (by decide) r4 (by grind)
  change (row 105).toNat + 1 + 0 = (row 107).toNat + 65536 * (row 109).toNat at low
  change (row 112).toNat + 2 = (row 110).toNat at height
  change (row 111).toNat + 1 = (row 110).toNat at next
  refine ⟨?_, ?_, ?_, ?_, ?_, next, r4⟩
  · rw [opcode]; rfl
  · unfold instructionAddWord; omega
  · unfold instructionAddWord; omega
  · unfold instructionAddWord; omega
  · omega

def instructionControlNat (pc height col : Nat) : Nat :=
  match col with
  | 104 => 106
  | 105 => pc % 65536
  | 106 => pc / 65536
  | 107 => (pc + 1) % 65536
  | 108 => (pc + 1) / 65536
  | 109 => (pc % 65536 + 1) / 65536
  | 110 => height
  | 111 => height - 1
  | 112 => height - 2
  | _ => 0

def instructionAdd32ControlWitness (a b : UInt32) (pc height col : Nat) : Fp :=
  if col < 104 then instructionAdd32RangeWitness a b col else
  if col < 113 then Fp.ofNat (instructionControlNat pc height col) else
    let slot := col - 113
    Fp.ofNat (instructionControlNat pc height (instructionControlRangeColumn (slot / 16)) /
      2 ^ (slot % 16) % 2)

theorem instruction_control_witness_metadata (a b : UInt32) (pc height col : Nat)
    (lo : 104 ≤ col) (hi : col < 113) :
    instructionAdd32ControlWitness a b pc height col = Fp.ofNat (instructionControlNat pc height col) := by
  simp only [instructionAdd32ControlWitness, if_neg (by omega : ¬col < 104), if_pos hi]

theorem instruction_control_witness_bit (a b : UInt32) (pc height slot bit : Nat)
    (hb : bit < 16) :
    instructionAdd32ControlWitness a b pc height (113 + 16 * slot + bit) =
      Fp.ofNat (instructionControlNat pc height (instructionControlRangeColumn slot) / 2 ^ bit % 2) := by
  have h0 : ¬113 + 16 * slot + bit < 104 := by omega
  have h1 : ¬113 + 16 * slot + bit < 113 := by omega
  have hd : (113 + 16 * slot + bit - 113) / 16 = slot := by omega
  have hm : (113 + 16 * slot + bit - 113) % 16 = bit := by omega
  simp only [instructionAdd32ControlWitness, if_neg h0, if_neg h1, hd, hm]

/-- Canonical metadata lies in the circuit's chosen no-overflow domain. -/
theorem instruction_control_nat_range (pc height : Nat)
    (pcBound : pc + 1 < 4294967296) (heightLo : 2 ≤ height) (heightHi : height < 65536)
    (slot : Nat) (hs : slot < 7) :
    instructionControlNat pc height (instructionControlRangeColumn slot) < 65536 := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 := by omega
  rcases cases with hs | hs | hs | hs | hs | hs | hs <;> subst slot <;>
    simp [instructionControlRangeColumn, instructionControlNat] <;> omega

/-- Expressions whose columns lie in a preserved prefix retain their values. -/
theorem instruction_control_prefix_eval (e : Expr) (row other : Nat → Fp) (width : Nat)
    (bound : e.colBound ≤ width) (same : ∀ col, col < width → row col = other col) :
    e.evalWith (instructionAddEnv row) = e.evalWith (instructionAddEnv other) := by
  induction e with
  | col c nx => exact same c (by change c + 1 ≤ width at bound; omega)
  | add a b ia ib =>
    have ha : a.colBound ≤ width := by change max a.colBound b.colBound ≤ width at bound; omega
    have hb : b.colBound ≤ width := by change max a.colBound b.colBound ≤ width at bound; omega
    change _ + _ = _ + _
    rw [ia ha, ib hb]
  | mul a b ia ib =>
    have ha : a.colBound ≤ width := by change max a.colBound b.colBound ≤ width at bound; omega
    have hb : b.colBound ≤ width := by change max a.colBound b.colBound ≤ width at bound; omega
    change _ * _ = _ * _
    rw [ia ha, ib hb]
  | neg a ia => exact congrArg Neg.neg (ia bound)
  | const _ | pub _ | isFirst | isLast | isTransition => rfl

set_option maxRecDepth 4096 in
theorem instruction_control_base_column_bounds :
    instructionAdd32RangeConstraints.all (fun e => decide (e.colBound ≤ 104)) = true := by
  decide

theorem instruction_control_witness_metadata_holds (a b : UInt32) (pc height : Nat)
    (pcBound : pc + 1 < 4294967296) (heightLo : 2 ≤ height) (heightHi : height < 65536) :
    ∀ e ∈ instructionControlMetadataConstraints,
      e.evalWith (instructionAddEnv (instructionAdd32ControlWitness a b pc height)) = 0 := by
  have ca (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_add a b
  have cm (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_mul a b
  have lo : pc % 65536 + 1 = (pc + 1) % 65536 + 65536 * ((pc % 65536 + 1) / 65536) := by omega
  have hi : pc / 65536 + (pc % 65536 + 1) / 65536 = (pc + 1) / 65536 := by omega
  have hs : height - 2 + 2 = height := by omega
  have hn : height - 1 + 1 = height := by omega
  have loF := congrArg Fp.ofNat lo
  have hiF := congrArg Fp.ofNat hi
  have hsF := congrArg Fp.ofNat hs
  have hnF := congrArg Fp.ofNat hn
  simp only [ca, cm] at loF hiF hsF hnF
  have carry : (pc % 65536 + 1) / 65536 = 0 ∨ (pc % 65536 + 1) / 65536 = 1 := by omega
  simp only [instructionControlMetadataConstraints, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Fp.ofNat 106 + -Fp.ofNat 106 = 0; grind
  · change Fp.ofNat (pc % 65536) + Fp.ofNat 1 +
      -(Fp.ofNat ((pc + 1) % 65536) + Fp.ofNat 65536 * Fp.ofNat ((pc % 65536 + 1) / 65536)) = 0
    rw [loF]; grind
  · change Fp.ofNat (pc / 65536) + Fp.ofNat ((pc % 65536 + 1) / 65536) +
      -Fp.ofNat ((pc + 1) / 65536) = 0
    rw [hiF]; grind
  · change Fp.ofNat ((pc % 65536 + 1) / 65536) *
      (Fp.ofNat ((pc % 65536 + 1) / 65536) + -Fp.ofNat 1) = 0
    rcases carry with hc | hc <;> rw [hc] <;> decide
  · change Fp.ofNat (height - 2) + Fp.ofNat 2 + -Fp.ofNat height = 0
    rw [hsF]; grind
  · change Fp.ofNat (height - 1) + Fp.ofNat 1 + -Fp.ofNat height = 0
    rw [hnF]; grind

theorem instruction_control_witness_holds (a b : UInt32) (pc height : Nat)
    (pcBound : pc + 1 < 4294967296) (heightLo : 2 ≤ height) (heightHi : height < 65536) :
    instructionAdd32ControlHolds (instructionAdd32ControlWitness a b pc height) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · have hbound := List.all_eq_true.mp instruction_control_base_column_bounds e he
      have bound : e.colBound ≤ 104 := of_decide_eq_true hbound
      rw [instruction_control_prefix_eval e _ (instructionAdd32RangeWitness a b) 104 bound
        (by intro c hc; simp only [instructionAdd32ControlWitness, if_pos hc])]
      exact instruction_add32_range_witness_holds a b e he
    · exact instruction_control_witness_metadata_holds a b pc height pcBound heightLo heightHi e he
  · obtain ⟨slot, hs, he⟩ := List.mem_flatMap.mp he
    have hs' := List.mem_range.mp hs
    have colLo : 104 ≤ instructionControlRangeColumn slot := by
      unfold instructionControlRangeColumn; split <;> omega
    have colHi : instructionControlRangeColumn slot < 113 := by
      unfold instructionControlRangeColumn; split <;> omega
    rcases List.mem_cons.mp he with he | he
    · subst e
      have bits := instruction_control_witness_bit a b pc height slot
      have eq := instruction_bit_expr_complete (instructionAdd32ControlWitness a b pc height)
        16 (113 + 16 * slot) (instructionControlNat pc height (instructionControlRangeColumn slot))
        (instruction_control_nat_range pc height pcBound heightLo heightHi slot hs') bits
      change instructionAdd32ControlWitness a b pc height (instructionControlRangeColumn slot) +
        -(instructionBitExpr (113 + 16 * slot) 16).evalWith
          (instructionAddEnv (instructionAdd32ControlWitness a b pc height)) = 0
      rw [eq, instruction_control_witness_metadata a b pc height _ colLo colHi]
      grind
    · obtain ⟨bit, hb, he⟩ := List.mem_map.mp he
      subst e
      change instructionAdd32ControlWitness a b pc height (113 + 16 * slot + bit) *
        (instructionAdd32ControlWitness a b pc height (113 + 16 * slot + bit) + -(1 : Fp)) = 0
      rw [instruction_control_witness_bit a b pc height slot bit (List.mem_range.mp hb)]
      have hv : instructionControlNat pc height (instructionControlRangeColumn slot) / 2 ^ bit % 2 = 0 ∨
          instructionControlNat pc height (instructionControlRangeColumn slot) / 2 ^ bit % 2 = 1 := by omega
      rcases hv with hv | hv <;> rw [hv] <;> decide

set_option maxRecDepth 8192 in
theorem instruction_control_table_wf :
    instructionAdd32ControlTable.wf ⟨[instructionAdd32ControlTable], 0, 0⟩ 2 = true := by
  decide

set_option maxRecDepth 8192 in
theorem instruction_control_table_size :
    instructionAdd32ControlTable.width = 225 ∧
      instructionAdd32ControlTable.constraints.length = 231 := by
  decide

end NearCompression
