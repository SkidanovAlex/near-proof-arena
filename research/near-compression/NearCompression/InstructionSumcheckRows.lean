import NearCompression.InstructionLayerCircuit

/-! Exact eight-row algebra for a sumcheck adapter. These are field identities
and honest zero-target results, not random-challenge soundness theorems. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

abbrev InstructionCube3 := Bool × Bool × Bool
abbrev InstructionPoint3 := Fp × Fp × Fp

def instructionCube3 : List InstructionCube3 :=
  [(false,false,false),(true,false,false),(false,true,false),(true,true,false),
   (false,false,true),(true,false,true),(false,true,true),(true,true,true)]

def instructionCubeIndex (b : InstructionCube3) : Nat :=
  (if b.1 then 1 else 0)+2*(if b.2.1 then 1 else 0)+4*(if b.2.2 then 1 else 0)

def instructionCubePoint (b : InstructionCube3) : InstructionPoint3 :=
  (if b.1 then 1 else 0,if b.2.1 then 1 else 0,if b.2.2 then 1 else 0)

def instructionLerp (a b t : Fp) : Fp := (1-t)*a+t*b

/-- Row index uses little-endian challenge bits; every column has the same fold. -/
def instructionRowsMLE (rows : Nat → Nat → Fp) (x : InstructionPoint3) (col : Nat) : Fp :=
  instructionLerp
    (instructionLerp (instructionLerp (rows 0 col) (rows 1 col) x.1)
      (instructionLerp (rows 2 col) (rows 3 col) x.1) x.2.1)
    (instructionLerp (instructionLerp (rows 4 col) (rows 5 col) x.1)
      (instructionLerp (rows 6 col) (rows 7 col) x.1) x.2.1) x.2.2

theorem instruction_lerp_zero (a b : Fp) : instructionLerp a b 0=a := by
  unfold instructionLerp
  grind

theorem instruction_lerp_one (a b : Fp) : instructionLerp a b 1=b := by
  unfold instructionLerp
  grind

theorem instruction_cube_index_bound (b : InstructionCube3) : instructionCubeIndex b<8 := by
  obtain ⟨a,b,c⟩ := b
  cases a <;> cases b <;> cases c <;> decide

theorem instruction_rows_mle_boolean (rows : Nat → Nat → Fp) (b : InstructionCube3) (col : Nat) :
    instructionRowsMLE rows (instructionCubePoint b) col=rows (instructionCubeIndex b) col := by
  obtain ⟨a,b,c⟩ := b
  cases a <;> cases b <;> cases c <;>
    simp [instructionRowsMLE,instructionCubePoint,instructionCubeIndex,instruction_lerp_zero,instruction_lerp_one]

/-- Folding the column inputs preserves the already-proved compiler semantics;
no assertion is made that folding commutes with nonlinear constraints. -/
theorem instruction_folded_compile_eval (rows : Nat → Nat → Fp) (x : InstructionPoint3)
    (e : Expr) (c : InstructionPackedCircuit) (compiled : instructionLayerCompile e=some c) :
    instructionPackedEval (instructionRowsMLE rows x) c=
      e.evalWith (instructionAddEnv (instructionRowsMLE rows x)) :=
  instruction_layer_compile_eval e c compiled _

def instructionConstraintBatch (weights : Nat → Fp) (row : Nat → Fp) : Nat → List Expr → Fp
  | _,[] => 0
  | i,e::es => weights i * e.evalWith (instructionAddEnv row)+instructionConstraintBatch weights row (i+1) es

theorem instruction_constraint_batch_zero (weights : Nat → Fp) (row : Nat → Fp)
    (es : List Expr) (zero : ∀ e ∈ es,e.evalWith (instructionAddEnv row)=0) (start : Nat) :
    instructionConstraintBatch weights row start es=0 := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
    simp only [instructionConstraintBatch,zero e (List.mem_cons_self ..),
      ih (fun e he => zero e (List.mem_cons_of_mem _ he))]
    grind

def instructionEqCoordinate (z x : Fp) : Fp := (1-z)*(1-x)+z*x

def instructionEqPoint (z x : InstructionPoint3) : Fp :=
  instructionEqCoordinate z.1 x.1 * instructionEqCoordinate z.2.1 x.2.1 * instructionEqCoordinate z.2.2 x.2.2

/-- Polynomial evaluated by the proposed row-batching sumcheck: equality weight
multiplies the constraint evaluated on multilinearly extended columns. -/
def instructionAddSumcheckPolynomial (rows : Nat → Nat → Fp) (weights : Nat → Fp)
    (z x : InstructionPoint3) : Fp :=
  instructionEqPoint z x * instructionConstraintBatch weights (instructionRowsMLE rows x) 0 instructionAdd32RangeConstraints

def instructionAddSumcheckTarget (rows : Nat → Nat → Fp) (weights : Nat → Fp) (z : InstructionPoint3) : Fp :=
  (instructionCube3.map (fun b => instructionAddSumcheckPolynomial rows weights z (instructionCubePoint b))).foldr (·+·) 0

theorem instruction_sumcheck_boolean_value (rows : Nat → Nat → Fp) (weights : Nat → Fp)
    (z : InstructionPoint3) (b : InstructionCube3) :
    instructionAddSumcheckPolynomial rows weights z (instructionCubePoint b)=
      instructionEqPoint z (instructionCubePoint b) *
        instructionConstraintBatch weights (rows (instructionCubeIndex b)) 0 instructionAdd32RangeConstraints := by
  have eq : instructionRowsMLE rows (instructionCubePoint b)=rows (instructionCubeIndex b) := by
    funext col
    exact instruction_rows_mle_boolean rows b col
  simp only [instructionAddSumcheckPolynomial,eq]

theorem instruction_sum_map_zero {α : Type} (xs : List α) (f : α → Fp)
    (zero : ∀ x ∈ xs,f x=0) : (xs.map f).foldr (·+·) 0=0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,List.foldr_cons,zero a (List.mem_cons_self ..),
      ih (fun a ha => zero a (List.mem_cons_of_mem _ ha))]
    grind

/-- All 106 constraints at each of the eight rows imply the honest zero target,
for every choice of batching and equality-weight challenges. -/
theorem instruction_add_sumcheck_zero (rows : Nat → Nat → Fp)
    (holds : ∀ r,r<8 → instructionAdd32RangeHolds (rows r))
    (weights : Nat → Fp) (z : InstructionPoint3) : instructionAddSumcheckTarget rows weights z=0 := by
  apply instruction_sum_map_zero
  intro b hb
  rw [instruction_sumcheck_boolean_value,
    instruction_constraint_batch_zero weights _ _ (holds _ (instruction_cube_index_bound b)) 0]
  grind

theorem instruction_compiled_sumcheck_zero (rows : Nat → Nat → Fp)
    (holds : ∀ r,r<8 → instructionLayerAdd32Holds (rows r))
    (weights : Nat → Fp) (z : InstructionPoint3) : instructionAddSumcheckTarget rows weights z=0 :=
  instruction_add_sumcheck_zero rows (fun r hr => (instruction_layer_add32_holds_iff _).mp (holds r hr)) weights z

/-- Nonlinearity matters: two valid Boolean endpoints do not force a folded
Boolean constraint to vanish at an off-cube challenge. -/
theorem instruction_boolean_constraint_off_cube :
    (0 : Fp)*(0-1)=0 ∧ (1 : Fp)*(1-1)=0 ∧
    instructionLerp 0 1 2 * (instructionLerp 0 1 2-1)≠0 := by decide

set_option maxRecDepth 65536 in
/-- The existing source constraints are genuinely quadratic, independently of
how a later protocol chooses to batch them. -/
theorem instruction_sumcheck_source_degree :
    instructionAdd32RangeConstraints.all (fun e => decide (e.degree≤2))=true := by decide

def instructionCubeSuffix4 : List (Bool × Bool) :=
  [(false,false),(true,false),(false,true),(true,true)]

def instructionAddSumcheckRoundOne (rows : Nat → Nat → Fp) (weights : Nat → Fp)
    (z : InstructionPoint3) (t : Fp) : Fp :=
  (instructionCubeSuffix4.map (fun b => instructionAddSumcheckPolynomial rows weights z
    (t,if b.1 then 1 else 0,if b.2 then 1 else 0))).foldr (·+·) 0

/-- Exact first-round Boolean-sum consistency, with the same least-significant
row-bit convention used by the column folding and source table. -/
theorem instruction_sumcheck_first_round_consistency (rows : Nat → Nat → Fp)
    (weights : Nat → Fp) (z : InstructionPoint3) :
    instructionAddSumcheckRoundOne rows weights z 0 + instructionAddSumcheckRoundOne rows weights z 1=
      instructionAddSumcheckTarget rows weights z := by
  simp only [instructionAddSumcheckRoundOne,instructionAddSumcheckTarget,instructionCube3,
    instructionCubeSuffix4,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
    instructionCubePoint,Bool.false_eq_true,ite_false,ite_true]
  grind

theorem instruction_sumcheck_first_round_zero (rows : Nat → Nat → Fp)
    (holds : ∀ r,r<8 → instructionLayerAdd32Holds (rows r))
    (weights : Nat → Fp) (z : InstructionPoint3) :
    instructionAddSumcheckRoundOne rows weights z 0 + instructionAddSumcheckRoundOne rows weights z 1=0 := by
  rw [instruction_sumcheck_first_round_consistency,instruction_compiled_sumcheck_zero rows holds]

end NearCompression
