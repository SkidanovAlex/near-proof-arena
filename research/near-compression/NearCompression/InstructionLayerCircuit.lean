import NearCompression.InstructionRangeTrace

/-! A semantic lowering bridge, not a GKR protocol. Trees are balanced with
copy gates; the baseline deliberately does not share repeated subexpressions. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Every non-leaf gate reads only the immediately preceding layer. -/
inductive InstructionLayerCircuit : Nat → Type where
  | constant (n : Nat) : InstructionLayerCircuit 0
  | input (col : Nat) : InstructionLayerCircuit 0
  | copy {d : Nat} (a : InstructionLayerCircuit d) : InstructionLayerCircuit (d+1)
  | add {d : Nat} (a b : InstructionLayerCircuit d) : InstructionLayerCircuit (d+1)
  | mul {d : Nat} (a b : InstructionLayerCircuit d) : InstructionLayerCircuit (d+1)
  | neg {d : Nat} (a : InstructionLayerCircuit d) : InstructionLayerCircuit (d+1)

def instructionLayerEval {d : Nat} (row : Nat → Fp) : InstructionLayerCircuit d → Fp
  | .constant n => Fp.ofNat n
  | .input col => row col
  | .copy a => instructionLayerEval row a
  | .add a b => instructionLayerEval row a + instructionLayerEval row b
  | .mul a b => instructionLayerEval row a * instructionLayerEval row b
  | .neg a => -instructionLayerEval row a

def instructionLayerRaise {d : Nat} (a : InstructionLayerCircuit d) :
    (n : Nat) → InstructionLayerCircuit (d+n)
  | 0 => a
  | n+1 => .copy (instructionLayerRaise a n)

theorem instruction_layer_raise_eval {d : Nat} (a : InstructionLayerCircuit d)
    (row : Nat → Fp) (n : Nat) : instructionLayerEval row (instructionLayerRaise a n)=instructionLayerEval row a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

abbrev InstructionPackedCircuit := Sigma InstructionLayerCircuit

def instructionPackedEval (row : Nat → Fp) (c : InstructionPackedCircuit) : Fp :=
  instructionLayerEval row c.2

def instructionLayerJoin (mul : Bool) (a b : InstructionPackedCircuit) : InstructionPackedCircuit :=
  let left := instructionLayerRaise a.2 b.1
  let right := (Nat.add_comm b.1 a.1) ▸ instructionLayerRaise b.2 a.1
  ⟨a.1+b.1+1,if mul then .mul left right else .add left right⟩

theorem instruction_layer_cast_eval {d e : Nat} (h : d=e) (a : InstructionLayerCircuit d)
    (row : Nat → Fp) : instructionLayerEval row (h ▸ a)=instructionLayerEval row a := by
  subst e
  rfl

theorem instruction_layer_join_eval (mul : Bool) (a b : InstructionPackedCircuit) (row : Nat → Fp) :
    instructionPackedEval row (instructionLayerJoin mul a b)=
      if mul then instructionPackedEval row a * instructionPackedEval row b
      else instructionPackedEval row a + instructionPackedEval row b := by
  cases mul <;> simp only [instructionPackedEval,instructionLayerJoin,Bool.false_eq_true,
    ite_false,ite_true,instructionLayerEval,instruction_layer_cast_eval,instruction_layer_raise_eval]

/-- Unsupported AIR accesses are rejected rather than silently treated as zero. -/
def instructionLayerCompile : Expr → Option InstructionPackedCircuit
  | .const n => some ⟨0,.constant n⟩
  | .col col false => some ⟨0,.input col⟩
  | .add a b => do return instructionLayerJoin false (←instructionLayerCompile a) (←instructionLayerCompile b)
  | .mul a b => do return instructionLayerJoin true (←instructionLayerCompile a) (←instructionLayerCompile b)
  | .neg a => do
      let c ← instructionLayerCompile a
      return ⟨c.1+1,.neg c.2⟩
  | _ => none

/-- This measures the polynomial degree of a gate in its immediate input wires,
not the degree of the complete composed expression in trace cells. -/
def instructionLayerGateDegree {d : Nat} : InstructionLayerCircuit d → Nat
  | .constant _ => 0
  | .input _ | .copy _ | .neg _ | .add _ _ => 1
  | .mul _ _ => 2

theorem instruction_layer_gate_degree {d : Nat} (c : InstructionLayerCircuit d) :
    instructionLayerGateDegree c≤2 := by cases c <;> simp [instructionLayerGateDegree]

/-- Compilation succeeds exactly for the declared current-row fragment. -/
theorem instruction_layer_compile_local (e : Expr) :
    (instructionLayerCompile e).isSome=true ↔ instructionLocalExpr e := by
  induction e with
  | const n => simp [instructionLayerCompile,instructionLocalExpr]
  | col col next => cases next <;> simp [instructionLayerCompile,instructionLocalExpr]
  | add a b ia ib | mul a b ia ib =>
    simp only [instructionLocalExpr,←ia,←ib]
    cases ha : instructionLayerCompile a <;> cases hb : instructionLayerCompile b <;>
      simp [instructionLayerCompile,ha,hb]
  | neg a ia =>
    simp only [instructionLocalExpr,←ia]
    cases ha : instructionLayerCompile a <;> simp [instructionLayerCompile,ha]
  | pub i => simp [instructionLayerCompile,instructionLocalExpr]
  | isFirst => simp [instructionLayerCompile,instructionLocalExpr]
  | isLast => simp [instructionLayerCompile,instructionLocalExpr]
  | isTransition => simp [instructionLayerCompile,instructionLocalExpr]

theorem instruction_layer_compile_eval (e : Expr) (c : InstructionPackedCircuit)
    (compiled : instructionLayerCompile e=some c) (row : Nat → Fp) :
    instructionPackedEval row c=e.evalWith (instructionAddEnv row) := by
  induction e generalizing c with
  | const n => cases compiled; rfl
  | col col next =>
    cases next
    · cases compiled; rfl
    · simp [instructionLayerCompile] at compiled
  | add a b ia ib | mul a b ia ib =>
    cases ha : instructionLayerCompile a <;> cases hb : instructionLayerCompile b <;>
      simp [instructionLayerCompile,ha,hb] at compiled
    all_goals
      subst c
      rw [instruction_layer_join_eval,ia _ ha,ib _ hb]
      rfl
  | neg a ia =>
    cases ha : instructionLayerCompile a <;> simp [instructionLayerCompile,ha] at compiled
    subst c
    exact congrArg Neg.neg (ia _ ha)
  | pub i => simp [instructionLayerCompile] at compiled
  | isFirst => simp [instructionLayerCompile] at compiled
  | isLast => simp [instructionLayerCompile] at compiled
  | isTransition => simp [instructionLayerCompile] at compiled

/-- Accepted circuits agree with the actual AIR evaluator on any trace row. -/
theorem instruction_layer_compile_trace_eval (e : Expr) (c : InstructionPackedCircuit)
    (compiled : instructionLayerCompile e=some c) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    instructionPackedEval (tr.cell t r) c=e.eval tr t r pub := by
  have localExpr := (instruction_layer_compile_local e).mp (by rw [compiled]; rfl)
  rw [instruction_local_eval e tr t r pub localExpr]
  exact instruction_layer_compile_eval e c compiled _

/-- Local gate polynomial: columns 0/1 are predecessor values, column 2 is
this gate's output. Leaf inputs use column 0 as their boundary value. -/
def instructionLayerGateExpr {d : Nat} : InstructionLayerCircuit d → Expr
  | .constant n => .const n
  | .input _ | .copy _ => .col 0 false
  | .add _ _ => .add (.col 0 false) (.col 1 false)
  | .mul _ _ => .mul (.col 0 false) (.col 1 false)
  | .neg _ => .neg (.col 0 false)

def instructionLayerGateRelation {d : Nat} (c : InstructionLayerCircuit d) : Expr :=
  .add (.col 2 false) (.neg (instructionLayerGateExpr c))

def instructionLayerGateInputs {d : Nat} (row : Nat → Fp) (c : InstructionLayerCircuit d) : Nat → Fp
  | 0 => match c with
    | .constant _ => 0
    | .input col => row col
    | .copy a | .add a _ | .mul a _ | .neg a => instructionLayerEval row a
  | 1 => match c with
    | .add _ b | .mul _ b => instructionLayerEval row b
    | _ => 0
  | _ => instructionLayerEval row c

theorem instruction_layer_gate_relation_degree {d : Nat} (c : InstructionLayerCircuit d) :
    (instructionLayerGateRelation c).degree≤2 := by
  cases c <;> simp [instructionLayerGateRelation,instructionLayerGateExpr,Expr.degree]

theorem instruction_layer_gate_relation_holds {d : Nat} (c : InstructionLayerCircuit d) (row : Nat → Fp) :
    (instructionLayerGateRelation c).evalWith (instructionAddEnv (instructionLayerGateInputs row c))=0 := by
  cases c <;> simp only [instructionLayerGateRelation,instructionLayerGateExpr,Expr.evalWith,
    instructionAddEnv,instructionLayerGateInputs,instructionLayerEval] <;> grind

/-- Each original range-enforced addition constraint has an accepted lowering. -/
theorem instruction_layer_add32_compiles (e : Expr) (he : e ∈ instructionAdd32RangeConstraints) :
    ∃ c,instructionLayerCompile e=some c := by
  have accepted := (instruction_layer_compile_local e).mpr (instruction_range_constraints_local e he)
  cases eq : instructionLayerCompile e with
  | none => simp [eq] at accepted
  | some c => exact ⟨c,rfl⟩

/-- Every source constraint must be represented and its circuit output vanish.
This condition does not permit silently dropping rejected expressions. -/
def instructionLayerAdd32Holds (row : Nat → Fp) : Prop :=
  ∀ e ∈ instructionAdd32RangeConstraints, ∃ c,
    instructionLayerCompile e=some c ∧ instructionPackedEval row c=0

theorem instruction_layer_add32_holds_iff (row : Nat → Fp) :
    instructionLayerAdd32Holds row ↔ instructionAdd32RangeHolds row := by
  constructor
  · intro holds e he
    obtain ⟨c,hc,zero⟩ := holds e he
    rw [←instruction_layer_compile_eval e c hc row]
    exact zero
  · intro holds e he
    obtain ⟨c,hc⟩ := instruction_layer_add32_compiles e he
    exact ⟨c,hc,(instruction_layer_compile_eval e c hc row).trans (holds e he)⟩

theorem instruction_layer_add32_binop (row : Nat → Fp) (holds : instructionLayerAdd32Holds row) :
    Num.binop 32 0 (instructionAddWord row 0 1) (instructionAddWord row 2 3)=
      some (instructionAddWord row 4 5) :=
  instruction_add32_range_binop row ((instruction_layer_add32_holds_iff row).mp holds)

theorem instruction_layer_add32_witness (a b : UInt32) :
    instructionLayerAdd32Holds (instructionAdd32RangeWitness a b) :=
  (instruction_layer_add32_holds_iff _).mpr (instruction_add32_range_witness_holds a b)

end NearCompression
