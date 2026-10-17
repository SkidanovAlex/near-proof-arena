import NearCompression.PreparedAddTransition
import NearCompression.PreparedCodeProvenance

/-! A local expression substitution from the original snapshot layout into the
605-column EXEC layout. The old PC selectors are ghost values, not the numeric
PC of execution. No global old-trace or old-PC-bound claim is made. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

def preparedExecAdvance : Expr :=
  .mul (.mul (.add (.const 1) (.neg (.col 41 false)))
    (.add (.const 1) (.neg (.col 430 false))))
    (.add (.const 1) (.neg (.col 469 false)))

def preparedExecOldCol (c : Nat) (next : Bool) : Expr :=
  if c<16 then
    if next then
      if c=0 then .add (.const 1) (.neg preparedExecAdvance)
      else if c=1 then preparedExecAdvance else .const 0
    else if c=0 then .const 1 else .const 0
  else .col (c+16) next

/-- Only the local ghost PC zero is selected. Fields of other records are zero. -/
def preparedExecOldPub (i : Nat) : Expr :=
  if 56≤i ∧ i<60 then .col (466+(i-56)) false
  else if 60≤i ∧ i<62 then preparedGasBits (470+16*(i-60))
  else if 62≤i ∧ i<66 then preparedGasBits (502+16*(i-62))
  else .const 0

def preparedExecSubstitute : Expr → Expr
  | .const n => .const n
  | .col c n => preparedExecOldCol c n
  | .pub i => preparedExecOldPub i
  | .isFirst => .isFirst
  | .isLast => .isLast
  | .isTransition => .isTransition
  | .add a b => .add (preparedExecSubstitute a) (preparedExecSubstitute b)
  | .mul a b => .mul (preparedExecSubstitute a) (preparedExecSubstitute b)
  | .neg a => .neg (preparedExecSubstitute a)

def preparedExecGhostEnv (env : Env Fp) : Env Fp :=
  { env with
    col := fun c n => (preparedExecOldCol c n).evalWith env
    pub := fun i => (preparedExecOldPub i).evalWith env }

theorem prepared_exec_substitute_eval (e : Expr) (env : Env Fp) :
    (preparedExecSubstitute e).evalWith env=e.evalWith (preparedExecGhostEnv env) := by
  induction e with
  | const n => rfl
  | col c n => rfl
  | pub i => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | add a b ha hb => simp only [preparedExecSubstitute,Expr.evalWith,ha,hb];rfl
  | mul a b ha hb => simp only [preparedExecSubstitute,Expr.evalWith,ha,hb];rfl
  | neg a ha => simp only [preparedExecSubstitute,Expr.evalWith,ha];rfl

def preparedExecGhostRow (row : Nat → Fp) (i : Nat) : Fp :=
  if i<16 then if i=0 then 1 else 0 else row (i+16)
def preparedExecGhostNext (row next pub : Nat → Fp) (i : Nat) : Fp :=
  (preparedExecOldCol i true).evalWith (preparedRowEnv row next pub 0 0)
def preparedExecGhostPub (row next pub : Nat → Fp) (i : Nat) : Fp :=
  (preparedExecOldPub i).evalWith (preparedRowEnv row next pub 0 0)

theorem prepared_exec_ghost_env (row next pub : Nat → Fp) :
    preparedExecGhostEnv (preparedRowEnv row next pub 0 0)=
    preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
      (preparedExecGhostPub row next pub) 0 0 := by
  unfold preparedExecGhostEnv preparedRowEnv
  congr 1
  funext c n
  cases n
  · simp [preparedExecGhostEnv,preparedExecOldCol,preparedExecGhostRow,preparedRowEnv,
      Expr.evalWith]
    split <;> (try simp_all [Expr.evalWith])
    split <;> rfl
  · rfl

theorem prepared_exec_substitute_row (e : Expr) (row next pub : Nat → Fp) :
    (preparedExecSubstitute e).evalWith (preparedRowEnv row next pub 0 0)=
      e.evalWith (preparedRowEnv (preparedExecGhostRow row)
        (preparedExecGhostNext row next pub) (preparedExecGhostPub row next pub) 0 0) := by
  rw [prepared_exec_substitute_eval,prepared_exec_ghost_env]

/-- Zero/one simplification is justified over the actual Fp environment. -/
def preparedExecSimplify : Expr → Expr
  | .add a b =>
    let x:=preparedExecSimplify a;let y:=preparedExecSimplify b
    if x=.const 0 then y else if y=.const 0 then x else .add x y
  | .mul a b =>
    let x:=preparedExecSimplify a;let y:=preparedExecSimplify b
    if x=.const 0 ∨ y=.const 0 then .const 0
    else if x=.const 1 then y else if y=.const 1 then x else .mul x y
  | .neg a => let x:=preparedExecSimplify a
              if x=.const 0 then .const 0 else .neg x
  | e => e

theorem prepared_exec_simplify_eval (e : Expr) (row next pub : Nat → Fp) :
    (preparedExecSimplify e).evalWith (preparedRowEnv row next pub 0 0)=
      e.evalWith (preparedRowEnv row next pub 0 0) := by
  induction e with
  | add a b ha hb =>
    simp only [preparedExecSimplify]
    split <;> rename_i h
    · have z : a.evalWith (preparedRowEnv row next pub 0 0)=0 := by rw [←ha,h];rfl
      simp only [Expr.evalWith,preparedRowEnv,hb,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
    · split <;> rename_i h'
      · have z : b.evalWith (preparedRowEnv row next pub 0 0)=0 := by rw [←hb,h'];rfl
        simp only [Expr.evalWith,preparedRowEnv,ha,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
      · simp only [Expr.evalWith,ha,hb]
  | mul a b ha hb =>
    simp only [preparedExecSimplify]
    split <;> rename_i h
    · rcases h with h|h
      · have z : a.evalWith (preparedRowEnv row next pub 0 0)=0 := by rw [←ha,h];rfl
        simp only [Expr.evalWith,preparedRowEnv,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
      · have z : b.evalWith (preparedRowEnv row next pub 0 0)=0 := by rw [←hb,h];rfl
        simp only [Expr.evalWith,preparedRowEnv,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
    · split <;> rename_i h'
      · have z : a.evalWith (preparedRowEnv row next pub 0 0)=1 := by rw [←ha,h'];rfl
        simp only [Expr.evalWith,preparedRowEnv,hb,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
      · split <;> rename_i h''
        · have z : b.evalWith (preparedRowEnv row next pub 0 0)=1 := by rw [←hb,h''];rfl
          simp only [Expr.evalWith,preparedRowEnv,ha,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
        · simp only [Expr.evalWith,ha,hb]
  | neg a ha =>
    simp only [preparedExecSimplify]
    split <;> rename_i h
    · have z : a.evalWith (preparedRowEnv row next pub 0 0)=0 := by rw [←ha,h];rfl
      simp only [Expr.evalWith,preparedRowEnv,z]; dsimp only [preparedRowEnv] at *; (try simp only [←Fp.ofNat_def] at *); grind
    · simp only [Expr.evalWith,ha]
  | _ => rfl

def preparedExecLower (e : Expr) : Expr := preparedExecSimplify (preparedExecSubstitute e)

theorem prepared_exec_lower_eval (e : Expr) (row next pub : Nat → Fp) :
    (preparedExecLower e).evalWith (preparedRowEnv row next pub 0 0)=
      e.evalWith (preparedRowEnv (preparedExecGhostRow row)
        (preparedExecGhostNext row next pub) (preparedExecGhostPub row next pub) 0 0) := by
  rw [preparedExecLower,prepared_exec_simplify_eval,prepared_exec_substitute_row]

/-- Canonical bounded-row projection; Boolean and SP constraints are actual
EXEC columns. The ghost PC contributes no restriction on the real numeric PC. -/
theorem prepared_exec_row_choices (row next pub : Nat → Fp)
    (boolean : ∀ i,i<605 → row i*(row i-1)=0)
    (sp : (preparedExecLower (preparedChoiceResidual 16 9)).evalWith
      (preparedRowEnv row next pub 0 0)=0) :
    preparedRowChoices (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
      (preparedExecGhostPub row next pub) 0 0 := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    change preparedExecGhostRow row i*(preparedExecGhostRow row i+ -(1:Fp))=0
    by_cases small : i<16
    · simp only [preparedExecGhostRow,small,ite_true]
      split <;> grind
    · have h:=boolean (i+16) (by omega)
      simp only [preparedExecGhostRow,small,ite_false]
      grind
  · simp only [preparedChoiceResidual,preparedExprSum,Expr.evalWith,preparedRowEnv,
      preparedExecGhostRow,Nat.reduceAdd,Nat.reduceLT,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [←Fp.ofNat_def]
    grind
  · exact (prepared_exec_lower_eval _ row next pub).symm.trans sp

def preparedExecStackWord (row : Nat → Fp) (slot : Nat) : Nat :=
  preparedStackWord (preparedExecGhostRow row) slot
def preparedExecResultWord (row : Nat → Fp) : Nat :=
  preparedAddResultWord (preparedExecGhostRow row)

/-- The actual selected stack operands, without supplied operand-lookup
assumptions. Source adapters below use structural AST equality, not this
conclusion, to establish these residual premises. -/
theorem prepared_exec_add_binop (row next pub : Nat → Fp)
    (boolean : ∀ i,i<605 → row i*(row i-1)=0)
    (sp : (preparedExecLower (preparedChoiceResidual 16 9)).evalWith
      (preparedRowEnv row next pub 0 0)=0)
    (active : row 41=0) (noBorrow : row 430=0)
    (isAdd : (preparedExecLower (preparedFetchPython 1)).evalWith
      (preparedRowEnv row next pub 0 0)=1)
    (depth : (preparedExecLower preparedAddDepthResidual).evalWith
      (preparedRowEnv row next pub 0 0)=0)
    (carries : ∀ i,i<2 → (preparedExecLower (preparedAddCarryPython i)).evalWith
      (preparedRowEnv row next pub 0 0)=0) :
    ∃ selected,selected<9 ∧ 2≤selected ∧
      (∀ i,i<9 → row (32+i)=if i=selected then 1 else 0) ∧
      Num.binop 32 0 (preparedExecStackWord row (selected-2))
        (preparedExecStackWord row (selected-1))=some (preparedExecResultWord row) := by
  have choices:=prepared_exec_row_choices row next pub boolean sp
  obtain ⟨selected,hs,he,hot,arithmetic⟩ := prepared_active_add_binop
    (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
    (preparedExecGhostPub row next pub) 0 0 choices
    (by simpa [preparedExecGhostRow] using active)
    (by simpa [preparedExecGhostRow] using noBorrow)
    ((prepared_exec_lower_eval _ row next pub).symm.trans isAdd)
    ((prepared_exec_lower_eval _ row next pub).symm.trans depth)
    (fun i hi => (prepared_exec_lower_eval _ row next pub).symm.trans (carries i hi))
  refine ⟨selected,hs,he,?_,arithmetic⟩
  intro i hi
  have h:=hot i hi
  simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using h

end NearCompression
