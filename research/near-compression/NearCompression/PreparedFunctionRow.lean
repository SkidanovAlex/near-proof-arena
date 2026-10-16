import NearCompression.InstructionAddRange

/-! Actual Fp/Expr local row interfaces for the bounded prepared-function AIR.
Sums are reassociated relative to the Python balanced AST. No whole-VM theorem. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def preparedPCBase : Nat := 0
def preparedSPBase : Nat := 16
def preparedDoneColumn : Nat := 25
def preparedFailureColumn : Nat := 26
def preparedStackBase : Nat := 27
def preparedGasBase : Nat := 283
def preparedDifferenceBase : Nat := 347
def preparedBorrowBase : Nat := 411
def preparedResultBase : Nat := 415
def preparedCarryBase : Nat := 447
def preparedRowWidth : Nat := 449
def preparedCodePublicBase : Nat := 56

def preparedRowEnv (row next pub : Nat → Fp) (first last : Fp) : Env Fp :=
  ⟨Fp.ofNat,(·+·),(·*·),Neg.neg,(fun c n => if n then next c else row c),pub,
    first,last,1-last⟩

def preparedExprSum : Nat → (Nat → Expr) → Expr
  | 0,_ => .const 0
  | n+1,f => .add (f 0) (preparedExprSum n (fun i => f (i+1)))
def preparedFieldSum : Nat → (Nat → Fp) → Fp
  | 0,_ => 0
  | n+1,f => f 0 + preparedFieldSum n (fun i => f (i+1))
def preparedNatSum : Nat → (Nat → Nat) → Nat
  | 0,_ => 0
  | n+1,f => f 0 + preparedNatSum n (fun i => f (i+1))

def preparedFetch (field : Nat) : Expr :=
  preparedExprSum 16 (fun i => .mul (.col i false) (.pub (56+10*i+field)))
def preparedIndex (base count : Nat) : Expr :=
  preparedExprSum count (fun i => .mul (.const i) (.col (base+i) false))
def preparedStackLimb (slot limb : Nat) : Expr :=
  instructionBitExpr (27+32*slot+16*limb) 16
/-- Top-two selection, matching Python's sum over heights 2 through 8. -/
def preparedOperand (left : Bool) (limb : Nat) : Expr :=
  preparedExprSum 7 (fun i => .mul (.col (16+(i+2)) false)
    (preparedStackLimb (if left then i else i+1) limb))
def preparedBooleanResidual (col : Nat) : Expr := instructionBitConstraint col

def preparedChoiceResidual (base count : Nat) : Expr :=
  .add (preparedExprSum count (fun i => .col (base+i) false)) (.neg (.const 1))
def preparedRowChoices (row next pub : Nat → Fp) (first last : Fp) : Prop :=
  (∀ i,i<449 → (preparedBooleanResidual i).evalWith (preparedRowEnv row next pub first last)=0) ∧
  (preparedChoiceResidual 0 16).evalWith (preparedRowEnv row next pub first last)=0 ∧
  (preparedChoiceResidual 16 9).evalWith (preparedRowEnv row next pub first last)=0

theorem prepared_expr_sum_eval (n : Nat) (f : Nat → Expr) (env : Env Fp)
    (zero : env.ofNat 0=0) (add : ∀ a b,env.add a b=a+b) :
    (preparedExprSum n f).evalWith env=preparedFieldSum n (fun i => (f i).evalWith env) := by
  induction n generalizing f with
  | zero => exact zero
  | succ n ih => simp only [preparedExprSum,preparedFieldSum,Expr.evalWith,add,ih]

theorem prepared_sum_nat_bound (n : Nat) (f : Nat → Fp)
    (small : n < ZkFormal.Algebra.P) (bits : ∀ i,i<n → (f i).toNat≤1) :
    (preparedFieldSum n f).toNat=preparedNatSum n (fun i => (f i).toNat) ∧
    preparedNatSum n (fun i => (f i).toNat)≤n := by
  induction n generalizing f with
  | zero => exact ⟨rfl,by simp [preparedNatSum]⟩
  | succ n ih =>
    have tail := ih (fun i => f (i+1)) (by omega) (by intro i hi;exact bits (i+1) (by omega))
    have head := bits 0 (by omega)
    change (Fp.add (f 0) (preparedFieldSum n (fun i => f (i+1)))).toNat = _ ∧ _
    rw [Fp.toNat_add,tail.1]
    simp only [preparedNatSum]
    constructor
    · exact Nat.mod_eq_of_lt (by omega)
    · omega

theorem prepared_nat_sum_zero (n : Nat) (f : Nat → Nat)
    (zero : preparedNatSum n f=0) (i : Nat) (hi : i<n) : f i=0 := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    simp only [preparedNatSum] at zero
    cases i with
    | zero => omega
    | succ i => exact ih (fun i => f (i+1)) (by omega) i (by omega)

theorem prepared_nat_sum_one (n : Nat) (f : Nat → Nat)
    (sum : preparedNatSum n f=1) :
    ∃ i,i<n ∧ f i=1 ∧ ∀ j,j<n → j≠i → f j=0 := by
  induction n generalizing f with
  | zero => simp [preparedNatSum] at sum
  | succ n ih =>
    simp only [preparedNatSum] at sum
    by_cases h : f 0=1
    · refine ⟨0,by omega,h,?_⟩
      intro j hj ne
      cases j with
      | zero => contradiction
      | succ j => exact prepared_nat_sum_zero n (fun k => f (k+1)) (by omega) j (by omega)
    · have hz : f 0=0 := by omega
      obtain ⟨i,hi,hone,rest⟩ := ih (fun k => f (k+1)) (by omega)
      refine ⟨i+1,by omega,hone,?_⟩
      intro j hj ne
      cases j with
      | zero => exact hz
      | succ j => exact rest j (by omega) (by omega)

theorem prepared_onehot (n base : Nat) (row : Nat → Fp)
    (small : n<ZkFormal.Algebra.P) (bits : ∀ i,i<n → (row (base+i)).toNat≤1)
    (sum : preparedFieldSum n (fun i => row (base+i))=1) :
    ∃ selected,selected<n ∧ ∀ i,i<n → row (base+i)=if i=selected then 1 else 0 := by
  have bound := prepared_sum_nat_bound n (fun i => row (base+i)) small bits
  have hs : preparedNatSum n (fun i => (row (base+i)).toNat)=1 := by
    rw [←bound.1,sum];rfl
  obtain ⟨selected,hi,one,zero⟩ := prepared_nat_sum_one n _ hs
  refine ⟨selected,hi,?_⟩
  intro i hib
  by_cases h : i=selected
  · subst i;rw [if_pos rfl,←Fp.ofNat_toNat (row (base+selected)),one];rfl
  · rw [if_neg h,←Fp.ofNat_toNat (row (base+i)),zero i hib h];rfl

theorem prepared_row_boolean (row next pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last) (i : Nat) (hi : i<449) :
    (row i).toNat≤1 := by
  exact instruction_add_boolean_bound (row i) (h.1 i hi)

theorem prepared_row_pc_sp (row next pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last) :
    (∃ pc,pc<16 ∧ ∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
    (∃ sp,sp<9 ∧ ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) := by
  have hs (base count : Nat) (e : (preparedChoiceResidual base count).evalWith (preparedRowEnv row next pub first last)=0) :
      preparedFieldSum count (fun i => row (base+i))=1 := by
    simp only [preparedChoiceResidual,Expr.evalWith] at e
    rw [prepared_expr_sum_eval count _ _ rfl (by intros;rfl)] at e
    change preparedFieldSum count (fun i => row (base+i)) + -(1:Fp)=0 at e
    grind
  constructor
  · simpa using prepared_onehot 16 0 row (by decide) (by intro i hi;simpa using prepared_row_boolean row next pub first last h i (by omega)) (hs 0 16 h.2.1)
  · exact prepared_onehot 9 16 row (by decide) (by intro i hi;exact prepared_row_boolean row next pub first last h (16+i) (by omega)) (hs 16 9 h.2.2)


theorem prepared_sum_zero (n : Nat) (f : Nat → Fp)
    (h : ∀ i,i<n → f i=0) : preparedFieldSum n f=0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [preparedFieldSum]
    rw [h 0 (by omega),ih (fun i => f (i+1)) (by intro i hi;exact h (i+1) (by omega))]
    rfl

theorem prepared_sum_select (n selected : Nat) (selector values : Nat → Fp)
    (hi : selected<n) (onehot : ∀ i,i<n → selector i=if i=selected then 1 else 0) :
    preparedFieldSum n (fun i => selector i * values i)=values selected := by
  induction n generalizing selected selector values with
  | zero => omega
  | succ n ih =>
    cases selected with
    | zero =>
      simp only [preparedFieldSum]
      rw [onehot 0 (by omega)]
      have tail : preparedFieldSum n (fun i => selector (i+1)*values (i+1))=0 := by
        apply prepared_sum_zero
        intro i hi
        rw [onehot (i+1) (by omega)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
        grind
      rw [tail]
      grind
    | succ selected =>
      simp only [preparedFieldSum]
      rw [onehot 0 (by omega)]
      have ht := ih selected (fun i => selector (i+1)) (fun i => values (i+1)) (by omega) (by
        intro i hi
        simpa using onehot (i+1) (by omega))
      simp only [Ne.symm (Nat.succ_ne_zero selected),ite_false]
      grind

theorem prepared_fetch_selected (row next pub : Nat → Fp) (first last : Fp)
    (pc : Nat) (hpc : pc<16)
    (onehot : ∀ i,i<16 → row i=if i=pc then 1 else 0) (field : Nat) :
    (preparedFetch field).evalWith (preparedRowEnv row next pub first last)=pub (56+10*pc+field) := by
  unfold preparedFetch
  rw [prepared_expr_sum_eval 16 _ _ rfl (by intros;rfl)]
  exact prepared_sum_select 16 pc row (fun i => pub (56+10*i+field)) hpc onehot

theorem prepared_stack_limb_eval (row next pub : Nat → Fp) (first last : Fp)
    (slot limb : Nat) :
    (preparedStackLimb slot limb).evalWith (preparedRowEnv row next pub first last)=
    (instructionBitExpr (27+32*slot+16*limb) 16).evalWith (instructionAddEnv row) := by
  have h (n base : Nat) :
      (instructionBitExpr base n).evalWith (preparedRowEnv row next pub first last)=
      (instructionBitExpr base n).evalWith (instructionAddEnv row) := by
    induction n generalizing base with
    | zero => rfl
    | succ n ih =>
      change row base + Fp.ofNat 2 * (instructionBitExpr (base+1) n).evalWith (preparedRowEnv row next pub first last) =
        row base + Fp.ofNat 2 * (instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)
      rw [ih]
  exact h 16 _

theorem prepared_operand_selected (row next pub : Nat → Fp) (first last : Fp)
    (sp : Nat) (hsp : sp<9) (enough : 2≤sp)
    (onehot : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (left : Bool) (limb : Nat) :
    (preparedOperand left limb).evalWith (preparedRowEnv row next pub first last)=
    (preparedStackLimb (if left then sp-2 else sp-1) limb).evalWith
      (preparedRowEnv row next pub first last) := by
  unfold preparedOperand
  rw [prepared_expr_sum_eval 7 _ _ rfl (by intros;rfl)]
  have h := prepared_sum_select 7 (sp-2) (fun i => row (16+(i+2)))
    (fun i => (preparedStackLimb (if left then i else i+1) limb).evalWith (preparedRowEnv row next pub first last))
    (by omega) (by
      intro i hi
      rw [onehot (i+2) (by omega)]
      have eq : (i+2=sp) ↔ (i=sp-2) := by omega
      simp only [eq])
  change preparedFieldSum 7 (fun i => row (16+(i+2)) *
    (preparedStackLimb (if left then i else i+1) limb).evalWith (preparedRowEnv row next pub first last)) = _
  rw [h]
  have off : sp-2+1=sp-1 := by omega
  rw [off]

theorem prepared_stack_limb_bound (row next pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last) (slot limb : Nat)
    (hs : slot<8) (hl : limb<2) :
    ((preparedStackLimb slot limb).evalWith (preparedRowEnv row next pub first last)).toNat<65536 := by
  rw [prepared_stack_limb_eval]
  apply instruction_bit_expr_bound row 16 _ (by decide)
  intro i hi
  exact prepared_row_boolean row next pub first last h _ (by omega)

/-- Public fetch and both stack operand limbs follow from the actual choice residuals.
The depth premise is an explicit obligation of active-add control constraints. -/
theorem prepared_row_fetch_and_operands (row next pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last) :
    ∃ pc sp,pc<16 ∧ sp<9 ∧
      (∀ field,(preparedFetch field).evalWith (preparedRowEnv row next pub first last)=pub (56+10*pc+field)) ∧
      (2≤sp → ∀ left limb,(preparedOperand left limb).evalWith (preparedRowEnv row next pub first last)=
        (preparedStackLimb (if left then sp-2 else sp-1) limb).evalWith (preparedRowEnv row next pub first last)) := by
  obtain ⟨⟨pc,hpc,hp⟩,⟨sp,hsp,hs⟩⟩ := prepared_row_pc_sp row next pub first last h
  exact ⟨pc,sp,hpc,hsp,prepared_fetch_selected row next pub first last pc hpc hp,
    fun enough left limb => prepared_operand_selected row next pub first last sp hsp enough hs left limb⟩


/-- Exact balanced tree used for a power-of-two Python `sm` list. -/
def preparedBalancedSum (term : Nat → Expr) : Nat → Nat → Expr
  | 0,offset => term offset
  | depth+1,offset => .add (preparedBalancedSum term depth offset)
      (preparedBalancedSum term depth (offset+2^depth))
def preparedFetchPython (field : Nat) : Expr :=
  preparedBalancedSum (fun i => .mul (.col i false) (.pub (56+10*i+field))) 4 0

theorem prepared_balanced16_eval (term : Nat → Expr) (row next pub : Nat → Fp) (first last : Fp) :
    (preparedBalancedSum term 4 0).evalWith (preparedRowEnv row next pub first last)=
    (preparedExprSum 16 term).evalWith (preparedRowEnv row next pub first last) := by
  simp only [preparedBalancedSum,preparedExprSum,Expr.evalWith,preparedRowEnv,Nat.reducePow,Nat.reduceAdd,←Fp.ofNat_def]
  grind

theorem prepared_fetch_python_eval (field : Nat) (row next pub : Nat → Fp) (first last : Fp) :
    (preparedFetchPython field).evalWith (preparedRowEnv row next pub first last)=
    (preparedFetch field).evalWith (preparedRowEnv row next pub first last) :=
  prepared_balanced16_eval _ row next pub first last

/-- Exact two source choice residuals; the nine-element balanced sum is an
 eight-element tree plus its last leaf. -/
def preparedPCResidualPython : Expr :=
  .add (preparedBalancedSum (fun i => .col i false) 4 0) (.neg (.const 1))
def preparedSPResidualPython : Expr :=
  .add (.add (preparedBalancedSum (fun i => .col (16+i) false) 3 0) (.col 24 false)) (.neg (.const 1))

theorem prepared_python_choices (row next pub : Nat → Fp) (first last : Fp)
    (boolean : ∀ i,i<449 → (preparedBooleanResidual i).evalWith (preparedRowEnv row next pub first last)=0)
    (pc : preparedPCResidualPython.evalWith (preparedRowEnv row next pub first last)=0)
    (sp : preparedSPResidualPython.evalWith (preparedRowEnv row next pub first last)=0) :
    preparedRowChoices row next pub first last := by
  refine ⟨boolean,?_,?_⟩
  · unfold preparedPCResidualPython at pc
    simp only [Expr.evalWith] at pc
    rw [prepared_balanced16_eval] at pc
    simpa only [preparedChoiceResidual,Expr.evalWith,Nat.zero_add] using pc
  · simp only [preparedSPResidualPython,preparedBalancedSum,Expr.evalWith,preparedRowEnv,Nat.reducePow,Nat.reduceAdd] at sp
    simp only [preparedChoiceResidual,preparedExprSum,Expr.evalWith,preparedRowEnv,Nat.reduceAdd,←Fp.ofNat_def]
    simp only [←Fp.ofNat_def] at sp
    grind

def preparedAddDepthResidual : Expr :=
  .mul (.mul (.add (.const 1) (.neg (.col 25 false)))
      (.add (.const 1) (.neg (.col 414 false))))
    (.mul (preparedFetchPython 1) (.add (.col 16 false) (.col 17 false)))

theorem prepared_active_add_depth (row next pub : Nat → Fp) (first last : Fp)
    (sp : Nat) (hsp : sp<9) (onehot : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (active : row 25=0) (noBorrow : row 414=0)
    (isAdd : (preparedFetchPython 1).evalWith (preparedRowEnv row next pub first last)=1)
    (depth : preparedAddDepthResidual.evalWith (preparedRowEnv row next pub first last)=0) :
    2≤sp := by
  change ((1:Fp)+ -row 25) * ((1:Fp)+ -row 414) *
    ((preparedFetchPython 1).evalWith (preparedRowEnv row next pub first last)*(row 16+row 17))=0 at depth
  rw [active,noBorrow,isAdd] at depth
  have h0 := onehot 0 (by decide)
  have h1 := onehot 1 (by decide)
  simp only [Nat.reduceAdd] at h0 h1
  by_cases bad : 2≤sp
  · exact bad
  have cases : sp=0 ∨ sp=1 := by omega
  rcases cases with h | h <;> subst sp <;> simp only [ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero] at h0 h1 <;> grind


/-- Fee canonicality is inherited from the selected public code record; it is
 not a 64-bit value reduced into a single field element. -/
theorem prepared_fetch_fee_bounds (row next pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub (56+10*pc+(6+limb))).toNat<65536) :
    ∀ limb,limb<4 → ((preparedFetchPython (6+limb)).evalWith (preparedRowEnv row next pub first last)).toNat<65536 := by
  obtain ⟨⟨pc,hpc,hp⟩,_⟩ := prepared_row_pc_sp row next pub first last h
  intro limb hl
  rw [prepared_fetch_python_eval,prepared_fetch_selected row next pub first last pc hpc hp]
  exact publicBounds pc hpc limb hl

theorem prepared_opcode_selected (row next pub : Nat → Fp) (first last : Fp)
    (pc opcode : Nat) (hpc : pc<16)
    (onehot : ∀ i,i<16 → row i=if i=pc then 1 else 0)
    (code : ∀ tag,tag<4 → pub (56+10*pc+tag)=if tag=opcode then 1 else 0)
    (tag : Nat) (ht : tag<4) :
    (preparedFetchPython tag).evalWith (preparedRowEnv row next pub first last)=
      if tag=opcode then 1 else 0 := by
  rw [prepared_fetch_python_eval,prepared_fetch_selected row next pub first last pc hpc onehot]
  exact code tag ht

end NearCompression
