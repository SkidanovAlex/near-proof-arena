import NearCompression.PreparedAddTransition
import NearCompression.PreparedGasPublicBridge

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

def preparedNoFirst : Expr → Prop
  | .isFirst => False
  | .add a b | .mul a b => preparedNoFirst a ∧ preparedNoFirst b
  | .neg a => preparedNoFirst a
  | _ => True

theorem prepared_no_first_eval (e : Expr) (h : preparedNoFirst e)
    (row next pub : Nat → Fp) (first other last : Fp) :
    e.evalWith (preparedRowEnv row next pub first last)=e.evalWith (preparedRowEnv row next pub other last) := by
  induction e with
  | const n => rfl
  | col n b => rfl
  | pub n => rfl
  | isFirst => exact False.elim h
  | isLast => rfl
  | isTransition => rfl
  | add a b ia ib =>
    change a.evalWith _+b.evalWith _=a.evalWith _+b.evalWith _
    rw [ia h.1,ib h.2]
  | mul a b ia ib =>
    change a.evalWith _*b.evalWith _=a.evalWith _*b.evalWith _
    rw [ia h.1,ib h.2]
  | neg a ih =>
    change -a.evalWith _ = -a.evalWith _
    rw [ih h]

theorem prepared_table_nonlast_eval (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : ZkFormal.Near.TableLocal table tr t pub)
    (next : r+1<tr.height t) (e : Expr) (member : e∈table.constraints) (nf : preparedNoFirst e) :
    e.evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) 0 0)=0 := by
  have h:=localH.constr r (by omega) e member
  rw [Expr.eval,prepared_gas_row_env] at h
  have notLast : ¬r+1=tr.height t := by omega
  rw [Nat.mod_eq_of_lt next,if_neg notLast] at h
  rw [prepared_no_first_eval e nf _ _ _ _ 0 0] at h
  exact h

theorem prepared_choices_recontext (row next other pub : Nat → Fp) (first last : Fp)
    (h : preparedRowChoices row next pub first last) : preparedRowChoices row other pub 0 0 := by
  refine ⟨h.1,?_,?_⟩
  · simpa only [preparedChoiceResidual,preparedExprSum,Expr.evalWith,preparedRowEnv,Bool.false_eq_true,ite_false] using h.2.1
  · simpa only [preparedChoiceResidual,preparedExprSum,Expr.evalWith,preparedRowEnv,Bool.false_eq_true,ite_false] using h.2.2

theorem prepared_table_row_choices (table : Table) (middle tail : List Expr)
    (source : table.constraints=preparedGasSourceConstraints middle tail)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (hr : r<tr.height t) (other : Nat → Fp) :
    preparedRowChoices (tr.cell t r) other (fun i => pub.getD i 0) 0 0 := by
  have h:=prepared_gas_extract_source middle tail (tr.cell t r)
    (tr.cell t ((r+1)%tr.height t)) pub (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0) (by
      intro e he
      have h:=localH.constr r hr e (by rw [source];exact he)
      rw [Expr.eval,prepared_gas_row_env] at h
      exact h)
  exact prepared_choices_recontext _ _ other _ _ _ h.2

theorem prepared_transition_no_first (e : Expr) (h : e∈preparedAddTransitionConstraints) : preparedNoFirst e := by
  simp only [preparedAddTransitionConstraints,List.mem_append] at h
  rcases h with (hp|hc)|hs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp hp
    by_cases hi:i=0 <;> simp [preparedPCStepPython,preparedTransitionEq,preparedAdvanceExpr,
      preparedSuccessExpr,preparedActiveExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst,hi]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl <;>
      simp [preparedPCOverflowPython,preparedSPStepPython,preparedTransitionEq,preparedSPIndexPython,
        preparedAdvanceExpr,preparedSuccessExpr,preparedActiveExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst]
  · obtain ⟨slot,_,hs⟩:=List.mem_flatMap.mp hs
    obtain ⟨limb,_,rfl⟩:=List.mem_map.mp hs
    by_cases hi:slot+2≤8 <;>
      simp [preparedStackStepPython,preparedTransitionEq,preparedTransitionBits,preparedSuccessExpr,
        preparedActiveExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst,hi]

theorem prepared_transition_source_member (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (e : Expr) (he : e∈preparedAddTransitionConstraints) : e∈preparedAddTransitionSource prefixPart middle dead := by
  simp only [preparedAddTransitionSource,List.mem_append]
  simp only [preparedAddTransitionConstraints,List.mem_append] at he
  rcases he with (hp|hc)|hs
  · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
  · exact Or.inl (Or.inl (Or.inr hc))
  · obtain ⟨slot,hslot,hl⟩:=List.mem_flatMap.mp hs
    obtain ⟨limb,hlimb,rfl⟩:=List.mem_map.mp hl
    exact Or.inr (List.mem_flatMap.mpr ⟨slot,hslot,List.mem_flatMap.mpr ⟨limb,hlimb,by simp⟩⟩)

theorem prepared_table_add_transitions (table : Table) (prefixPart middle : List Expr)
    (dead : Nat → Nat → Expr) (source : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (next : r+1<tr.height t) :
    PreparedAddTransitionHolds (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) := by
  intro e he
  exact prepared_table_nonlast_eval table tr t r pub localH next e
    (by rw [source];exact prepared_transition_source_member prefixPart middle dead e he)
    (prepared_transition_no_first e he)

def preparedGasStepPython (limb : Nat) : Expr :=
  preparedTransitionEq (preparedTransitionBits (283+16*limb) true)
    (.add (.mul preparedSuccessExpr (preparedTransitionBits (347+16*limb) false))
      (.mul (.add (.const 1) (.neg preparedSuccessExpr)) (preparedTransitionBits (283+16*limb) false)))
def preparedGasValue (row : Nat → Fp) (pub : List Fp) : Nat :=
  preparedGasWord (fun i => (preparedGasLimb row pub 283 i).toNat)
def preparedFeeValue (row : Nat → Fp) (pub : List Fp) : Nat :=
  preparedGasWord (fun i => (preparedGasFee row pub i).toNat)


theorem prepared_next_gas_success (row next : Nat → Fp) (pub : List Fp)
    (gasH : PreparedGasHolds row pub)
    (feeBounds : ∀ i,i<4 → (preparedGasFee row pub i).toNat<65536)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next (fun i => pub.getD i 0) 0 0)=1)
    (noBorrow : row 414=0)
    (updates : ∀ i,i<4 → (preparedGasStepPython i).evalWith (preparedRowEnv row next (fun i => pub.getD i 0) 0 0)=0) :
    preparedGasValue next pub=preparedGasValue row pub-preparedFeeValue row pub := by
  have limbs (i : Nat) (hi : i<4) : preparedGasLimb next pub 283 i=preparedGasLimb row pub 347 i := by
    have h:=updates i hi
    simp only [preparedGasStepPython,preparedTransitionEq,Expr.evalWith] at h
    rw [success,prepared_transition_bits_horner,prepared_transition_bits_horner,prepared_transition_bits_horner] at h
    unfold preparedGasLimb
    rw [prepared_gas_bits_horner,prepared_gas_bits_horner]
    change (1:Fp)*(_+ -((1:Fp)*_+((1:Fp)+ -1)*_))=0 at h
    grind
  have word : preparedGasValue next pub=preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat) := by
    simp only [preparedGasValue,preparedGasWord]
    rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]
  have total:=prepared_gas_nat_total (fun i => (preparedGasLimb row pub 283 i).toNat)
    (fun i => (preparedGasFee row pub i).toNat) (fun i => (preparedGasLimb row pub 347 i).toNat)
    (fun i => (row (411+i)).toNat) (prepared_gas_limb_equation row pub gasH feeBounds)
  change preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat)+preparedFeeValue row pub=
    preparedGasValue row pub+18446744073709551616*(row 414).toNat at total
  rw [noBorrow] at total
  change preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat)+preparedFeeValue row pub=preparedGasValue row pub+0 at total
  rw [word]
  omega

/-- Source `eq(...,0)` includes an explicit subtraction of zero. -/
def preparedAddDepthSource : Expr := .add preparedAddDepthResidual (.neg (.const 0))
def preparedFailureInvariantPython : Expr :=
  .add (.mul (.col 26 false) preparedActiveExpr) (.neg (.const 0))
def preparedDoneStepPython : Expr :=
  preparedTransitionEq (.col 25 true) (.add (.col 25 false)
    (.add (.mul preparedActiveExpr (.col 414 false)) (.mul preparedSuccessExpr (preparedFetchPython 3))))
def preparedFailureStepPython : Expr :=
  preparedTransitionEq (.col 26 true) (.add (.col 26 false) (.mul preparedActiveExpr (.col 414 false)))

theorem prepared_success_flags (row next pub : Nat → Fp)
    (active : row 25=0) (noBorrow : row 414=0)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (notEnd : (preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0)=0)
    (inv : preparedFailureInvariantPython.evalWith (preparedRowEnv row next pub 0 0)=0)
    (done : preparedDoneStepPython.evalWith (preparedRowEnv row next pub 0 0)=0)
    (failed : preparedFailureStepPython.evalWith (preparedRowEnv row next pub 0 0)=0) :
    row 26=0 ∧ next 25=0 ∧ next 26=0 := by
  change row 26*((1:Fp)+ -row 25)+ -(0:Fp)=0 at inv
  change (1:Fp)*(next 25+ -(row 25+(((1:Fp)+ -row 25)*row 414+
    preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*(preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0))))=0 at done
  change (1:Fp)*(next 26+ -(row 26+((1:Fp)+ -row 25)*row 414))=0 at failed
  rw [active] at inv
  rw [active,noBorrow,success,notEnd] at done
  rw [active,noBorrow] at failed
  grind

/-- Full TableLocal supplies all arithmetic/selection/update validity premises.
The shape equalities and member facts are structural source-AST obligations.
CODE provenance and full Wasm frames/entry/exit are not asserted here. -/
theorem prepared_table_local_add (table : Table) (gasMiddle gasTail prefixPart transitionMiddle : List Expr)
    (dead : Nat → Nat → Expr)
    (gasSource : table.constraints=preparedGasSourceConstraints gasMiddle gasTail)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart transitionMiddle dead)
    (depthMember : preparedAddDepthSource∈table.constraints)
    (flagMembers : ∀ e∈[preparedFailureInvariantPython,preparedDoneStepPython,preparedFailureStepPython],e∈table.constraints)
    (carryMembers : ∀ i,i<2 → preparedAddCarryPython i∈table.constraints)
    (gasMembers : ∀ i,i<4 → preparedGasStepPython i∈table.constraints)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicAdd : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
      pub.getD (56+10*pc+tag) 0=if tag=1 then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub) :
    let row:=tr.cell t r
    let next:=tr.cell t (r+1)
    row 26=0 ∧ next 25=0 ∧ next 26=0 ∧
    preparedGasValue next pub=preparedGasValue row pub-preparedFeeValue row pub ∧
    ∃ pc sp,pc<15 ∧ 2≤sp ∧ sp<9 ∧
      (∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
      (∀ i,i<16 → next i=if i=pc+1 then 1 else 0) ∧
      (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
      (∀ i,i<9 → next (16+i)=if i=sp-1 then 1 else 0) ∧
      Num.binop 32 0 (preparedStackWord row (sp-2)) (preparedStackWord row (sp-1))=some (preparedAddResultWord row) ∧
      (∀ slot,slot<8 → preparedStackWord next slot=if slot=sp-2 then preparedAddResultWord row
        else if slot=sp-1 then 0 else preparedStackWord row slot) := by
  let row:=tr.cell t r
  let next:=tr.cell t (r+1)
  let pf:=fun i => pub.getD i 0
  have choices : preparedRowChoices row next pf 0 0 :=
    prepared_table_row_choices table gasMiddle gasTail gasSource tr t r pub localH (by omega) next
  have nextChoices : preparedRowChoices next next pf 0 0 :=
    prepared_table_row_choices table gasMiddle gasTail gasSource tr t (r+1) pub localH nonlast next
  have extracted:=prepared_gas_extract_source gasMiddle gasTail row
    (tr.cell t ((r+1)%tr.height t)) pub (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0) (by
      intro e he
      have h:=localH.constr r (by omega) e (by rw [gasSource];exact he)
      rw [Expr.eval,prepared_gas_row_env] at h
      exact h)
  have feeBounds:=prepared_gas_public_fee_bounds row next pub 0 0 choices publicBounds
  have borrow:=prepared_gas_borrow_sound row pub extracted.1 feeBounds
  have zeroNat : (row 414).toNat=0 := borrow.2.1.mpr enoughGas
  have noBorrow : row 414=0 := by rw [←Fp.ofNat_toNat (row 414),zeroNat];rfl
  obtain ⟨⟨pc,hpc,hp⟩,_⟩:=prepared_row_pc_sp row next pf 0 0 choices
  have selected : row pc=1 := by simpa only [ite_true] using hp pc hpc
  have op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pf 0 0)=if i=1 then 1 else 0 := by
    intro i hi
    exact prepared_opcode_selected row next pf 0 0 pc 1 hpc hp (publicAdd pc hpc selected) i hi
  have success := (prepared_success_advance row next pf active noBorrow op).1
  have updates : ∀ i,i<4 → (preparedGasStepPython i).evalWith (preparedRowEnv row next pf 0 0)=0 := by
    intro i hi
    apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (gasMembers i hi)
    simp [preparedGasStepPython,preparedTransitionEq,preparedTransitionBits,preparedSuccessExpr,preparedActiveExpr,preparedBalancedSum,preparedNoFirst]
  have depth : preparedAddDepthResidual.evalWith (preparedRowEnv row next pf 0 0)=0 := by
    have h:=prepared_table_nonlast_eval table tr t r pub localH nonlast _ depthMember (by
      simp [preparedAddDepthSource,preparedAddDepthResidual,preparedFetchPython,preparedBalancedSum,preparedNoFirst])
    change preparedAddDepthResidual.evalWith (preparedRowEnv row next pf 0 0)+ -(0:Fp)=0 at h
    grind
  have flags : row 26=0 ∧ next 25=0 ∧ next 26=0 := by
    apply prepared_success_flags row next pf active noBorrow success (by simpa using op 3 (by decide))
    · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (flagMembers _ (by simp))
      simp [preparedFailureInvariantPython,preparedActiveExpr,preparedNoFirst]
    · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (flagMembers _ (by simp))
      simp [preparedDoneStepPython,preparedTransitionEq,preparedActiveExpr,preparedSuccessExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst]
    · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (flagMembers _ (by simp))
      simp [preparedFailureStepPython,preparedTransitionEq,preparedActiveExpr,preparedNoFirst]
  have carries : ∀ i,i<2 → (preparedAddCarryPython i).evalWith (preparedRowEnv row next pf 0 0)=0 := by
    intro i hi
    apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (carryMembers i hi)
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl|rfl <;>
      simp [preparedAddCarryPython,preparedSuccessfulAdd,preparedFetchPython,preparedOperandPython,
        preparedOperandTermPython,preparedGasBits,preparedGasSumTree,preparedBalancedSum,preparedNoFirst]
  exact ⟨flags.1,flags.2.1,flags.2.2,prepared_next_gas_success row next pub extracted.1 feeBounds success noBorrow updates,
    prepared_add_transition_sound row next pf choices nextChoices
      (prepared_table_add_transitions table prefixPart transitionMiddle dead transitionSource tr t r pub localH nonlast)
      active noBorrow op depth carries⟩

end NearCompression
