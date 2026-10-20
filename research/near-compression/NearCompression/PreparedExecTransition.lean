import NearCompression.PreparedExecAdapter
import NearCompression.PreparedStackCases

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm ZkFormal.Near

theorem prepared_exec_fetch_lower (field : Nat) (hf : field<10) :
    preparedExecLower (preparedFetchPython field)=
      preparedExecSimplify (if field<4 then .col (466+field) false
      else if field<6 then preparedGasBits (470+16*(field-4))
      else preparedGasBits (502+16*(field-6))) := by
  have cases : field=0 ∨ field=1 ∨ field=2 ∨ field=3 ∨ field=4 ∨ field=5 ∨
      field=6 ∨ field=7 ∨ field=8 ∨ field=9 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst field <;> rfl

theorem prepared_exec_advance_lower :
    preparedExecLower preparedAdvanceExpr=preparedExecAdvance := by rfl

/-- Exact balanced source SP choice is transported to the old proof interface. -/
theorem prepared_exec_python_choices (row next pub : Nat → Fp)
    (boolean : ∀ i,i<605 → row i*(row i-1)=0)
    (sp : (preparedExecLower preparedSPResidualPython).evalWith
      (preparedRowEnv row next pub 0 0)=0) :
    preparedRowChoices (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
      (preparedExecGhostPub row next pub) 0 0 := by
  apply prepared_python_choices
  · intro i hi
    change preparedExecGhostRow row i*(preparedExecGhostRow row i+ -(1:Fp))=0
    by_cases small : i<16
    · simp only [preparedExecGhostRow,small,ite_true]
      split <;> grind
    · have h:=boolean (i+16) (by omega)
      simp only [preparedExecGhostRow,small,ite_false]
      grind
  · simp only [preparedPCResidualPython,preparedBalancedSum,Expr.evalWith,preparedRowEnv,
      preparedExecGhostRow,Nat.reduceAdd,Nat.reducePow,Nat.reduceLT,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [←Fp.ofNat_def]
    grind
  · exact (prepared_exec_lower_eval _ row next pub).symm.trans sp

/-- PC selectors used only inside the inherited local proof are constructed
from the advance expression. Their update equations are identities, not
constraints on the numeric 32-bit EXEC program counter. -/
theorem prepared_exec_ghost_pc_step (row next pub : Nat → Fp) (i : Nat) (hi : i<16) :
    (preparedPCStepPython i).evalWith
      (preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
        (preparedExecGhostPub row next pub) 0 0)=0 := by
  have advance := prepared_exec_lower_eval preparedAdvanceExpr row next pub
  rw [prepared_exec_advance_lower] at advance
  change (1:Fp)*(preparedExecGhostNext row next pub i+
    -(((1:Fp)+ -preparedAdvanceExpr.evalWith
      (preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
        (preparedExecGhostPub row next pub) 0 0))*preparedExecGhostRow row i+
      preparedAdvanceExpr.evalWith
      (preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
        (preparedExecGhostPub row next pub) 0 0)*
      (if i=0 then (.const 0:Expr) else .col (i-1) false).evalWith
      (preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
        (preparedExecGhostPub row next pub) 0 0)))=0
  rw [←advance]
  by_cases z : i=0
  · subst i
    simp only [preparedExecGhostNext,preparedExecOldCol,preparedExecGhostRow,
      Nat.reduceLT,Nat.reduceEqDiff,ite_true,Expr.evalWith,preparedRowEnv]
    simp only [←Fp.ofNat_def]
    grind
  · by_cases o : i=1
    · subst i
      simp only [preparedExecGhostNext,preparedExecOldCol,preparedExecGhostRow,
        Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,ite_true,ite_false,Expr.evalWith,preparedRowEnv]
      simp only [←Fp.ofNat_def]
      grind
    · have prev : i-1<16 := by omega
      have pn : i-1≠0 := by omega
      simp only [preparedExecGhostNext,preparedExecOldCol,preparedExecGhostRow,
        hi,z,o,prev,pn,ite_true,ite_false,Expr.evalWith,preparedRowEnv]
      simp only [←Fp.ofNat_def]
      grind

theorem prepared_exec_transition_holds (row next pub : Nat → Fp)
    (sp : (preparedExecLower preparedSPStepPython).evalWith (preparedRowEnv row next pub 0 0)=0)
    (stack : ∀ slot,slot<8 → ∀ limb,limb<2 →
      (preparedExecLower (preparedStackStepPython slot limb)).evalWith
        (preparedRowEnv row next pub 0 0)=0) :
    PreparedAddTransitionHolds (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
      (preparedExecGhostPub row next pub) := by
  intro e he
  simp only [preparedAddTransitionConstraints,List.mem_append,List.mem_map,List.mem_cons,
    List.mem_singleton,List.mem_flatMap,List.mem_range,List.not_mem_nil,or_false] at he
  rcases he with (⟨i,hi,rfl⟩ | (rfl|rfl)) | ⟨slot,hs,limb,hl,rfl⟩
  · exact prepared_exec_ghost_pc_step row next pub i hi
  · change preparedAdvanceExpr.evalWith _*preparedExecGhostRow row 15+ -(0:Fp)=0
    simp only [preparedExecGhostRow,Nat.reduceLT,Nat.reduceEqDiff,ite_true,ite_false]
    grind
  · exact (prepared_exec_lower_eval _ row next pub).symm.trans sp
  · exact (prepared_exec_lower_eval _ row next pub).symm.trans (stack slot hs limb hl)

/-- Structural source provenance, permitting only proved zero/one
normalization. This is not an assumed semantic residual equation. -/
def PreparedExecHasSource (table : Table) (e : Expr) : Prop :=
  ∃ original, original∈table.constraints ∧ preparedNoFirst original ∧
    preparedExecSimplify original=preparedExecLower e

theorem prepared_exec_source_eval (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (e : Expr) (source : PreparedExecHasSource table e) :
    (preparedExecLower e).evalWith
      (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 0 0)=0 := by
  obtain ⟨original,member,nofirst,eq⟩:=source
  rw [←eq,prepared_exec_simplify_eval]
  exact prepared_table_nonlast_eval table tr t r pub localH nonlast original member nofirst

structure PreparedExecLocalSource (table : Table) : Prop where
  boolean : ∀ i,i<605 → preparedGasBoolean i∈table.constraints
  spChoice : PreparedExecHasSource table preparedSPResidualPython
  spStep : PreparedExecHasSource table preparedSPStepPython
  stackStep : ∀ slot,slot<8 → ∀ limb,limb<2 →
    PreparedExecHasSource table (preparedStackStepPython slot limb)
  addDepth : PreparedExecHasSource table preparedAddDepthResidual
  addCarry : ∀ limb,limb<2 → PreparedExecHasSource table (preparedAddCarryPython limb)

theorem prepared_exec_table_boolean (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (hr : r<tr.height t)
    (source : PreparedExecLocalSource table) (i : Nat) (hi : i<605) :
    tr.cell t r i*(tr.cell t r i-1)=0 := by
  have h:=localH.constr r hr _ (source.boolean i hi)
  change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
  grind

theorem prepared_exec_table_projection (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (source : PreparedExecLocalSource table) :
    let row:=preparedExecGhostRow (tr.cell t r)
    let next:=preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    let fields:=preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    preparedRowChoices row next fields 0 0 ∧ PreparedAddTransitionHolds row next fields := by
  constructor
  · exact prepared_exec_python_choices _ _ _
      (prepared_exec_table_boolean table tr t r pub localH (by omega) source)
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.spChoice)
  · exact prepared_exec_transition_holds _ _ _
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.spStep)
      (fun slot hs limb hl=>prepared_exec_source_eval table tr t r pub localH nonlast _
        (source.stackStep slot hs limb hl))

theorem prepared_exec_table_add (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (source : PreparedExecLocalSource table)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (isAdd : tr.cell t r 467=1) :
    ∃ selected,selected<9 ∧ 2≤selected ∧
      (∀ i,i<9 → tr.cell t r (32+i)=if i=selected then 1 else 0) ∧
      Num.binop 32 0 (preparedExecStackWord (tr.cell t r) (selected-2))
        (preparedExecStackWord (tr.cell t r) (selected-1))=
          some (preparedExecResultWord (tr.cell t r)) := by
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source
  have op : (preparedFetchPython 1).evalWith
      (preparedRowEnv (preparedExecGhostRow (tr.cell t r))
        (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
        (preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) 0 0)=1 := by
    rw [←prepared_exec_lower_eval]
    exact isAdd
  obtain ⟨selected,hs,he,hot,arith⟩:=prepared_active_add_binop _ _ _ 0 0 projection.1
    (by simpa [preparedExecGhostRow] using active)
    (by simpa [preparedExecGhostRow] using noBorrow) op
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.addDepth))
    (fun i hi=>(prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ (source.addCarry i hi)))
  refine ⟨selected,hs,he,?_,arith⟩
  intro i hi
  have h:=hot i hi
  simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
    Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

end NearCompression
