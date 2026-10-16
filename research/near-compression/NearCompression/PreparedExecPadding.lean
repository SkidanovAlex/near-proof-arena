import NearCompression.PreparedLiteralRunCall
set_option maxRecDepth 65536

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

def PreparedExecSnapshotEq (row next : Nat → Fp) : Prop :=
  next 41=row 41 ∧ next 42=row 42 ∧ preparedExecWord64 next 299=preparedExecWord64 row 299 ∧
  preparedCodeExecPC next=preparedCodeExecPC row ∧
  (∀ i,i<9 → next (32+i)=row (32+i)) ∧
  (∀ slot,slot<8 → preparedExecStackWord next slot=preparedExecStackWord row slot)

theorem prepared_exec_choices_at (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (hr : r<tr.height t) (source : PreparedExecClosureSource table)
    (next fields : Nat → Fp) : preparedRowChoices (preparedExecGhostRow (tr.cell t r)) next fields 0 0 := by
  apply prepared_python_choices
  · intro i hi
    change preparedExecGhostRow (tr.cell t r) i*(preparedExecGhostRow (tr.cell t r) i+ -(1:Fp))=0
    by_cases small : i<16
    · simp only [preparedExecGhostRow,small,ite_true]
      split <;> grind
    · have h:=prepared_exec_table_boolean table tr t r pub localH hr source.localSource (i+16) (by omega)
      simp only [preparedExecGhostRow,small,ite_false]
      grind
  · simp only [preparedPCResidualPython,preparedBalancedSum,Expr.evalWith,preparedRowEnv,
      preparedExecGhostRow,Nat.reduceAdd,Nat.reducePow,Nat.reduceLT,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [←Fp.ofNat_def]
    grind
  · have h:=localH.constr r hr _ source.sp
    simp only [preparedExecSPChoice,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      Nat.reduceAdd,Nat.reducePow,Bool.false_eq_true,ite_false] at h
    simp only [preparedSPResidualPython,preparedBalancedSum,Expr.evalWith,preparedRowEnv,
      preparedExecGhostRow,Nat.reduceAdd,Nat.reducePow,Nat.reduceLT,ite_false]
    exact h

theorem prepared_exec_ghost_quiet (row next pub : Nat → Fp)
    (advance : preparedExecAdvance.evalWith (preparedRowEnv row next pub 0 0)=0) :
    preparedExecGhostNext row next pub=preparedExecGhostRow next := by
  funext i
  by_cases small:i<16
  · simp only [preparedExecGhostNext,preparedExecOldCol,preparedExecGhostRow,small,ite_true]
    by_cases z:i=0
    · simp only [z,ite_true,Expr.evalWith,preparedRowEnv]
      change (1:Fp)+ -preparedExecAdvance.evalWith (preparedRowEnv row next pub 0 0)=1
      rw [advance];grind
    · simp only [z,ite_false]
      by_cases o:i=1
      · simp only [o,ite_true]
        exact advance
      · simp only [o,ite_false];rfl
  · simp only [preparedExecGhostNext,preparedExecOldCol,preparedExecGhostRow,small,ite_false,
      Expr.evalWith,preparedRowEnv,ite_true]

/-- A zero advance and zero const/add/drop effects preserve numeric PC, live
height, and every stack word. Applies to both terminal transitions and padding. -/
theorem prepared_exec_quiet (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (source : PreparedExecClosureSource table) (pcSource : PreparedExecPCSource table)
    (advance : preparedExecPCAdvance.eval tr t r pub=0)
    (quiet : ∀ i,i<3 → preparedExecGasSuccess.eval tr t r pub*tr.cell t r (466+i)=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r) ∧
    (∀ i,i<9 → tr.cell t (r+1) (32+i)=tr.cell t r (32+i)) ∧
    (∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=preparedExecStackWord (tr.cell t r) slot) := by
  let row:=tr.cell t r
  let next:=tr.cell t (r+1)
  let fields:=fun i=>pub.getD i 0
  have adv : preparedExecAdvance.evalWith (preparedRowEnv row next fields 0 0)=0 := advance
  have ghost:=prepared_exec_ghost_quiet row next fields adv
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source.localSource
  have nextChoices:=prepared_exec_choices_at table tr t (r+1) pub localH nonlast source
    (preparedExecGhostRow next) (preparedExecGhostPub row next fields)
  have oldAdvance : preparedAdvanceExpr.evalWith (preparedRowEnv (preparedExecGhostRow row)
      (preparedExecGhostNext row next fields) (preparedExecGhostPub row next fields) 0 0)=0 := by
    rw [←prepared_exec_lower_eval,prepared_exec_advance_lower]
    exact adv
  have oldQuiet : ∀ i,i<3 → preparedSuccessExpr.evalWith (preparedRowEnv (preparedExecGhostRow row)
      (preparedExecGhostNext row next fields) (preparedExecGhostPub row next fields) 0 0)*
      (preparedFetchPython i).evalWith (preparedRowEnv (preparedExecGhostRow row)
      (preparedExecGhostNext row next fields) (preparedExecGhostPub row next fields) 0 0)=0 := by
    intro i hi
    rw [←prepared_exec_lower_eval (preparedFetchPython i),prepared_exec_fetch_lower i (by omega)]
    simp only [show i<4 by omega,ite_true,preparedExecSimplify,Expr.evalWith,preparedRowEnv]
    exact quiet i hi
  rw [ghost] at projection oldAdvance oldQuiet
  have q:=prepared_quiet_projection _ _ _ projection.1 nextChoices projection.2 oldAdvance oldQuiet
  refine ⟨?_,?_,q.2.2⟩
  · have pc:=prepared_exec_pc_transition table tr t pub pcSource localH r nonlast 0 (by decide) advance
    simpa using pc
  · intro i hi
    have h:=q.2.1 i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem prepared_literal_padding_step (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (r : Nat) (nonlast : r+1<tr.height 0)
    (done : tr.cell 0 r 41=1) : PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+1)) := by
  have localH:=prepared_exec_table_local _ _ _ count tr pub holds
  have success : preparedExecGasSuccess.eval tr 0 r pub=0 := by
    change ((1:Fp)+ -tr.cell 0 r 41)*_=0
    rw [done];grind
  have advance : preparedExecPCAdvance.eval tr 0 r pub=0 := by
    change preparedExecGasSuccess.eval tr 0 r pub*_=0
    rw [success];grind
  have q:=prepared_exec_quiet _ tr 0 r pub localH nonlast prepared_literal_exec_closure prepared_literal_exec_pc
    advance (by intro i hi;rw [success];grind)
  have nextDone:=prepared_exec_source_eval _ tr 0 r pub localH nonlast _ prepared_literal_exec_closure.done
  have nextFail:=prepared_exec_source_eval _ tr 0 r pub localH nonlast _ prepared_literal_exec_closure.failed
  change (1:Fp)*(tr.cell 0 (r+1) 41+ -(tr.cell 0 r 41+(((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430+
    (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*tr.cell 0 r 469)))=0 at nextDone
  change (1:Fp)*(tr.cell 0 (r+1) 42+ -(tr.cell 0 r 42+((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430))=0 at nextFail
  rw [done] at nextDone nextFail
  refine ⟨by rw [done];grind,by grind,?_,q⟩
  exact prepared_exec_gas_update_word _ tr 0 r pub prepared_literal_exec_gas localH nonlast false success

theorem prepared_exec_snapshot_trans (a b c : Nat → Fp)
    (ab : PreparedExecSnapshotEq a b) (bc : PreparedExecSnapshotEq b c) : PreparedExecSnapshotEq a c := by
  exact ⟨bc.1.trans ab.1,bc.2.1.trans ab.2.1,bc.2.2.1.trans ab.2.2.1,
    bc.2.2.2.1.trans ab.2.2.2.1,fun i hi=>(bc.2.2.2.2.1 i hi).trans (ab.2.2.2.2.1 i hi),
    fun i hi=>(bc.2.2.2.2.2 i hi).trans (ab.2.2.2.2.2 i hi)⟩

theorem prepared_literal_padding_suffix (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (r : Nat) (done : tr.cell 0 r 41=1)
    (distance : Nat) (bound : r+distance<tr.height 0) :
    PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+distance)) := by
  induction distance with
  | zero => exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ distance ih =>
    have previous:=ih (by omega)
    have step:=prepared_literal_padding_step count tr pub holds (r+distance) (by omega) (previous.1.trans done)
    exact prepared_exec_snapshot_trans _ _ _ previous step

end NearCompression
