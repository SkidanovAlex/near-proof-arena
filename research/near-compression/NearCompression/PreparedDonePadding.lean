import NearCompression.PreparedWasmConstruct

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Semantic snapshot equality; arithmetic words are reconstructed from
separately constrained limbs, not a single field-valued packing. -/
def PreparedSnapshotEq (row next : Nat → Fp) (pub : List Fp) : Prop :=
  next 25=row 25 ∧ next 26=row 26 ∧ preparedGasValue next pub=preparedGasValue row pub ∧
  (∀ i,i<16 → next i=row i) ∧ (∀ i,i<9 → next (16+i)=row (16+i)) ∧
  (∀ slot,slot<8 → preparedStackWord next slot=preparedStackWord row slot)

theorem prepared_done_padding_step (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (nonlast : r+1<tr.height t) (done : tr.cell t r 25=1) :
    PreparedSnapshotEq (tr.cell t r) (tr.cell t (r+1)) pub := by
  let row:=tr.cell t r
  let next:=tr.cell t (r+1)
  let pp:=fun i=>pub.getD i 0
  have success : preparedSuccessExpr.evalWith (preparedRowEnv row next pp 0 0)=0 := by
    change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)=0
    change row 25=1 at done
    rw [done];grind
  have advance : preparedAdvanceExpr.evalWith (preparedRowEnv row next pp 0 0)=0 := by
    change preparedSuccessExpr.evalWith (preparedRowEnv row next pp 0 0)*_=0
    rw [success];grind
  have nextDone := prepared_table_nonlast_eval table tr t r pub air.localH nonlast preparedDoneStepPython
    (air.source.terminal.flagMembers _ (by simp)) (by
      simp [preparedDoneStepPython,preparedTransitionEq,preparedActiveExpr,preparedSuccessExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst])
  have nextFail := prepared_table_nonlast_eval table tr t r pub air.localH nonlast preparedFailureStepPython
    (air.source.terminal.flagMembers _ (by simp)) (by
      simp [preparedFailureStepPython,preparedTransitionEq,preparedActiveExpr,preparedNoFirst])
  change (1:Fp)*(next 25+ -(row 25+(((1:Fp)+ -row 25)*row 414+
    preparedSuccessExpr.evalWith (preparedRowEnv row next pp 0 0)*(preparedFetchPython 3).evalWith
      (preparedRowEnv row next pp 0 0))))=0 at nextDone
  change (1:Fp)*(next 26+ -(row 26+((1:Fp)+ -row 25)*row 414))=0 at nextFail
  change row 25=1 at done
  rw [done,success] at nextDone
  rw [done] at nextFail
  have flags : next 25=row 25 ∧ next 26=row 26 := by rw [done];constructor <;> grind
  have choices:=prepared_table_row_choices table air.source.terminal.gasMiddle air.source.terminal.gasTail
    air.source.terminal.gasSource tr t r pub air.localH (by omega) next
  have nextChoices:=prepared_table_row_choices table air.source.terminal.gasMiddle air.source.terminal.gasTail
    air.source.terminal.gasSource tr t (r+1) pub air.localH nonlast next
  have transitions:=prepared_table_add_transitions table air.source.prefixPart air.source.middle air.source.dead
    air.source.transition tr t r pub air.localH nonlast
  have quiet:=prepared_quiet_projection row next pp choices nextChoices transitions advance (by
    intro i hi;rw [success];grind)
  exact ⟨flags.1,flags.2,prepared_gas_failure_freeze row next pub success
    (prepared_gas_updates_table table air.source.terminal tr t r pub air.localH nonlast),quiet⟩

theorem prepared_snapshot_eq_trans (a b c : Nat → Fp) (pub : List Fp)
    (ab : PreparedSnapshotEq a b pub) (bc : PreparedSnapshotEq b c pub) : PreparedSnapshotEq a c pub := by
  exact ⟨bc.1.trans ab.1,bc.2.1.trans ab.2.1,bc.2.2.1.trans ab.2.2.1,
    fun i hi=>(bc.2.2.2.1 i hi).trans (ab.2.2.2.1 i hi),
    fun i hi=>(bc.2.2.2.2.1 i hi).trans (ab.2.2.2.2.1 i hi),
    fun i hi=>(bc.2.2.2.2.2 i hi).trans (ab.2.2.2.2.2 i hi)⟩

/-- All rows after a terminal snapshot preserve its published semantics. -/
theorem prepared_done_padding_suffix (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (done : tr.cell t r 25=1)
    (distance : Nat) (bound : r+distance<tr.height t) :
    PreparedSnapshotEq (tr.cell t r) (tr.cell t (r+distance)) pub := by
  induction distance with
  | zero => exact ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ distance ih =>
    have previous:=ih (by omega)
    have nextDone : tr.cell t (r+distance) 25=1:=previous.1.trans done
    have step:=prepared_done_padding_step table tr t (r+distance) pub air (by omega) nextDone
    exact prepared_snapshot_eq_trans _ _ _ pub previous step

end NearCompression
