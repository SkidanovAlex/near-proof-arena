import NearCompression.PreparedTypedTerminal
import NearCompression.PreparedTypedQuietStack
import NearCompression.PreparedTypedQuietControl
import NearCompression.PreparedTypedQuietLocals
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
structure PreparedTypedSnapshotEq (row next : Nat→Fp) (count : Nat) : Prop where
  done : next 41=row 41
  failed : next 42=row 42
  gas : preparedExecWord64 next 299=preparedExecWord64 row 299
  pc : preparedCodeExecPC next=preparedCodeExecPC row
  sp : ∀i,i<9 → next (32+i)=row (32+i)
  limbs : ∀slot,slot<8 → ∀limb,limb<4 → preparedTypedStackLimb next slot limb=preparedTypedStackLimb row slot limb
  tags : ∀slot,slot<8 → next (1074+slot)=row (1074+slot)
  locals : preparedTypedLocalArray next count=preparedTypedLocalArray row count
  label : next 639=row 639
  height : ∀i,i<9 → next (640+i)=row (640+i)
  target : preparedControlSavedTarget next=preparedControlSavedTarget row
private theorem done_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1623+66*(4-count.val)]?=some preparedLocalsLiteralExec1002 := by decide
private theorem fail_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1624+66*(4-count.val)]?=some preparedLocalsLiteralExec1003 := by decide

theorem prepared_typed_padding_step (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (done : tr.cell t r 41=1) : PreparedTypedSnapshotEq (tr.cell t r) (tr.cell t (r+1)) count := by
  have quiet : preparedExecGasSuccess.eval tr t r pub=0 := by
    change ((1:Fp)+ -tr.cell t r 41)*_=0;rw [done];grind
  have control:=prepared_typed_quiet_pc_labels count hc tr t r pub localH nonlast quiet
  obtain ⟨sp,hs,hot⟩:=prepared_typed_source_sp count hc tr t r pub localH (by omega)
  have nextHot:=prepared_typed_quiet_depth count hc tr t r pub localH nonlast quiet sp hs hot
  have nd:=localH.constr r (by omega) _ (List.mem_of_getElem? (done_at ⟨count,by omega⟩))
  have nf:=localH.constr r (by omega) _ (List.mem_of_getElem? (fail_at ⟨count,by omega⟩))
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 41+
    -(tr.cell t r 41+(((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430+
      (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)))))=0 at nd
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 42+
    -(tr.cell t r 42+((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430))=0 at nf
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,done] at nd nf
  refine ⟨by rw [done];grind,by grind,
    prepared_control_gas_update_word _ tr t r pub (prepared_typed_gas_source count hc) localH nonlast false quiet,
    control.1,?_,?_,?_,prepared_typed_quiet_local_array count hc tr t r pub localH nonlast quiet,
    control.2.1,control.2.2.1,control.2.2.2⟩
  · intro i hi;rw [nextHot i hi,hot i hi]
  · intro slot hs limb hl;exact prepared_typed_quiet_stack_limb count hc tr t r pub localH nonlast quiet slot limb hs hl
  · intro slot hs;exact prepared_typed_quiet_stack_tag count hc tr t r pub localH nonlast quiet slot hs

theorem prepared_typed_snapshot_refl (row : Nat→Fp) (count : Nat) : PreparedTypedSnapshotEq row row count :=
  ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _=>rfl,fun _ _=>rfl,rfl,rfl,fun _ _=>rfl,rfl⟩
theorem prepared_typed_snapshot_trans (a b c : Nat→Fp) (count : Nat)
    (ab : PreparedTypedSnapshotEq a b count) (bc : PreparedTypedSnapshotEq b c count) : PreparedTypedSnapshotEq a c count :=
  ⟨bc.done.trans ab.done,bc.failed.trans ab.failed,bc.gas.trans ab.gas,bc.pc.trans ab.pc,
    fun i hi=>(bc.sp i hi).trans (ab.sp i hi),fun s hs i hi=>(bc.limbs s hs i hi).trans (ab.limbs s hs i hi),
    fun s hs=>(bc.tags s hs).trans (ab.tags s hs),bc.locals.trans ab.locals,bc.label.trans ab.label,
    fun i hi=>(bc.height i hi).trans (ab.height i hi),bc.target.trans ab.target⟩

theorem prepared_typed_padding_suffix (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (r n : Nat) (live : r+n<tr.height t) (done : tr.cell t r 41=1) :
    PreparedTypedSnapshotEq (tr.cell t r) (tr.cell t (r+n)) count := by
  induction n with
  | zero=>simpa using prepared_typed_snapshot_refl (tr.cell t r) count
  | succ n ih=>
    have previous:=ih (by omega)
    have next:=prepared_typed_padding_step count hc tr t (r+n) pub localH (by omega) (previous.done.trans done)
    simpa only [Nat.add_assoc] using prepared_typed_snapshot_trans _ _ _ count previous next

theorem prepared_typed_snapshot_value (row next : Nat→Fp) (count : Nat)
    (eq : PreparedTypedSnapshotEq row next count) (slot : Nat) (hs : slot<8) :
    preparedTypedStackValue next slot=preparedTypedStackValue row slot := by
  have word : preparedTypedStackWord next slot=preparedTypedStackWord row slot := by
    unfold preparedTypedStackWord instructionAdd64Word
    rw [eq.limbs slot hs 0 (by decide),eq.limbs slot hs 1 (by decide),eq.limbs slot hs 2 (by decide),eq.limbs slot hs 3 (by decide)]
  simp only [preparedTypedStackValue,eq.tags slot hs,word]

/-- Padding rows represent the same typed snapshot; no additional Wasm step
is executed after terminal status. -/
theorem prepared_typed_snapshot_state (row next : Nat→Fp) (count : Nat)
    (eq : PreparedTypedSnapshotEq row next count)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState row s f fs sp count root) : PreparedTypedState next s f fs sp count root := by
  refine ⟨state.depth,?_,state.frames,state.pc.trans eq.pc.symm,?_,state.gas.trans eq.gas.symm,
    state.countBound,state.locals.trans eq.locals.symm,?_⟩
  · intro i hi;rw [eq.sp i hi];exact state.selected i hi
  · rw [state.stack]
    symm
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_snapshot_value row next count eq i (by have h:=state.depth;omega)
  · exact prepared_control_labels_transport row next f f root state.labels rfl eq.label eq.height eq.target
end NearCompression
