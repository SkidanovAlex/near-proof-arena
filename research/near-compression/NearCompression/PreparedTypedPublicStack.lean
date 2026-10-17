import NearCompression.PreparedTypedPaddedExit
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedPublicStackWord (pub : List Fp) (slot : Nat) : Nat :=
  instructionAdd64Word (fun i=>pub.getD (75+5*slot+i) 0) 0
def preparedTypedPublicStackValue (pub : List Fp) (slot : Nat) : Val :=
  if pub.getD (74+5*slot) 0=0 then .i32 (UInt32.ofNat (preparedTypedPublicStackWord pub slot))
  else .i64 (UInt64.ofNat (preparedTypedPublicStackWord pub slot))
def preparedTypedPublicStack (pub : List Fp) : Array Val :=
  ((List.range (pub.getD 67 0).toNat).map (preparedTypedPublicStackValue pub)).toArray

/-- The complete natural boundary message binds each actual tag and all four
limbs, not a packed field element or an assumed public stack equality. -/
theorem prepared_typed_boundary_stack_value (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0)
    (slot : Nat) (hs : slot<8) :
    preparedTypedStackValue (tr.cell 0 r) slot=preparedTypedPublicStackValue pub slot := by
  have balanced:=holds
  rw [prepared_typed_bus_literal_air] at balanced
  have message:=prepared_typed_boundary_bound _ _ _ codeCount tr pub balanced counts true r hr endpoint
  have tag : tr.cell 0 r (1074+slot)=pub.getD (74+5*slot) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (11+5*slot) 0) message
    have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7:=by omega
    rcases cases with z|z|z|z|z|z|z|z <;> subst slot <;> exact h
  have limb (i : Nat) (hi : i<4) :
      preparedTypedStackLimb (tr.cell 0 r) slot i=pub.getD (75+5*slot+i) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (12+5*slot+i) 0) message
    have slots : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7:=by omega
    have limbs : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases slots with z|z|z|z|z|z|z|z <;> subst slot <;> rcases limbs with z|z|z|z <;> subst i
    all_goals change (preparedCodeBits _).eval tr 0 r pub=_ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals exact h
  have word : preparedTypedStackWord (tr.cell 0 r) slot=preparedTypedPublicStackWord pub slot := by
    unfold preparedTypedStackWord preparedTypedPublicStackWord instructionAdd64Word
    rw [limb 0 (by decide),limb 1 (by decide),limb 2 (by decide),limb 3 (by decide)]
  simp only [preparedTypedStackValue,preparedTypedPublicStackValue,tag,word]

theorem prepared_typed_boundary_stack (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0)
    (sp : Nat) (bound : sp<9) (selected : ∀i,i<9 → tr.cell 0 r (32+i)=if i=sp then 1 else 0) :
    (pub.getD 67 0).toNat=sp ∧ preparedTypedPublicStack pub=preparedTypedStack (tr.cell 0 r) sp := by
  have balanced:=holds
  rw [prepared_typed_bus_literal_air] at balanced
  have message:=prepared_typed_boundary_bound _ _ _ codeCount tr pub balanced counts true r hr endpoint
  have field:=congrArg (fun msg:List Fp=>msg.getD 4 0) message
  change (preparedControlIndex 32).eval tr 0 r pub=pub.getD 67 0 at field
  have index : (preparedControlIndex 32).eval tr 0 r pub=Fp.ofNat sp :=
    prepared_control_index_selected (tr.cell 0 r) 32 sp bound selected
  have natEq : (pub.getD 67 0).toNat=sp := by
    rw [←field,index,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show sp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)]
  refine ⟨natEq,?_⟩
  simp only [preparedTypedPublicStack,preparedTypedStack,natEq]
  congr 1
  apply List.map_congr_left
  intro slot hs
  exact (prepared_typed_boundary_stack_value codeCount count tr pub holds counts r hr endpoint slot
    (by have h:=List.mem_range.mp hs;omega)).symm

/-- Every DONE row's mixed stack survives the padding suffix and is exactly
what the public exit record decodes. Interpreter terminal linkage is separate. -/
theorem prepared_typed_done_public_stack (codeCount count : Nat) (hc : count≤4)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (done : tr.cell 0 r 41=1)
    (sp : Nat) (bound : sp<9) (selected : ∀i,i<9 → tr.cell 0 r (32+i)=if i=sp then 1 else 0) :
    (pub.getD 67 0).toNat=sp ∧ preparedTypedPublicStack pub=preparedTypedStack (tr.cell 0 r) sp := by
  have suffix:=prepared_typed_padding_suffix count hc tr 0 pub (prepared_typed_exec_local codeCount count tr pub holds)
    r (tr.height 0-1-r) (by omega) done
  have index : r+(tr.height 0-1-r)=tr.height 0-1:=by omega
  rw [index] at suffix
  have lastSelected : ∀i,i<9 → tr.cell 0 (tr.height 0-1) (32+i)=if i=sp then 1 else 0 := by
    intro i hi;rw [suffix.sp i hi,selected i hi]
  have lastBinding:=prepared_typed_boundary_stack codeCount count tr pub holds counts (tr.height 0-1) (by omega) (by omega) sp bound lastSelected
  refine ⟨lastBinding.1,lastBinding.2.trans ?_⟩
  apply prepared_typed_stack_congr
  intro i hi
  exact prepared_typed_snapshot_value _ _ count suffix i (by omega)
end NearCompression
