import NearCompression.PreparedControlPadding
import NearCompression.PreparedControlBoundary

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near NearSpecV3.Wasm

theorem prepared_control_boundary_stack_word (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0) (slot : Nat) (hs : slot<8) :
    preparedExecStackWord (tr.cell 0 r) slot=preparedExecPublicStackWord pub slot := by
  have balanced:=holds
  rw [prepared_control_bus_literal_air] at balanced
  have message:=prepared_control_boundary_bound _ _ _ count tr pub balanced counts true r hr endpoint
  have limb (i : Nat) (hi : i<2) :
      preparedCodeLimb (tr.cell 0 r) (43+32*slot+16*i)=pub.getD (50+2*slot+i) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (11+2*slot+i) 0) message
    have slots : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7 := by omega
    have limbs : i=0 ∨ i=1 := by omega
    rcases slots with z|z|z|z|z|z|z|z <;> subst slot <;> rcases limbs with z|z <;> subst i
    all_goals change (preparedCodeBits _).eval tr 0 r pub=_ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals exact h
  have lo:=limb 0 (by decide)
  have hi:=limb 1 (by decide)
  have words : preparedExecStackWord (tr.cell 0 r) slot=
      (preparedCodeLimb (tr.cell 0 r) (43+32*slot)).toNat+
      65536*(preparedCodeLimb (tr.cell 0 r) (43+32*slot+16)).toNat := by
    simp only [preparedExecStackWord,preparedStackWord,preparedCodeLimb]
    rw [prepared_exec_ghost_bits _ 16 _ (by omega),prepared_exec_ghost_bits _ 16 _ (by omega)]
    rw [show 27+32*slot+16=43+32*slot by omega]
  rw [words]
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at lo hi
  rw [lo,hi]
  simp only [preparedExecPublicStackWord,Nat.add_right_comm 50 _ 1]

theorem prepared_control_final_row_published (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0)
    (final : St) (error : Option String) (binding : PreparedExecFinalRow (tr.cell 0 r) final error) :
    PreparedExecPublishedOutput pub final error := by
  rcases binding with ⟨done,failed,gas,sp,bound,selected,stack⟩
  have balanced:=holds
  rw [prepared_control_bus_literal_air] at balanced
  have message:=prepared_control_boundary_bound _ _ _ count tr pub balanced counts true r hr endpoint
  have d:=congrArg (fun msg:List Fp=>msg.getD 5 0) message
  have f:=congrArg (fun msg:List Fp=>msg.getD 6 0) message
  change tr.cell 0 r 41=pub.getD 44 0 at d
  change tr.cell 0 r 42=pub.getD 45 0 at f
  have spField:=congrArg (fun msg:List Fp=>msg.getD 4 0) message
  change (preparedSPIndexPython false).evalWith
    (preparedRowEnv (preparedExecGhostRow (tr.cell 0 r)) (preparedExecGhostRow (tr.cell 0 r))
      (fun i=>pub.getD i 0) 0 0)=pub.getD 43 0 at spField
  have hot : ∀ i,i<9 → preparedExecGhostRow (tr.cell 0 r) (16+i)=if i=sp then 1 else 0 := by
    intro i hi
    simpa only [preparedExecGhostRow,show ¬16+i<16 by omega,ite_false,
      show 16+i+16=32+i by omega] using selected i hi
  rw [prepared_sp_index_selected (preparedExecGhostRow (tr.cell 0 r)) (preparedExecGhostRow (tr.cell 0 r)) (fun i=>pub.getD i 0) false sp bound hot] at spField
  have spNat : (pub.getD 43 0).toNat=sp := by
    rw [←spField,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show sp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)]
  refine ⟨d.symm.trans done,f.symm.trans failed,gas.trans
    (prepared_control_boundary_gas count tr pub holds counts true r hr endpoint),?_,?_⟩
  · rw [spNat];exact bound
  · rw [spNat,stack]
    exact prepared_exec_public_stack_decode _ pub sp bound
      (fun slot hs=>prepared_control_boundary_stack_word count tr pub holds counts r hr endpoint slot hs)

/-- Once the actual terminal result is bound to its first DONE row, every
remaining row is derived from literal AIR and the final public receive bus. -/
theorem prepared_control_terminal_published (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (final : St) (error : Option String)
    (binding : PreparedExecFinalRow (tr.cell 0 r) final error) :
    PreparedExecPublishedOutput pub final error := by
  have same:=prepared_control_padding_suffix count tr pub holds r binding.1 (tr.height 0-1-r) (by omega)
  have transported:=prepared_exec_final_row_transport _ _ final error binding same
  have endpoint : r+(tr.height 0-1-r)+1=tr.height 0 := by omega
  exact prepared_control_final_row_published count tr pub holds counts _ (by omega) endpoint final error transported

end NearCompression
