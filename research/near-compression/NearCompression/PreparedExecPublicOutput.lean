import NearCompression.PreparedExecPadding

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near NearSpecV3.Wasm

/-- A terminal interpreter result represented by an EXEC snapshot. -/
def PreparedExecFinalRow (row : Nat → Fp) (final : St) (error : Option String) : Prop :=
  row 41=1 ∧ row 42=(if error.isSome then 1 else 0) ∧
  final.gas.g=preparedExecWord64 row 299 ∧
  ∃ sp,sp<9 ∧ (∀ i,i<9 → row (32+i)=if i=sp then 1 else 0) ∧
    final.stack=preparedWasmStack (preparedExecGhostRow row) sp

def preparedExecPublicStackWord (pub : List Fp) (slot : Nat) : Nat :=
  (pub.getD (50+2*slot) 0).toNat+65536*(pub.getD (51+2*slot) 0).toNat

def preparedExecPublicStack (pub : List Fp) : Nat → Array Val
  | 0 => #[]
  | n+1 => (preparedExecPublicStack pub n).push (.i32 (UInt32.ofNat (preparedExecPublicStackWord pub n)))

/-- Public exit status, fast gas and live i32 stack; exit PC remains metadata. -/
def PreparedExecPublishedOutput (pub : List Fp) (final : St) (error : Option String) : Prop :=
  pub.getD 44 0=1 ∧ pub.getD 45 0=(if error.isSome then 1 else 0) ∧
  final.gas.g=preparedExecPublicGas pub true ∧ (pub.getD 43 0).toNat<9 ∧
  final.stack=preparedExecPublicStack pub (pub.getD 43 0).toNat

theorem prepared_exec_final_row_transport (row next : Nat → Fp) (final : St) (error : Option String)
    (binding : PreparedExecFinalRow row final error) (same : PreparedExecSnapshotEq row next) :
    PreparedExecFinalRow next final error := by
  rcases binding with ⟨done,failed,gas,sp,hs,selected,stack⟩
  refine ⟨same.1.trans done,same.2.1.trans failed,gas.trans same.2.2.1.symm,
    sp,hs,fun i hi=>(same.2.2.2.2.1 i hi).trans (selected i hi),?_⟩
  rw [stack]
  apply prepared_wasm_stack_congr
  intro slot hslot
  exact (same.2.2.2.2.2 slot (by omega)).symm

theorem prepared_exec_ghost_bits (row : Nat → Fp) (n base : Nat) (hb : 16≤base) :
    (instructionBitExpr base n).evalWith (instructionAddEnv (preparedExecGhostRow row))=
    (instructionBitExpr (base+16) n).evalWith (instructionAddEnv row) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    change preparedExecGhostRow row base+Fp.ofNat 2*(instructionBitExpr (base+1) n).evalWith
      (instructionAddEnv (preparedExecGhostRow row))=
      row (base+16)+Fp.ofNat 2*(instructionBitExpr (base+16+1) n).evalWith (instructionAddEnv row)
    rw [ih (base+1) (by omega)]
    simp only [preparedExecGhostRow,show ¬base<16 by omega,ite_false,
      show base+1+16=base+16+1 by omega]

theorem prepared_literal_boundary_stack_word (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0) (slot : Nat) (hs : slot<8) :
    preparedExecStackWord (tr.cell 0 r) slot=preparedExecPublicStackWord pub slot := by
  have message:=prepared_exec_boundary_bound _ _ _ count tr pub holds counts true r hr endpoint
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

theorem prepared_exec_public_stack_decode (row : Nat → Fp) (pub : List Fp) (sp : Nat) (bound : sp<9)
    (words : ∀ slot,slot<8 → preparedExecStackWord row slot=preparedExecPublicStackWord pub slot) :
    preparedWasmStack (preparedExecGhostRow row) sp=preparedExecPublicStack pub sp := by
  induction sp with
  | zero => rfl
  | succ sp ih =>
    simp only [preparedWasmStack,preparedExecPublicStack,ih (by omega)]
    rw [show preparedStackWord (preparedExecGhostRow row) sp=preparedExecPublicStackWord pub sp from words sp (by omega)]

theorem prepared_literal_final_row_published (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0)
    (final : St) (error : Option String) (binding : PreparedExecFinalRow (tr.cell 0 r) final error) :
    PreparedExecPublishedOutput pub final error := by
  rcases binding with ⟨done,failed,gas,sp,bound,selected,stack⟩
  have message:=prepared_exec_boundary_bound _ _ _ count tr pub holds counts true r hr endpoint
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
    (prepared_literal_boundary_gas count tr pub holds counts true r hr endpoint),?_,?_⟩
  · rw [spNat];exact bound
  · rw [spNat,stack]
    exact prepared_exec_public_stack_decode _ pub sp bound
      (fun slot hs=>prepared_literal_boundary_stack_word count tr pub holds counts r hr endpoint slot hs)

/-- Once the actual terminal result is bound to its first DONE row, every
remaining row is derived from literal AIR and the final public receive bus. -/
theorem prepared_literal_terminal_published (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (final : St) (error : Option String)
    (binding : PreparedExecFinalRow (tr.cell 0 r) final error) :
    PreparedExecPublishedOutput pub final error := by
  have same:=prepared_literal_padding_suffix count tr pub holds r binding.1 (tr.height 0-1-r) (by omega)
  have transported:=prepared_exec_final_row_transport _ _ final error binding same
  have endpoint : r+(tr.height 0-1-r)+1=tr.height 0 := by omega
  exact prepared_literal_final_row_published count tr pub holds counts _ (by omega) endpoint final error transported

end NearCompression
