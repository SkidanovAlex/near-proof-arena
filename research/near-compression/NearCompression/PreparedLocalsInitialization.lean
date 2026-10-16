import NearCompression.PreparedLocalsIndex
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

private theorem locals_initial_slice :
    (preparedLocalsLiteralExecBase.drop 824).take 128=
      (List.range 128).map (fun i=>Expr.mul .isFirst (.add (.col (686+i) false) (.neg (.const 0)))) := by rfl

theorem prepared_locals_initial_bit (count : Nat) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (positive : 0<tr.height t) (i : Nat) (hi : i<128) : tr.cell t 0 (686+i)=0 := by
  have source : Expr.mul .isFirst (.add (.col (686+i) false) (.neg (.const 0)))∈preparedLocalsLiteralExecBase := by
    apply List.mem_of_mem_drop
    apply List.mem_of_mem_take
    rw [locals_initial_slice]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have h:=localH.constr 0 positive _ (prepared_locals_base_member count _ source)
  change (1:Fp)*(tr.cell t 0 (686+i)+ -(0:Fp))=0 at h
  grind

private theorem zero_bits (row : Nat→Fp) (base n : Nat)
    (zero : ∀i,i<n → row (base+i)=0) :
    (instructionBitExpr base n).evalWith (instructionAddEnv row)=0 := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    have head : row base=0 := by simpa using zero 0 (by omega)
    have tail := ih (base+1) (by intro i hi; have h:=zero (i+1) (by omega); simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
    change row base+Fp.ofNat 2*(instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)=0
    rw [head,tail]
    grind

theorem prepared_locals_initial_limb (count : Nat) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (positive : 0<tr.height t) (slot limb : Nat) (hs : slot<4) (hl : limb<2) :
    preparedCodeLimb (tr.cell t 0) (686+32*slot+16*limb)=0 := by
  apply zero_bits
  intro i hi
  have h:=prepared_locals_initial_bit count tr t pub localH positive (32*slot+16*limb+i) (by omega)
  simpa [Nat.add_assoc] using h

theorem prepared_locals_initial_word (count : Nat) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (positive : 0<tr.height t) (slot : Nat) (hs : slot<4) :
    preparedLocalsWord (tr.cell t 0) slot=0 := by
  have low:=prepared_locals_initial_limb count tr t pub localH positive slot 0 hs (by decide)
  have high:=prepared_locals_initial_limb count tr t pub localH positive slot 1 hs (by decide)
  have index : 686+32*slot+16=702+32*slot := by omega
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,index] at low high
  unfold preparedLocalsWord
  rw [low,high]
  rfl

theorem prepared_locals_initial_array (count : Nat) (bound : count≤4)
    (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (positive : 0<tr.height t) :
    preparedLocalsArray (tr.cell t 0) count=(List.replicate count (Val.i32 0)).toArray := by
  unfold preparedLocalsArray
  apply congrArg List.toArray
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_replicate]
    rw [prepared_locals_initial_word count tr t pub localH positive i (by simpa using Nat.lt_of_lt_of_le (show i<count by simpa using hi) bound)]
    rfl
end NearCompression
