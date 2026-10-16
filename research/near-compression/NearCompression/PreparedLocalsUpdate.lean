import NearCompression.PreparedLocalsIndex
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem locals_boolean_prefix :
    preparedLocalsLiteralExecBase.take 817=(List.range 817).map
      (fun i=>preparedGasBoolean (if i<682 then i else i+1)) := by rfl

theorem prepared_locals_bits_boolean (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (c : Nat) (hc : c<818) (notInverse : c≠682) : (tr.cell t r c).toNat≤1 := by
  let i:=if c<682 then c else c-1
  have hi : i<817 := by dsimp [i];split <;> omega
  have eq : (if i<682 then i else i+1)=c := by dsimp [i];split <;> (try split) <;> omega
  have source : preparedGasBoolean c∈preparedLocalsLiteralExecBase := by
    apply List.mem_of_mem_take
    rw [locals_boolean_prefix]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,congrArg preparedGasBoolean eq⟩
  have h:=localH.constr r hr _ (prepared_locals_base_member count _ source)
  change tr.cell t r c*(tr.cell t r c+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

def preparedLocalsSuccess : Expr :=
  .mul (.add (.const 1) (.neg (.col 41 false))) (.add (.const 1) (.neg (.col 430 false)))
def preparedLocalsWrite (slot : Nat) : Expr :=
  .mul preparedLocalsSuccess (.mul (.add (.col 684 false) (.col 685 false)) (.col (814+slot) false))
def preparedLocalsTop (limb : Nat) : Expr :=
  preparedBalancedSum (fun i=>.mul (.col (32+(i+1)) false) (preparedCodeBits (43+32*i+16*limb))) 3 0

def preparedLocalsUpdate (slot limb : Nat) : Expr :=
  .mul .isTransition (.add (preparedCodeBits (686+32*slot+16*limb) true)
    (.neg (.add
      (.mul (.add (.const 1) (.neg (preparedLocalsWrite slot))) (preparedCodeBits (686+32*slot+16*limb)))
      (.mul (preparedLocalsWrite slot) (preparedLocalsTop limb)))))

private theorem locals_update_slice :
    (preparedLocalsLiteralExecBase.drop 952).take 8=
      (List.range 4).flatMap (fun slot=>(List.range 2).map (preparedLocalsUpdate slot)) := by rfl

theorem prepared_locals_update_source (count slot limb : Nat) (hs : slot<4) (hl : limb<2) :
    preparedLocalsUpdate slot limb∈(preparedLocalsLiteralExecTable count).constraints := by
  apply prepared_locals_base_member
  apply List.mem_of_mem_drop
  apply List.mem_of_mem_take
  rw [locals_update_slice]
  exact List.mem_flatMap.mpr ⟨slot,List.mem_range.mpr hs,
    List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩

/-- The exact source equation at a nonfinal row, with real selector and
column evaluation. Bounds and selected-operand decoding are separate lemmas. -/
theorem prepared_locals_limb_step (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (slot limb : Nat) (hs : slot<4) (hl : limb<2) :
    preparedCodeLimb (tr.cell t (r+1)) (686+32*slot+16*limb)=
      (1-(preparedLocalsWrite slot).eval tr t r pub)*preparedCodeLimb (tr.cell t r) (686+32*slot+16*limb)+
      (preparedLocalsWrite slot).eval tr t r pub*(preparedLocalsTop limb).eval tr t r pub := by
  have h:=localH.constr r (by omega) _ (prepared_locals_update_source count slot limb hs hl)
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits (686+32*slot+16*limb) true).eval tr t r pub+
      -(((1:Fp)+ -(preparedLocalsWrite slot).eval tr t r pub)*
        (preparedCodeBits (686+32*slot+16*limb)).eval tr t r pub+
        (preparedLocalsWrite slot).eval tr t r pub*(preparedLocalsTop limb).eval tr t r pub))=0 at h
  rw [if_neg (by omega : r+1≠tr.height t),prepared_code_bits_eval,prepared_code_bits_eval] at h
  simp only [ite_true,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
  grind

/-- Boolean decomposition prevents limb-to-field reduction aliases for all
local and operand-stack limbs in this profile. -/
theorem prepared_locals_limb_bound (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (base : Nat) (bounds : base+16≤682 ∨ 683≤base ∧ base+16≤818) :
    (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  exact instruction_bit_expr_bound _ 16 base (by decide) (fun i hi=>
    prepared_locals_bits_boolean count tr t r pub localH hr (base+i) (by omega) (by omega))
end NearCompression
