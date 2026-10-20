import NearCompression.InstructionAddRange

/-! Four-limb gas subtraction for the prepared-function diagnostic. The
integer chain is connected below to GAS283, DIFF347 and BORROW411 source
expressions; this module does not claim the full prepared-function step. -/
set_option autoImplicit false
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def preparedGasWord (limbs : Nat → Nat) : Nat :=
  limbs 0+65536*limbs 1+4294967296*limbs 2+281474976710656*limbs 3

theorem prepared_gas_word_bound (limbs : Nat → Nat) (bounds : ∀ i,i<4 → limbs i<65536) :
    preparedGasWord limbs<18446744073709551616 := by
  have h0:=bounds 0 (by decide);have h1:=bounds 1 (by decide)
  have h2:=bounds 2 (by decide);have h3:=bounds 3 (by decide)
  unfold preparedGasWord; omega

/-- Telescoping exact natural equations; no field-valued aggregate. -/
theorem prepared_gas_nat_total (gas fee diff borrow : Nat → Nat)
    (equations : ∀ i,i<4 → diff i+fee i+(if i=0 then 0 else borrow (i-1)) = gas i+65536*borrow i) :
    preparedGasWord diff+preparedGasWord fee =
      preparedGasWord gas+18446744073709551616*borrow 3 := by
  have e0:=equations 0 (by decide);have e1:=equations 1 (by decide)
  have e2:=equations 2 (by decide);have e3:=equations 3 (by decide)
  simp only [Nat.reduceEqDiff,ite_true,ite_false,Nat.reduceSub] at e0 e1 e2 e3
  unfold preparedGasWord; omega

theorem prepared_gas_nat_borrow (gas fee diff borrow : Nat → Nat)
    (gasBounds : ∀ i,i<4 → gas i<65536) (feeBounds : ∀ i,i<4 → fee i<65536)
    (diffBounds : ∀ i,i<4 → diff i<65536) (borrowBit : borrow 3≤1)
    (equations : ∀ i,i<4 → diff i+fee i+(if i=0 then 0 else borrow (i-1)) = gas i+65536*borrow i) :
    (borrow 3=1 ↔ preparedGasWord gas<preparedGasWord fee) ∧
    (borrow 3=0 ↔ preparedGasWord fee≤preparedGasWord gas) ∧
    preparedGasWord diff=(preparedGasWord gas+18446744073709551616-preparedGasWord fee)%18446744073709551616 := by
  have total:=prepared_gas_nat_total gas fee diff borrow equations
  have gb:=prepared_gas_word_bound gas gasBounds
  have fb:=prepared_gas_word_bound fee feeBounds
  have db:=prepared_gas_word_bound diff diffBounds
  refine ⟨by omega,by omega,?_⟩
  by_cases zero : borrow 3=0
  · have eq : preparedGasWord gas+18446744073709551616-preparedGasWord fee =
      preparedGasWord diff+18446744073709551616 := by omega
    rw [eq,Nat.add_mod]
    simp only [Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt db]
  · have eq : preparedGasWord gas+18446744073709551616-preparedGasWord fee =
      preparedGasWord diff := by omega
    rw [eq,Nat.mod_eq_of_lt db]
/-- Balanced 16-term reduction used literally by Python sm for this profile. -/
def preparedGasSumTree (term : Nat → Expr) : Nat → Nat → Expr
  | 0,offset => term offset
  | depth+1,offset => .add (preparedGasSumTree term depth offset)
      (preparedGasSumTree term depth (offset+2^depth))

def preparedGasBits (base : Nat) : Expr :=
  preparedGasSumTree (fun i => .mul (.const (2^i)) (.col (base+i) false)) 4 0

def preparedGasFetch (field : Nat) : Expr :=
  preparedGasSumTree (fun i => .mul (.col i false) (.pub (56+10*i+field))) 4 0

def preparedGasEnv (row : Nat → Fp) (pub : List Fp) : Env Fp :=
  {instructionAddEnv row with pub:=fun i => pub.getD i 0}

theorem prepared_gas_bits_horner (row : Nat → Fp) (pub : List Fp) (base : Nat) :
    (preparedGasBits base).evalWith (preparedGasEnv row pub)=
      (instructionBitExpr base 16).evalWith (instructionAddEnv row) := by
  simp only [preparedGasBits,preparedGasSumTree,instructionBitExpr,Expr.evalWith,
    preparedGasEnv,instructionAddEnv,Nat.reduceAdd,Nat.reducePow,Nat.add_zero,Nat.add_assoc]
  simp only [←Fp.ofNat_def]
  grind
def preparedGasBoolean (col : Nat) : Expr :=
  .add (instructionBitConstraint col) (.neg (.const 0))

def preparedGasSubtract (limb : Nat) : Expr :=
  .add (.add (.add (preparedGasBits (283+16*limb)) (.neg (preparedGasFetch (6+limb))))
      (.neg (if limb=0 then .const 0 else .col (411+limb-1) false)))
    (.neg (.add (preparedGasBits (347+16*limb))
      (.neg (.mul (.const 65536) (.col (411+limb) false)))))

/-- Exact Boolean and subtraction expression subset of the 449-column AIR. -/
def preparedGasConstraints : List Expr :=
  (List.range 449).map preparedGasBoolean ++ (List.range 4).map preparedGasSubtract

def PreparedGasHolds (row : Nat → Fp) (pub : List Fp) : Prop :=
  ∀ e∈preparedGasConstraints,e.evalWith (preparedGasEnv row pub)=0

def preparedGasLimb (row : Nat → Fp) (pub : List Fp) (base i : Nat) : Fp :=
  (preparedGasBits (base+16*i)).evalWith (preparedGasEnv row pub)

def preparedGasFee (row : Nat → Fp) (pub : List Fp) (i : Nat) : Fp :=
  (preparedGasFetch (6+i)).evalWith (preparedGasEnv row pub)

theorem prepared_gas_boolean (row : Nat → Fp) (pub : List Fp)
    (holds : PreparedGasHolds row pub) (col : Nat) (hc : col<449) : (row col).toNat≤1 := by
  have h := holds (preparedGasBoolean col) (List.mem_append_left _
    (List.mem_map.mpr ⟨col,List.mem_range.mpr hc,rfl⟩))
  change row col*(row col+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

theorem prepared_gas_limb_bound (row : Nat → Fp) (pub : List Fp)
    (holds : PreparedGasHolds row pub) (base i : Nat) (fits : base+16*i+16≤449) :
    (preparedGasLimb row pub base i).toNat<65536 := by
  unfold preparedGasLimb
  rw [prepared_gas_bits_horner]
  exact instruction_bit_expr_bound row 16 _ (by decide) (fun k hk =>
    prepared_gas_boolean row pub holds _ (by omega))

/-- All local values are bounded from source bit polynomials; the selected
public fee's four limb bounds are the explicit external lookup obligation. -/
theorem prepared_gas_limb_equation (row : Nat → Fp) (pub : List Fp)
    (holds : PreparedGasHolds row pub)
    (feeBounds : ∀ i,i<4 → (preparedGasFee row pub i).toNat<65536)
    (i : Nat) (hi : i<4) :
    (preparedGasLimb row pub 347 i).toNat+(preparedGasFee row pub i).toNat+
      (if i=0 then 0 else (row (411+(i-1))).toNat) =
    (preparedGasLimb row pub 283 i).toNat+65536*(row (411+i)).toNat := by
  have h := holds (preparedGasSubtract i) (List.mem_append_right _
    (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))
  have gb := prepared_gas_limb_bound row pub holds 283 i (by omega)
  have db := prepared_gas_limb_bound row pub holds 347 i (by omega)
  have cb := prepared_gas_boolean row pub holds (411+i) (by omega)
  by_cases zero : i=0
  · subst i
    change preparedGasLimb row pub 283 0 + -preparedGasFee row pub 0 + -(0:Fp) +
      -(preparedGasLimb row pub 347 0 + -((65536:Fp)*row 411))=0 at h
    have eq : preparedGasLimb row pub 347 0+preparedGasFee row pub 0+(0:Fp)=
      preparedGasLimb row pub 283 0+(65536:Fp)*row 411 := by grind
    exact instruction_add_limb_sound _ _ 0 _ _ db (feeBounds 0 hi) (by decide) gb cb eq
  · have pb := prepared_gas_boolean row pub holds (411+(i-1)) (by omega)
    have idx : 411+i-1=411+(i-1) := by omega
    simp only [preparedGasSubtract,ite_eq_right zero,Expr.evalWith] at h
    change preparedGasLimb row pub 283 i + -preparedGasFee row pub i + -row (411+i-1) +
      -(preparedGasLimb row pub 347 i + -((65536:Fp)*row (411+i)))=0 at h
    rw [idx] at h
    have eq : preparedGasLimb row pub 347 i+preparedGasFee row pub i+row (411+(i-1))=
      preparedGasLimb row pub 283 i+(65536:Fp)*row (411+i) := by grind
    simpa only [ite_eq_right zero] using
      instruction_add_limb_sound _ _ _ _ _ db (feeBounds i hi) pb gb cb eq

/-- Concrete AIR-to-Nat64 subtraction and exact terminal borrow comparison.
There is no caller supplied fee-versus-gas comparison premise. -/
theorem prepared_gas_borrow_sound (row : Nat → Fp) (pub : List Fp)
    (holds : PreparedGasHolds row pub)
    (feeBounds : ∀ i,i<4 → (preparedGasFee row pub i).toNat<65536) :
    let gas := preparedGasWord (fun i => (preparedGasLimb row pub 283 i).toNat)
    let fee := preparedGasWord (fun i => (preparedGasFee row pub i).toNat)
    let diff := preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat)
    ((row 414).toNat=1 ↔ gas<fee) ∧ ((row 414).toNat=0 ↔ fee≤gas) ∧
      diff=(gas+18446744073709551616-fee)%18446744073709551616 := by
  apply prepared_gas_nat_borrow (fun i => (preparedGasLimb row pub 283 i).toNat)
    (fun i => (preparedGasFee row pub i).toNat) (fun i => (preparedGasLimb row pub 347 i).toNat)
    (fun i => (row (411+i)).toNat)
  · intro i hi; exact prepared_gas_limb_bound row pub holds 283 i (by omega)
  · exact feeBounds
  · intro i hi; exact prepared_gas_limb_bound row pub holds 347 i (by omega)
  · exact prepared_gas_boolean row pub holds 414 (by decide)
  · exact prepared_gas_limb_equation row pub holds feeBounds
end NearCompression
