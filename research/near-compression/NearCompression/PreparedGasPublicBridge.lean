import NearCompression.PreparedGasBorrow
import NearCompression.PreparedFunctionRow
import ZkFormal.Near.Extract.Common

/-! Public CODE limb bounds and actual one-hot PC constraints discharge the
selected-fee premise. Public CODE authentication against Wasm/PREP remains a
separate obligation. Unrelated constraints are retained as source context. -/
set_option autoImplicit false
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def preparedGasSourceConstraints (middle tail : List Expr) : List Expr :=
  (List.range 449).map preparedGasBoolean ++
  [preparedPCResidualPython,preparedSPResidualPython] ++ middle ++
  (List.range 4).map preparedGasSubtract ++ tail

theorem prepared_gas_fetch_source (row next : Nat → Fp) (pub : List Fp)
    (first last : Fp) (field : Nat) :
    (preparedGasFetch field).evalWith (preparedGasEnv row pub)=
    (preparedFetchPython field).evalWith
      (preparedRowEnv row next (fun i => pub.getD i 0) first last) := by
  simp only [preparedGasFetch,preparedFetchPython,preparedGasSumTree,preparedBalancedSum,
    Expr.evalWith,preparedGasEnv,instructionAddEnv,preparedRowEnv,Bool.false_eq_true,ite_false]

theorem prepared_gas_subtract_source (row next : Nat → Fp) (pub : List Fp)
    (first last : Fp) (i : Nat) :
    (preparedGasSubtract i).evalWith (preparedGasEnv row pub)=
    (preparedGasSubtract i).evalWith
      (preparedRowEnv row next (fun j => pub.getD j 0) first last) := by
  by_cases hi : i=0 <;>
    simp only [preparedGasSubtract,hi,ite_true,ite_false,preparedGasBits,preparedGasFetch,
      preparedGasSumTree,Expr.evalWith,preparedGasEnv,instructionAddEnv,preparedRowEnv,Bool.false_eq_true,ite_false]

/-- Extract source Boolean/gas polynomials and exact PC/SP choice residuals
from full constraints, preserving all unrelated intervening/trailing checks. -/
theorem prepared_gas_extract_source (middle tail : List Expr) (row next : Nat → Fp)
    (pub : List Fp) (first last : Fp)
    (holds : ∀ e∈preparedGasSourceConstraints middle tail,
      e.evalWith (preparedRowEnv row next (fun i => pub.getD i 0) first last)=0) :
    PreparedGasHolds row pub ∧
      preparedRowChoices row next (fun i => pub.getD i 0) first last := by
  have bool : ∀ i,i<449 →
      (preparedGasBoolean i).evalWith (preparedRowEnv row next (fun j => pub.getD j 0) first last)=0 := by
    intro i hi
    apply holds
    simp only [preparedGasSourceConstraints,List.mem_append]
    apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have arith : ∀ i,i<4 →
      (preparedGasSubtract i).evalWith (preparedRowEnv row next (fun j => pub.getD j 0) first last)=0 := by
    intro i hi
    apply holds
    simp only [preparedGasSourceConstraints,List.mem_append]
    apply Or.inl; apply Or.inr
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      exact bool i (List.mem_range.mp hi)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      rw [prepared_gas_subtract_source row next pub first last]
      exact arith i (List.mem_range.mp hi)
  · apply prepared_python_choices
    · intro i hi
      have h:=bool i hi
      change row i*(row i+ -(1:Fp))+ -(0:Fp)=0 at h
      change row i*(row i+ -(1:Fp))=0
      grind
    · apply holds
      simp [preparedGasSourceConstraints]
    · apply holds
      simp [preparedGasSourceConstraints]

/-- One-hot PC plus bounded public CODE fee limbs suffices: selected fee
canonicality is no longer an external premise. -/
theorem prepared_gas_public_fee_bounds (row next : Nat → Fp) (pub : List Fp) (first last : Fp)
    (choices : preparedRowChoices row next (fun i => pub.getD i 0) first last)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 →
      (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536) :
    ∀ i,i<4 → (preparedGasFee row pub i).toNat<65536 := by
  intro i hi
  unfold preparedGasFee
  rw [prepared_gas_fetch_source row next pub first last]
  exact prepared_fetch_fee_bounds row next _ first last choices publicBounds i hi

/-- Full source-context to exact gas subtraction; public bytecode origin is
not silently assumed or authenticated by this local theorem. -/
theorem prepared_gas_public_sound (middle tail : List Expr) (row next : Nat → Fp)
    (pub : List Fp) (first last : Fp)
    (holds : ∀ e∈preparedGasSourceConstraints middle tail,
      e.evalWith (preparedRowEnv row next (fun i => pub.getD i 0) first last)=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 →
      (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536) :
    let gas := preparedGasWord (fun i => (preparedGasLimb row pub 283 i).toNat)
    let fee := preparedGasWord (fun i => (preparedGasFee row pub i).toNat)
    let diff := preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat)
    ((row 414).toNat=1 ↔ gas<fee) ∧ ((row 414).toNat=0 ↔ fee≤gas) ∧
      diff=(gas+18446744073709551616-fee)%18446744073709551616 := by
  have source := prepared_gas_extract_source middle tail row next pub first last holds
  exact prepared_gas_borrow_sound row pub source.1
    (prepared_gas_public_fee_bounds row next pub first last source.2 publicBounds)
theorem prepared_gas_row_env (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowEnv tr t r pub=preparedRowEnv (tr.cell t r)
      (tr.cell t ((r+1)%tr.height t)) (fun i => pub.getD i 0)
      (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0) := by
  simp only [rowEnv,preparedRowEnv]
  congr 1
  · funext c nx; cases nx <;> rfl
  · split <;> grind

/-- A checked local AIR row with the actual source constraint decomposition
supplies all gas and public-choice obligations; no manually selected subset
validity premise remains. -/
theorem prepared_gas_table_local (table : Table) (middle tail : List Expr)
    (source : table.constraints=preparedGasSourceConstraints middle tail)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (hr : r<tr.height t)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 →
      (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536) :
    let row := tr.cell t r
    let gas := preparedGasWord (fun i => (preparedGasLimb row pub 283 i).toNat)
    let fee := preparedGasWord (fun i => (preparedGasFee row pub i).toNat)
    let diff := preparedGasWord (fun i => (preparedGasLimb row pub 347 i).toNat)
    ((row 414).toNat=1 ↔ gas<fee) ∧ ((row 414).toNat=0 ↔ fee≤gas) ∧
      diff=(gas+18446744073709551616-fee)%18446744073709551616 := by
  apply prepared_gas_public_sound middle tail (tr.cell t r) (tr.cell t ((r+1)%tr.height t)) pub
    (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0) _ publicBounds
  intro e he
  have h := localH.constr r hr e (by rw [source]; exact he)
  rw [Expr.eval,prepared_gas_row_env] at h
  exact h
end NearCompression
