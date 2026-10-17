import NearCompression.PreparedGasBorrow
set_option maxRecDepth 4096
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra
/-- Exact Boolean and address-carry AST subset of scalar-memory-access-v1.
No opcode/stack/code provenance is assumed to follow from this subset. -/
def preparedMemoryAddressEquations : List Expr := [
  .add (.add (preparedGasBits 115) (preparedGasBits 147))
    (.neg (.add (preparedGasBits 179) (.mul (.const 65536) (.col 454 false)))),
  .add (.add (.add (preparedGasBits 131) (preparedGasBits 163)) (.col 454 false))
    (.neg (.add (preparedGasBits 195) (.mul (.const 65536) (.col 455 false)))),
  .add (.col 211 false) (.neg (.col 455 false))]
def preparedMemoryAddressConstraints : List Expr :=
  (List.range 460).map preparedGasBoolean ++ preparedMemoryAddressEquations
def PreparedMemoryAddressHolds (row : Nat→Fp) : Prop :=
  ∀e∈preparedMemoryAddressConstraints,e.evalWith (preparedGasEnv row [])=0

def preparedMemoryAddressLimb (row : Nat→Fp) (base : Nat) : Fp :=
  (preparedGasBits base).evalWith (preparedGasEnv row [])
def preparedMemoryAddressWord (row : Nat→Fp) (base : Nat) : Nat :=
  (preparedMemoryAddressLimb row base).toNat+65536*(preparedMemoryAddressLimb row (base+16)).toNat

theorem prepared_memory_address_boolean (row : Nat→Fp) (holds : PreparedMemoryAddressHolds row)
    (i : Nat) (hi : i<460) : (row i).toNat≤1 := by
  have h:=holds (preparedGasBoolean i) (List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))
  simp only [preparedGasBoolean,instructionBitConstraint,Expr.evalWith,preparedGasEnv,instructionAddEnv] at h
  change row i * (row i + -(1:Fp)) + -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

theorem prepared_memory_address_limb_bound (row : Nat→Fp) (holds : PreparedMemoryAddressHolds row)
    (base : Nat) (hb : base+16≤460) : (preparedMemoryAddressLimb row base).toNat<65536 := by
  unfold preparedMemoryAddressLimb
  rw [prepared_gas_bits_horner]
  exact instruction_bit_expr_bound row 16 base (by decide)
    (fun k hk=>prepared_memory_address_boolean row holds (base+k) (by omega))

/-- The effective address is a natural 33-bit sum, including carry out of
uint32. It is never the wrapped 32-bit address. -/
theorem prepared_memory_address_exact (row : Nat→Fp) (holds : PreparedMemoryAddressHolds row) :
    preparedMemoryAddressWord row 179+4294967296*(row 211).toNat =
      preparedMemoryAddressWord row 115+preparedMemoryAddressWord row 147 := by
  have get (e : Expr) (he : e∈preparedMemoryAddressEquations) :=
    holds e (List.mem_append_right _ he)
  have h0:=get (preparedMemoryAddressEquations[0]'(by decide)) (by simp [preparedMemoryAddressEquations])
  have h1:=get (preparedMemoryAddressEquations[1]'(by decide)) (by simp [preparedMemoryAddressEquations])
  have h2:=get (preparedMemoryAddressEquations[2]'(by decide)) (by simp [preparedMemoryAddressEquations])
  change preparedMemoryAddressLimb row 115+preparedMemoryAddressLimb row 147+
    -(preparedMemoryAddressLimb row 179+(65536:Fp)*row 454)=0 at h0
  change preparedMemoryAddressLimb row 131+preparedMemoryAddressLimb row 163+row 454+
    -(preparedMemoryAddressLimb row 195+(65536:Fp)*row 455)=0 at h1
  change row 211 + -row 455=0 at h2
  have c0:=prepared_memory_address_boolean row holds 454 (by decide)
  have c1:=prepared_memory_address_boolean row holds 455 (by decide)
  have b (base : Nat) (hb : base+16≤460):=prepared_memory_address_limb_bound row holds base hb
  have l0:=instruction_add_limb_sound _ _ 0 _ _ (b 115 (by decide)) (b 147 (by decide))
    (by decide) (b 179 (by decide)) c0 (by grind)
  have l1:=instruction_add_limb_sound _ _ _ _ _ (b 131 (by decide)) (b 163 (by decide))
    c0 (b 195 (by decide)) c1 (by grind)
  have same : row 211=row 455 := by grind
  rw [same]
  simp only [preparedMemoryAddressWord] at *
  have zero : (0:Fp).toNat=0 := rfl
  rw [zero] at l0
  simp only [Nat.reduceAdd] at *
  omega
end NearCompression
