import NearCompression.PreparedMemorySigned
import NearCompression.SHA512Round
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound

/-- Canonical16-bit field decoding, used before joining limbs into64-bit words. -/
theorem prepared_memory_limb_nat (row : Nat→Fp) (base : Nat)
    (bits:∀b,b<16→(row (base+b)).toNat≤1) :
    (preparedMemoryAddressLimb row base).toNat=ofBits (fun b=>(row (base+b)).toNat) 16 := by
  unfold preparedMemoryAddressLimb
  rw [prepared_gas_bits_horner,sha512_bit_expr_field,Fp.toNat_ofNat]
  have small:=ofBits_lt bits
  apply Nat.mod_eq_of_lt
  change ofBits (fun b=>(row (base+b)).toNat) 16<65536 at small
  unfold ZkFormal.Algebra.P;omega

theorem prepared_memory_word_limbs (row : Nat→Fp) (base : Nat)
    (bits:∀b,b<64→(row (base+b)).toNat≤1) :
    preparedMemoryWord row base=
      (preparedMemoryAddressLimb row base).toNat+65536*(preparedMemoryAddressLimb row (base+16)).toNat+
      4294967296*(preparedMemoryAddressLimb row (base+32)).toNat+
      281474976710656*(preparedMemoryAddressLimb row (base+48)).toNat := by
  have limb (offset : Nat) (ho:offset+16≤64) := prepared_memory_limb_nat row (base+offset)
    (fun b hb=>by have h:=bits (offset+b) (by omega);simpa only [Nat.add_assoc] using h)
  have zero:=limb 0 (by decide)
  simp only [Nat.add_zero] at zero
  rw [zero,limb 16 (by decide),limb 32 (by decide),limb 48 (by decide)]
  exact sha512_word_bits_split row base

/-- Equality of four canonical limbs binds actual natural64-bit words;
a single field equality of entire64-bit values would not suffice. -/
theorem prepared_memory_word_of_limb_eq (a b : Nat→Fp) (abase bbase : Nat)
    (abits:∀i,i<64→(a (abase+i)).toNat≤1) (bbits:∀i,i<64→(b (bbase+i)).toNat≤1)
    (limbs:∀i:Fin 4,preparedMemoryAddressLimb a (abase+16*i)=preparedMemoryAddressLimb b (bbase+16*i)) :
    preparedMemoryWord a abase=preparedMemoryWord b bbase := by
  rw [prepared_memory_word_limbs a abase abits,prepared_memory_word_limbs b bbase bbits]
  have e0:=limbs ⟨0,by decide⟩;have e1:=limbs ⟨1,by decide⟩
  have e2:=limbs ⟨2,by decide⟩;have e3:=limbs ⟨3,by decide⟩
  simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul] at e0 e1 e2 e3
  rw [e0,e1,e2,e3]
end NearCompression
