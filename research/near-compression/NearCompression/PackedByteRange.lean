import ZkFormal.Algebra.Fp

/-! Necessary integer range-bus and limb facts for the byte-packed candidate.
The bridge from native LogUp acceptance to integer balance and the complete
packed-AIR refinement are separate, unproved obligations. -/
namespace NearCompression
open ZkFormal.Algebra

def packedByteWeight (rows : List (Nat × Nat)) (value : Nat) : Nat :=
  (rows.map (fun entry => if entry.1=value then entry.2 else 0)).sum

theorem packed_byte_weight_zero_outside (rows : List (Nat × Nat)) (value : Nat)
    (bounded : ∀ entry∈rows,entry.1<256) (outside : 256≤value) :
    packedByteWeight rows value=0 := by
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    have small:=bounded entry (by simp)
    have different : entry.1≠value := by omega
    have tail:=ih (fun e he=>bounded e (by simp [he]))
    simp [packedByteWeight,different] at tail ⊢
    exact tail

/-- A positive send cannot be balanced by bounded receive values if it is
outside the byte range. Multiplicities are naturals, not residues modulo p. -/
theorem packed_byte_range_from_balance (rows : List (Nat × Nat)) (value sends : Nat)
    (bounded : ∀ entry∈rows,entry.1<256) (positive : 0<sends)
    (balance : sends=packedByteWeight rows value) : value<256 := by
  by_cases inside : value<256
  · exact inside
  · have zero:=packed_byte_weight_zero_outside rows value bounded (by omega)
    omega

/-- Two bounded bytes encode one canonical 16-bit limb without field wrap. -/
theorem packed_byte_limb_canonical (lo hi : Nat) (hl : lo<256) (hh : hi<256) :
    lo+256*hi<65536 ∧ (Fp.ofNat (lo+256*hi)).toNat=lo+256*hi := by
  have bound : lo+256*hi<65536 := by omega
  refine ⟨bound,?_⟩
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega)]

theorem packed_byte_limb_injective (lo hi lo' hi' : Nat)
    (hl : lo<256) (_hh : hi<256) (hl' : lo'<256) (_hh' : hi'<256)
    (same : lo+256*hi=lo'+256*hi') : lo=lo' ∧ hi=hi' := by omega

/-- The concrete adversarial test preserves the limb modulo p while violating
its byte decomposition. Arithmetic constraints alone cannot replace range checks. -/
theorem packed_byte_noncanonical_zero :
    ((P-256)+256*1)%P=0 ∧ 256≤P-256 := by decide

end NearCompression
