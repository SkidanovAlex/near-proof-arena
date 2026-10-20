import NearCompression.InstructionAdd64

namespace NearCompression
open ZkFormal.Algebra

/-- Four bounded limbs identify exact integer digits, not only field residues. -/
theorem sha512_word_limb_nat (row : Nat → Fp) (base word : Nat)
    (ranges : ∀ i,i<4 → (row (base+i)).toNat<65536)
    (decode : instructionAdd64Word row base=word) (i : Nat) (hi : i<4) :
    (row (base+i)).toNat=(word/65536^i)%65536 := by
  have h0 := ranges 0 (by decide)
  have h1 := ranges 1 (by decide)
  have h2 := ranges 2 (by decide)
  have h3 := ranges 3 (by decide)
  simp only [Nat.add_zero] at h0
  unfold instructionAdd64Word at decode
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with h | h | h | h <;> subst i <;>
    simp only [Nat.reducePow,Nat.add_zero,Nat.div_one] <;> omega

theorem sha512_word_limb_field (row : Nat → Fp) (base word : Nat)
    (ranges : ∀ i,i<4 → (row (base+i)).toNat<65536)
    (decode : instructionAdd64Word row base=word) (i : Nat) (hi : i<4) :
    row (base+i)=Fp.ofNat ((word/65536^i)%65536) := by
  rw [←sha512_word_limb_nat row base word ranges decode i hi,Fp.ofNat_toNat]

theorem sha512_word_limb_bound (row : Nat → Fp) (base : Nat)
    (ranges : ∀ i,i<4 → (row (base+i)).toNat<65536) :
    instructionAdd64Word row base<2^64 := by
  have h0 := ranges 0 (by decide)
  have h1 := ranges 1 (by decide)
  have h2 := ranges 2 (by decide)
  have h3 := ranges 3 (by decide)
  simp only [Nat.add_zero] at h0
  unfold instructionAdd64Word
  omega

end NearCompression
