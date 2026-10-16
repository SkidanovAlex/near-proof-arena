import NearCompression.SHA512Round

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound

/-- Integer equality of bounded words implies each polynomial limb wire. -/
theorem sha512_bit_word_binding_reverse (row : Nat → Fp) (target source : Nat)
    (boolean : ∀ bit, bit < 64 → (row (source + bit)).toNat ≤ 1)
    (ranges : ∀ limb, limb < 4 → (row (target + limb)).toNat < 65536)
    (eq : instructionAdd64Word row target = sha512BitsWord row source)
    (i : Nat) (hi : i < 4) :
    row (target + i) = (instructionBitExpr (source + 16 * i) 16).evalWith (instructionAddEnv row) := by
  let b := fun limb => (instructionBitExpr (source + 16 * limb) 16).evalWith (instructionAddEnv row)
  have bits (limb : Nat) (hl : limb < 4) (bit : Nat) (hb : bit < 16) :
      (row (source + 16 * limb + bit)).toNat ≤ 1 := by
    simpa only [Nat.add_assoc] using boolean (16 * limb + bit) (by omega)
  have brange (limb : Nat) (hl : limb < 4) : (b limb).toNat < 65536 :=
    instruction_bit_expr_bound row 16 (source + 16 * limb) (by decide) (bits limb hl)
  have bdecode (limb : Nat) (hl : limb < 4) :
      (b limb).toNat = ofBits (fun bit => (row (source + 16 * limb + bit)).toNat) 16 := by
    change ((instructionBitExpr (source + 16 * limb) 16).evalWith (instructionAddEnv row)).toNat = _
    rw [sha512_bit_expr_field, Fp.toNat_ofNat]
    have bound := ofBits_lt (bits limb hl)
    apply Nat.mod_eq_of_lt
    change _ < 65536 at bound
    unfold ZkFormal.Algebra.P
    omega
  rw [sha512_word_bits_split] at eq
  have d0 := bdecode 0 (by decide)
  have d1 := bdecode 1 (by decide)
  have d2 := bdecode 2 (by decide)
  have d3 := bdecode 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul] at d0 d1 d2 d3
  rw [← d0, ← d1, ← d2, ← d3] at eq
  have a0 := ranges 0 (by decide); have a1 := ranges 1 (by decide)
  have a2 := ranges 2 (by decide); have a3 := ranges 3 (by decide)
  have b0 := brange 0 (by decide); have b1 := brange 1 (by decide)
  have b2 := brange 2 (by decide); have b3 := brange 3 (by decide)
  simp only [instructionAdd64Word, Nat.add_zero] at eq a0
  change row (target + i) = b i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with hi | hi | hi | hi <;> subst i <;> apply Fp.ext <;> (try simp only [Nat.add_zero]) <;> omega

end NearCompression
