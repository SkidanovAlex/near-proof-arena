import ZkFormal.Sha.Sound.Bits
import NearSpecV3.SHA512

/-! Bit semantics for the actual SHA-512 functions. Adapted from the existing
SHA-256 bit proof structure, with 64-bit bounds and the actual SHA512 helpers.
Generic bit reconstruction lemmas are reused from ZkFormal.Sha.Sound.Bits. -/
namespace NearCompression
open NearSpecV3.SHA512
open ZkFormal.Sha.Sound (bt bt_eq bt_xor bt_and bt_of_lt bt_shiftRight)

theorem sha512_bt_mask64 {b : Nat} (hb : b < 64) : bt mask64 b = 1 := by
  rw [bt_eq, show mask64 = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hb]

theorem sha512_testBit_rotr {x n b : Nat} (hx : x < 2 ^ 64) (hn : n < 64) (hb : b < 64) :
    (rotr x n).testBit b = x.testBit ((b + n) % 64) := by
  unfold rotr
  rw [show mask64 = 2 ^ 64 - 1 from rfl, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : b + n < 64
  · rw [Nat.mod_eq_of_lt h]
    have h1 : ¬ (b ≥ 64 - n) := by omega
    simp [h1, hb, Nat.add_comm]
  · have h1 : x.testBit (n + b) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : (b + n) % 64 = b - (64 - n) := by omega
    have h3 : b ≥ 64 - n := by omega
    simp [h1, h2, h3, hb]

theorem sha512_bt_rotr {x n b : Nat} (hx : x < 2 ^ 64) (hn : n < 64) (hb : b < 64) :
    bt (rotr x n) b = bt x ((b + n) % 64) := by
  rw [bt_eq, bt_eq, sha512_testBit_rotr hx hn hb]

theorem sha512_bt_sig3 {x r1 r2 r3 b : Nat} (hx : x < 2 ^ 64) (h1 : r1 < 64) (h2 : r2 < 64) (h3 : r3 < 64)
    (hb : b < 64) :
    bt (rotr x r1 ^^^ rotr x r2 ^^^ rotr x r3) b =
      ((bt x ((b + r1) % 64) + bt x ((b + r2) % 64)) % 2 + bt x ((b + r3) % 64)) % 2 := by
  rw [bt_xor, bt_xor, sha512_bt_rotr hx h1 hb, sha512_bt_rotr hx h2 hb, sha512_bt_rotr hx h3 hb]

theorem sha512_bt_sigS {x r1 r2 r3 b : Nat} (hx : x < 2 ^ 64) (h1 : r1 < 64) (h2 : r2 < 64)
    (hb : b < 64) :
    bt (rotr x r1 ^^^ rotr x r2 ^^^ (x >>> r3)) b =
      ((bt x ((b + r1) % 64) + bt x ((b + r2) % 64)) % 2 +
        (if b + r3 < 64 then bt x (b + r3) else 0)) % 2 := by
  rw [bt_xor, bt_xor, sha512_bt_rotr hx h1 hb, sha512_bt_rotr hx h2 hb, bt_shiftRight, Nat.add_comm r3 b]
  by_cases h : b + r3 < 64
  · simp only [h, ite_true]
  · simp only [h, ite_false, bt_of_lt (b := b + r3) hx (by omega)]

theorem sha512_bt_ch {x y z b : Nat} (hb : b < 64) :
    bt (ch x y z) b = (bt x b * bt y b + ((bt x b + 1) % 2) * bt z b) % 2 := by
  unfold ch
  rw [bt_xor, bt_and, bt_and, bt_xor, sha512_bt_mask64 hb]

theorem sha512_bt_maj (x y z b : Nat) :
    bt (maj x y z) b = ((bt x b * bt y b + bt x b * bt z b) % 2 + bt y b * bt z b) % 2 := by
  unfold maj
  rw [bt_xor, bt_xor, bt_and, bt_and, bt_and]

theorem sha512_rotr_lt (x n : Nat) : rotr x n < 2 ^ 64 := by
  unfold rotr; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem sha512_sig3_lt (x r1 r2 r3 : Nat) : rotr x r1 ^^^ rotr x r2 ^^^ rotr x r3 < 2 ^ 64 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (sha512_rotr_lt _ _) (sha512_rotr_lt _ _)) (sha512_rotr_lt _ _)

theorem sha512_sigS_lt {x : Nat} (hx : x < 2 ^ 64) (r1 r2 r3 : Nat) :
    rotr x r1 ^^^ rotr x r2 ^^^ (x >>> r3) < 2 ^ 64 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (sha512_rotr_lt _ _) (sha512_rotr_lt _ _))
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)

theorem sha512_ch_lt (x : Nat) {y z : Nat} (hy : y < 2 ^ 64) (hz : z < 2 ^ 64) : ch x y z < 2 ^ 64 := by
  unfold ch
  exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz)

theorem sha512_maj_lt (x : Nat) {y z : Nat} (hy : y < 2 ^ 64) (hz : z < 2 ^ 64) : maj x y z < 2 ^ 64 := by
  unfold maj
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz))
    (Nat.and_lt_two_pow _ hz)


end NearCompression
