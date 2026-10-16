import NearCompression.SHA512BlockDecode

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.SHA512

/-- Canonical big-endian bytes of a 64-bit word. -/
def sha512NatWordBytes (word : Nat) : List Nat :=
  [word / 72057594037927936 % 256, word / 281474976710656 % 256,
   word / 1099511627776 % 256, word / 4294967296 % 256,
   word / 16777216 % 256, word / 65536 % 256, word / 256 % 256, word % 256]

theorem sha512_nat_word_bytes_length (word : Nat) : (sha512NatWordBytes word).length = 8 := rfl

theorem sha512_nat_word_bytes_bound (word byte : Nat) (h : byte ∈ sha512NatWordBytes word) :
    byte < 256 := by
  simp only [sha512NatWordBytes,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst byte <;> exact Nat.mod_lt _ (by decide)

set_option maxHeartbeats 800000 in
theorem sha512_nat_word_bytes_bits (row : Nat → Fp) (base : Nat)
    (boolean : ∀ bit, bit < 64 → (row (base+bit)).toNat ≤ 1) :
    sha512NatWordBytes (sha512BitsWord row base) = sha512WindowWordBytes row base := by
  have h0 := sha512_window_byte_bound row base 0 (by decide) boolean
  have h1 := sha512_window_byte_bound row base 1 (by decide) boolean
  have h2 := sha512_window_byte_bound row base 2 (by decide) boolean
  have h3 := sha512_window_byte_bound row base 3 (by decide) boolean
  have h4 := sha512_window_byte_bound row base 4 (by decide) boolean
  have h5 := sha512_window_byte_bound row base 5 (by decide) boolean
  have h6 := sha512_window_byte_bound row base 6 (by decide) boolean
  have h7 := sha512_window_byte_bound row base 7 (by decide) boolean
  have split := sha512_word_byte_split row base
  simp only [sha512NatWordBytes,sha512WindowWordBytes]
  simp only [List.cons.injEq]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;> omega

end NearCompression
