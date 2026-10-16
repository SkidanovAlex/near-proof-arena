import NearCompression.SHA512ScheduleWindow

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

/-- A byte decoded directly from eight window bits. -/
def sha512WindowByte (row : Nat → Fp) (base offset : Nat) : Nat :=
  ofBits (fun bit => (row (base+8*offset+bit)).toNat) 8

def sha512WindowWordBytes (row : Nat → Fp) (base : Nat) : List Nat :=
  [sha512WindowByte row base 7,sha512WindowByte row base 6,
   sha512WindowByte row base 5,sha512WindowByte row base 4,
   sha512WindowByte row base 3,sha512WindowByte row base 2,
   sha512WindowByte row base 1,sha512WindowByte row base 0]

theorem sha512_word_byte_split (row : Nat → Fp) (base : Nat) :
    sha512BitsWord row base =
      sha512WindowByte row base 0 + 256*sha512WindowByte row base 1 +
      65536*sha512WindowByte row base 2 + 16777216*sha512WindowByte row base 3 +
      4294967296*sha512WindowByte row base 4 + 1099511627776*sha512WindowByte row base 5 +
      281474976710656*sha512WindowByte row base 6 + 72057594037927936*sha512WindowByte row base 7 := by
  unfold sha512BitsWord
  rw [show 64=56+8 from rfl,ofBits_add,show 56=48+8 from rfl,ofBits_add,
    show 48=40+8 from rfl,ofBits_add,show 40=32+8 from rfl,ofBits_add,
    show 32=24+8 from rfl,ofBits_add,show 24=16+8 from rfl,ofBits_add,
    show 16=8+8 from rfl,ofBits_add]
  simp only [sha512WindowByte,Nat.mul_zero,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd,Nat.reducePow]
  simp only [Nat.add_assoc]

/-- The specification's big-endian word parser reverses the byte decoder. -/
theorem sha512_word_bytes_parse (row : Nat → Fp) (base : Nat) (tail : List Nat) :
    words (sha512WindowWordBytes row base ++ tail) = sha512BitsWord row base :: words tail := by
  change (((((((sha512WindowByte row base 7 * 256 + sha512WindowByte row base 6) * 256 +
    sha512WindowByte row base 5) * 256 + sha512WindowByte row base 4) * 256 +
    sha512WindowByte row base 3) * 256 + sha512WindowByte row base 2) * 256 +
    sha512WindowByte row base 1) * 256 + sha512WindowByte row base 0) :: words tail = _
  rw [sha512_word_byte_split]
  congr 1
  omega

def sha512DecodedBlock (row : Nat → Fp) : List Nat :=
  (List.range 16).flatMap (fun i => sha512WindowWordBytes row (sha512ScheduleWindowBase i))

theorem sha512_word_bytes_parse_many (row : Nat → Fp) (indices : List Nat) :
    words (indices.flatMap (fun i => sha512WindowWordBytes row (sha512ScheduleWindowBase i))) =
      indices.map (sha512ScheduleWindowWord row) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    rw [List.flatMap_cons,sha512_word_bytes_parse,ih]
    rfl

theorem sha512_decoded_block_words (row : Nat → Fp) :
    words (sha512DecodedBlock row) = sha512ScheduleWindow row :=
  sha512_word_bytes_parse_many row (List.range 16)

set_option maxRecDepth 8192 in
theorem sha512_decoded_block_length (row : Nat → Fp) : (sha512DecodedBlock row).length = 128 := by
  rfl

theorem sha512_window_byte_bound (row : Nat → Fp) (base offset : Nat) (ho : offset < 8)
    (boolean : ∀ bit, bit < 64 → (row (base+bit)).toNat ≤ 1) :
    sha512WindowByte row base offset < 256 := by
  apply ofBits_lt
  intro bit hb
  simpa only [Nat.add_assoc] using boolean (8*offset+bit) (by omega)

theorem sha512_word_bytes_bound (row : Nat → Fp) (base : Nat)
    (boolean : ∀ bit, bit < 64 → (row (base+bit)).toNat ≤ 1)
    (byte : Nat) (hb : byte ∈ sha512WindowWordBytes row base) : byte < 256 := by
  simp only [sha512WindowWordBytes,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb <;> subst byte <;>
    exact sha512_window_byte_bound row base _ (by decide) boolean

end NearCompression
