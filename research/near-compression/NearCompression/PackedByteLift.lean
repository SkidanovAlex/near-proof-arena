import NearCompression.PackedByteRange

/-! Canonical byte reconstruction. Whole-AIR refinement remains separate. -/
namespace NearCompression

def packedBits (n value : Nat) : List Nat :=
  match n with
  | 0 => []
  | n+1 => value%2 :: packedBits n (value/2)

def packedBitsValue : List Nat → Nat
  | [] => 0
  | b::bs => b+2*packedBitsValue bs

theorem packed_bits_boolean (n value : Nat) :
    ∀ b ∈ packedBits n value, b=0 ∨ b=1 := by
  induction n generalizing value with
  | zero => simp [packedBits]
  | succ n ih =>
    intro b hb
    simp only [packedBits,List.mem_cons] at hb
    rcases hb with h | h
    · have bound := Nat.mod_lt value (by decide : 0<2)
      omega
    · exact ih (value/2) b h

theorem packed_bits_length (n value : Nat) : (packedBits n value).length=n := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih => simp [packedBits,ih]

theorem packed_bits_reconstruct (n value : Nat) (bound : value<2^n) :
    packedBitsValue (packedBits n value)=value := by
  induction n generalizing value with
  | zero =>
    simp only [Nat.pow_zero] at bound
    have : value=0 := by omega
    simp [this,packedBits,packedBitsValue]
  | succ n ih =>
    have smaller : value/2<2^n := by
      rw [Nat.pow_succ] at bound
      omega
    simp only [packedBits,packedBitsValue,ih (value/2) smaller]
    omega

theorem packed_bits_append (a b : List Nat) :
    packedBitsValue (a++b)=packedBitsValue a+2^a.length*packedBitsValue b := by
  induction a with
  | nil => simp [packedBitsValue]
  | cons x xs ih =>
    simp only [List.cons_append,packedBitsValue,List.length_cons,ih,Nat.pow_succ]
    simp [Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc]

/-- Range-checked bytes lift to Boolean bits with exactly the original limb. -/
theorem packed_byte_pair_lift (lo hi : Nat) (hl : lo<256) (hh : hi<256) :
    let bits := packedBits 8 lo ++ packedBits 8 hi
    bits.length=16 ∧ (∀ b∈bits,b=0 ∨ b=1) ∧
      packedBitsValue bits=lo+256*hi := by
  dsimp
  refine ⟨by simp [packed_bits_length], ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact packed_bits_boolean 8 lo b h
    · exact packed_bits_boolean 8 hi b h
  · rw [packed_bits_append,packed_bits_length,
      packed_bits_reconstruct 8 lo hl,packed_bits_reconstruct 8 hi hh]

/-- Inactive zero bytes reconstruct to zero bits. -/
theorem packed_bits_zero (n : Nat) : ∀ b∈packedBits n 0,b=0 := by
  induction n with
  | zero => simp [packedBits]
  | succ n ih => simpa [packedBits] using ih

/-- Exact natural bus balance supplies the range premises for reconstruction.
No cryptographic acceptance-to-balance implication is assumed implicitly. -/
theorem packed_balanced_pair_lift (rows : List (Nat × Nat))
    (lo hi loSends hiSends : Nat)
    (bounded : ∀ entry∈rows,entry.1<256)
    (loPositive : 0<loSends) (hiPositive : 0<hiSends)
    (loBalance : loSends=packedByteWeight rows lo)
    (hiBalance : hiSends=packedByteWeight rows hi) :
    ∃ bits : List Nat, bits.length=16 ∧
      (∀ b∈bits,b=0 ∨ b=1) ∧ packedBitsValue bits=lo+256*hi ∧
      (ZkFormal.Algebra.Fp.ofNat (packedBitsValue bits)).toNat=lo+256*hi := by
  have hl := packed_byte_range_from_balance rows lo loSends bounded loPositive loBalance
  have hh := packed_byte_range_from_balance rows hi hiSends bounded hiPositive hiBalance
  obtain ⟨len,boolean,value⟩ := packed_byte_pair_lift lo hi hl hh
  refine ⟨packedBits 8 lo ++ packedBits 8 hi,len,boolean,value,?_⟩
  rw [value]
  exact (packed_byte_limb_canonical lo hi hl hh).2

end NearCompression
