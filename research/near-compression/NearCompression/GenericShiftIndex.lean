import NearCompression.GenericRowMLE
import NearCompression.GenericShiftKernel

/-! Natural-number indexing of the borrow automaton, including zero/empty
wraparound. This bridges the bit permutation in shift_kernel_dp_weighted to
the predecessor permutation used to reduce cyclic-next openings. -/
namespace NearCompression

def shiftListBitIndex : List Bool → Nat
  | [] => 0
  | bit::bits => (if bit then 1 else 0)+2*shiftListBitIndex bits

theorem shift_list_bit_index_bound (bits : List Bool) :
    shiftListBitIndex bits<2^bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    simp only [shiftListBitIndex,List.length_cons,Nat.pow_succ]
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem shift_subtract_bits_length (borrow : Bool) (bits : List Bool) :
    (shiftSubtractBits borrow bits).length=bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp only [shiftSubtractBits,List.length_cons,ih]

theorem shift_subtract_false (bits : List Bool) : shiftSubtractBits false bits=bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [shiftSubtractBits,shiftBorrowStep,Bool.xor_false,Bool.false_and,ih]

/-- Subtracting one decrements the index, or wraps zero to the maximal index. -/
theorem shift_subtract_index_carry (bits : List Bool) :
    shiftListBitIndex (shiftSubtractBits true bits)+1=
      if shiftListBitIndex bits=0 then 2^bits.length else shiftListBitIndex bits := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    cases bit
    · simp only [shiftSubtractBits,shiftBorrowStep,Bool.xor_true,Bool.not_false,
        Bool.true_and,shiftListBitIndex,Bool.false_eq_true,ite_false,ite_true,
        Nat.zero_add,List.length_cons,Nat.pow_succ]
      split at ih <;> split <;> omega
    · simp only [shiftSubtractBits,shiftBorrowStep,Bool.xor_true,Bool.not_true,
        Bool.true_and,shift_subtract_false,shiftListBitIndex,Bool.false_eq_true,
        ite_false,ite_true,Nat.zero_add,List.length_cons,Nat.pow_succ]
      split <;> omega

/-- Index form of subtraction, with no positivity premise on the input index. -/
theorem shift_subtract_index_mod (bits : List Bool) :
    shiftListBitIndex (shiftSubtractBits true bits)=
      (shiftListBitIndex bits+2^bits.length-1)%(2^bits.length) := by
  have carry := shift_subtract_index_carry bits
  have bound := shift_list_bit_index_bound bits
  have positive : 0<2^bits.length := Nat.two_pow_pos _
  by_cases zero : shiftListBitIndex bits=0
  · rw [if_pos zero] at carry
    rw [zero,Nat.zero_add,Nat.mod_eq_of_lt (by omega : 2^bits.length-1<2^bits.length)]
    omega
  · rw [if_neg zero] at carry
    have rearrange : shiftListBitIndex bits+2^bits.length-1=(shiftListBitIndex bits-1)+2^bits.length := by omega
    rw [rearrange,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega : shiftListBitIndex bits-1<2^bits.length)]
    omega

/-- Reindexing inverse needed for the cyclic-next opening reduction. -/
theorem shift_subtract_successor_mod (bits : List Bool) :
    (shiftListBitIndex (shiftSubtractBits true bits)+1)%(2^bits.length)=shiftListBitIndex bits := by
  rw [shift_subtract_index_carry]
  by_cases zero : shiftListBitIndex bits=0
  · rw [if_pos zero,Nat.mod_self,zero]
  · rw [if_neg zero,Nat.mod_eq_of_lt (shift_list_bit_index_bound bits)]

/-- The generic row MLE uses exactly this little-endian list indexing. -/
theorem shift_list_generic_index (bits : List Bool) :
    genericRowBitIndex bits.length (fun i => bits.getD i false)=shiftListBitIndex bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    change (if bit then 1 else 0)+2*genericRowBitIndex bits.length (fun i => bits.getD i false)=_
    rw [ih]
    rfl

/-- The transformed bit vector indexes the actual cyclic predecessor row. -/
theorem shift_subtract_generic_index (bits : List Bool) :
    genericRowBitIndex bits.length (fun i => (shiftSubtractBits true bits).getD i false)=
      (genericRowBitIndex bits.length (fun i => bits.getD i false)+2^bits.length-1)%(2^bits.length) := by
  have index := shift_list_generic_index (shiftSubtractBits true bits)
  rw [shift_subtract_bits_length] at index
  rw [index,shift_list_generic_index,shift_subtract_index_mod]

/-- Evaluating the cyclic-next oracle at the predecessor bit vector returns
the original row. This is the Boolean reindexing used by the shift kernel. -/
theorem shift_predecessor_next_mle {K : Type} [Lean.Grind.CommRing K]
    (values : Nat → K) (bits : List Bool) :
    genericRowNextMLE bits.length values
      (genericRowBooleanPoint (fun i => (shiftSubtractBits true bits).getD i false))=
      values (shiftListBitIndex bits) := by
  rw [generic_row_next_mle_boolean]
  have index := shift_list_generic_index (shiftSubtractBits true bits)
  rw [shift_subtract_bits_length] at index
  rw [index,shift_subtract_successor_mod]

end NearCompression
