import NearCompression.SHA384CommittedRouting
import NearCompression.SHA384Padding

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- The actual committed input row, decoded without a caller-supplied message. -/
def sha384CommittedMessage (n : Nat) (pub : List Fp) (tr : Trace Fp) : List Nat :=
  (List.range n).map (fun i => ((instructionBitExpr (8*i) 8).eval tr 2 0 pub).toNat)

theorem sha384_committed_message_length (n : Nat) (pub : List Fp) (tr : Trace Fp) :
    (sha384CommittedMessage n pub tr).length=n := by simp [sha384CommittedMessage]

theorem sha384_committed_message_byte (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (i : Nat) (hi : i<n) :
    (sha384CommittedMessage n pub tr).getD i 0=
      ((instructionBitExpr (8*i) 8).eval tr 2 0 pub).toNat := by
  simp [sha384CommittedMessage,List.getD,hi]

theorem sha384_committed_message_byte_bound (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (i : Nat) (hi : i<n) : (sha384CommittedMessage n pub tr).getD i 0<256 := by
  rw [sha384_committed_message_byte n pub tr i hi]
  exact sha384_committed_input_byte_bound n fixed pub tr h 0 i (Nat.two_pow_pos _) hi

/-- Each existing declared block row decodes to canonical SHA384 padding of
its actual committed input. Sufficient trace capacity remains a separate
obligation; no arbitrary caller message or routing equality is presumed. -/
theorem sha384_committed_padded_byte (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (bound : n≤P) (b j : Nat) (hr : b<tr.height 3)
    (hb : b<sha384PaddedLength n/128) (hj : j<128) :
    ((instructionBitExpr (8*j) 8).eval tr 3 b pub).toNat=
      (pad (sha384CommittedMessage n pub tr)).getD (128*b+j) 0 := by
  have position : 128*b+j<sha384PaddedLength n := by
    unfold sha384PaddedLength at hb ⊢;omega
  rw [sha384_padding_byte _ _ (by simpa only [sha384_committed_message_length] using position)]
  simp only [sha384_committed_message_length]
  by_cases data : 128*b+j<n
  · rw [ite_eq_left data,sha384_committed_message_byte n pub tr _ data]
    exact congrArg Fp.toNat (sha384_committed_pad_input_byte n fixed pub tr h bound b j hr hb hj data)
  · rw [ite_eq_right data]
    exact sha384_committed_pad_constant_nat n fixed pub tr h b j hr hb hj (by omega)

end NearCompression
