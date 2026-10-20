import NearCompression.SHA384DirectInput
import NearCompression.SHA384CommittedMessage

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Direct byte expressions evaluate to canonical padding of the actual input
row. No extra padding trace or byte-routing assumption is needed. -/
theorem sha384_direct_byte (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (i : Nat) (hi : i<sha384PaddedLength n) :
    (sha384DirectByte n i).eval tr 2 0 pub=
      Fp.ofNat ((pad (sha384CommittedMessage n pub tr)).getD i 0) := by
  rw [sha384_padding_byte _ i (by simpa only [sha384_committed_message_length] using hi)]
  simp only [sha384_committed_message_length]
  unfold sha384DirectByte
  by_cases data:i<n
  · rw [ite_eq_left data,ite_eq_left data,sha384_committed_message_byte n pub tr i data,Fp.ofNat_toNat]
  · rw [ite_eq_right data,ite_eq_right data]
    rfl

theorem sha384_direct_input_bits (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (r c : Nat) (hr : r<tr.height 2) (hc : c<8*n) :
    (tr.cell 2 r c).toNat≤1 := by
  have bit:=h.constr 2 (by simp [sha384DirectInputAir]) r hr (instructionBitConstraint c)
    (List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩))
  change tr.cell 2 r c*(tr.cell 2 r c+ -(1:Fp))=0 at bit
  have cases : tr.cell 2 r c=0 ∨ tr.cell 2 r c=1 := by grind
  rcases cases with z|z <;> rw [z] <;> decide

theorem sha384_direct_message_byte_bound (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (i : Nat) (hi : i<n) : (sha384CommittedMessage n pub tr).getD i 0<256 := by
  rw [sha384_committed_message_byte n pub tr i hi,sha384_committed_bitexpr_eval]
  exact instruction_bit_expr_bound _ 8 (8*i) (by decide)
    (fun k hk=>sha384_direct_input_bits n fixed pub tr h 0 (8*i+k) (Nat.two_pow_pos _) (by omega))

/-- All64 direct limb expressions have canonical padded-message content.
Booleanity is separately used to show the decoded input consists of bytes. -/
theorem sha384_direct_limb (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (b w l : Nat) (hb : b<sha384PaddedLength n/128) (hw : w<16) (hl : l<4) :
    (sha384DirectLimb n b w l).eval tr 2 0 pub=
      Fp.ofNat (256*(pad (sha384CommittedMessage n pub tr)).getD (128*b+8*w+6-2*l) 0+
        (pad (sha384CommittedMessage n pub tr)).getD (128*b+8*w+7-2*l) 0) := by
  have high : 128*b+8*w+6-2*l<sha384PaddedLength n := by unfold sha384PaddedLength at hb ⊢;omega
  have low : 128*b+8*w+7-2*l<sha384PaddedLength n := by unfold sha384PaddedLength at hb ⊢;omega
  change Fp.ofNat 256*(sha384DirectByte n (128*b+8*w+6-2*l)).eval tr 2 0 pub+
    (sha384DirectByte n (128*b+8*w+7-2*l)).eval tr 2 0 pub=_
  rw [sha384_direct_byte n pub tr _ high,sha384_direct_byte n pub tr _ low]
  have add (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := Lean.Grind.Semiring.natCast_add a b
  have mul (a b : Nat) : Fp.ofNat (a*b)=Fp.ofNat a*Fp.ofNat b := Lean.Grind.Semiring.natCast_mul a b
  rw [add,mul]

end NearCompression
