import NearCompression.SHA384BatchedPayloadIndex

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.SHA512

/-- The fallback is also a byte, so this bound covers every natural index. -/
theorem sha384_batch_padded_byte_bound (message : List UInt8) (i : Nat) :
    (pad (message.map UInt8.toNat)).getD i 0<256 := by
  by_cases hi : i<(pad (message.map UInt8.toNat)).length
  · have member (v : Nat) (hv : v ∈ pad (message.map UInt8.toNat)) : v<256 := by
      simp only [pad,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at hv
      rcases hv with ((hv | hv) | hv) | hv
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact x.toNat_lt
      · subst v;decide
      · rcases hv with ⟨_,rfl⟩;decide
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact x.toNat_lt
    have value := member _ (List.getElem_mem hi)
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hi] using value
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (pad (message.map UInt8.toNat)).length≤i)]

def sha384BatchMessageLimb (message : List UInt8) (block word limb : Nat) : Nat :=
  256*(pad (message.map UInt8.toNat)).getD (128*block+8*word+6-2*limb) 0+
    (pad (message.map UInt8.toNat)).getD (128*block+8*word+7-2*limb) 0

theorem sha384_batch_message_limb_bound (message : List UInt8) (block word limb : Nat) :
    sha384BatchMessageLimb message block word limb<65536 := by
  have high:=sha384_batch_padded_byte_bound message (128*block+8*word+6-2*limb)
  have low:=sha384_batch_padded_byte_bound message (128*block+8*word+7-2*limb)
  unfold sha384BatchMessageLimb
  omega

/-- Mapping the public tape into Fp preserves each lookup, including fallback. -/
theorem sha384_batched_public_field_lookup (message digest : List UInt8) (i : Nat) :
    (sha384BatchedPublic message digest).getD i 0=
      Fp.ofNat ((sha384BatchedPublicNat message digest).getD i 0) := by
  simp only [sha384BatchedPublic,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (sha384BatchedPublicNat message digest)[i]? <;> rfl

/-- The public field element decodes to the exact 16-bit padded-message limb;
no reduction modulo the field can change its value. -/
theorem sha384_batched_public_limb_nat (message digest : List UInt8)
    (size : digest.length=48) (block word limb : Nat)
    (hb : block<sha384PaddedLength message.length/128) (hw : word<16) (hl : limb<4) :
    ((sha384BatchedPublic message digest).getD
      (message.length+52+(block*64+word*4+limb)) 0).toNat=
      sha384BatchMessageLimb message block word limb := by
  rw [sha384_batched_public_field_lookup,
    sha384_batched_public_payload_index message digest size block word limb hb hw hl]
  change (Fp.ofNat (sha384BatchMessageLimb message block word limb)).toNat=_
  rw [Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have small:=sha384_batch_message_limb_bound message block word limb
  unfold P
  omega

/-- Splitting each bounded payload limb recovers its two original message
bytes in big-endian order, despite the little-endian order of the limbs. -/
theorem sha384_batch_message_limb_bytes (message : List UInt8) (block word limb : Nat) :
    sha384BatchMessageLimb message block word limb/256=
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+6-2*limb) 0 ∧
    sha384BatchMessageLimb message block word limb%256=
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+7-2*limb) 0 := by
  have low:=sha384_batch_padded_byte_bound message (128*block+8*word+7-2*limb)
  unfold sha384BatchMessageLimb
  omega

end NearCompression
