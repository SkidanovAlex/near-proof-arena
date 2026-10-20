import NearCompression.SHA384BatchedMessageCount

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

theorem sha384_batch_message_bits (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block word bit : Nat) (hb : block<sha384PaddedLength n/128) (hw : word<16) (hi : bit<64) :
    (tr.cell 0 (80*block) (sha512ScheduleWindowBase word+bit)).toNat≤1 := by
  have pair:=sha384_batch_pair_holds n pub tr h bound block 0 hb (by decide)
  have schedule:=sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl pair
  have bits:=sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) word hw bit hi
  simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.add_zero,Nat.zero_add] using bits

/-- Canonical public input and actual bus balance determine each natural
sixteen-bit schedule limb, with no count or routing premise remaining. -/
theorem sha384_batch_trace_limb (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (block word limb : Nat) (hb : block<sha384PaddedLength message.length/128)
    (hw : word<16) (hl : limb<4) :
    ofBits (fun bit => (tr.cell 0 (80*block) (sha512ScheduleWindowBase word+16*limb+bit)).toNat) 16=
      sha384BatchMessageLimb message block word limb := by
  have countBound : (sha384BatchMessageSegment message.length).count (sha384BatchedPublic message digest)≤P := by
    rw [sha384_batched_message_count message digest size bound];omega
  have field:=sha384_batch_message_limb message.length _ tr h bound countBound block word limb hb hw hl
  have decoded:=sha512_public_limb_decode (tr.cell 0 (80*block)) _ (sha512ScheduleWindowBase word+16*limb)
    (fun bit hi => by
      have bits:=sha384_batch_message_bits message.length _ tr h bound block word (16*limb+bit) hb hw (by omega)
      simpa only [Nat.add_assoc] using bits) field
  have actual:=sha384_batched_public_limb_nat message digest size block word limb hb hw hl
  have index : message.length+52+block*64+(word*4+limb)=message.length+52+(block*64+word*4+limb) := by omega
  rw [index] at decoded
  exact decoded.1.symm.trans actual

/-- The low/high trace bytes in each received limb equal the corresponding
padded-message bytes; natural byte bounds make the split unique. -/
theorem sha384_batch_trace_limb_bytes (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (block word limb : Nat) (hb : block<sha384PaddedLength message.length/128)
    (hw : word<16) (hl : limb<4) :
    sha512WindowByte (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb)=
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+7-2*limb) 0 ∧
    sha512WindowByte (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb+1)=
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+6-2*limb) 0 := by
  have eq:=sha384_batch_trace_limb message digest size tr h bound block word limb hb hw hl
  rw [show 16=8+8 from rfl,ofBits_add] at eq
  have lo:=sha512_window_byte_bound (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb) (by omega)
    (fun bit hi => sha384_batch_message_bits message.length _ tr h bound block word bit hb hw hi)
  have hi:=sha512_window_byte_bound (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb+1) (by omega)
    (fun bit hi => sha384_batch_message_bits message.length _ tr h bound block word bit hb hw hi)
  have lowIndex : sha512ScheduleWindowBase word+8*(2*limb)=sha512ScheduleWindowBase word+16*limb := by omega
  have highIndex : sha512ScheduleWindowBase word+8*(2*limb+1)=sha512ScheduleWindowBase word+16*limb+8 := by omega
  have split : sha512WindowByte (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb)+
      256*sha512WindowByte (tr.cell 0 (80*block)) (sha512ScheduleWindowBase word) (2*limb+1)=
      sha384BatchMessageLimb message block word limb := by
    simpa only [sha512WindowByte,lowIndex,highIndex,Nat.add_assoc,Nat.reducePow] using eq
  have bytes:=sha384_batch_message_limb_bytes message block word limb
  omega

theorem sha384_batch_trace_byte (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (block j : Nat) (hb : block<sha384PaddedLength message.length/128) (hj : j<128) :
    sha512WindowByte (tr.cell 0 (80*block)) (sha512ScheduleWindowBase (j/8)) (7-j%8)=
      (pad (message.map UInt8.toNat)).getD (128*block+j) 0 := by
  have pair:=sha384_batch_trace_limb_bytes message digest size tr h bound block (j/8) ((7-j%8)/2)
    hb (by omega) (by omega)
  have cases : 7-j%8=2*((7-j%8)/2) ∨ 7-j%8=2*((7-j%8)/2)+1 := by omega
  rcases cases with low|high
  · have idx : 128*block+8*(j/8)+7-2*((7-j%8)/2)=128*block+j := by omega
    rw [idx,←low] at pair
    exact pair.1
  · have idx : 128*block+8*(j/8)+6-2*((7-j%8)/2)=128*block+j := by omega
    rw [←high,idx] at pair
    exact pair.2

/-- Full padded-block decoding from the canonical statement and actual AIR.
No separate count, operand, message or routing equality is supplied. -/
theorem sha384_batched_decoded_block (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (block : Nat) (hb : block<sha384PaddedLength message.length/128) :
    sha512DecodedBlock (tr.cell 0 (80*block))=
      ((pad (message.map UInt8.toNat)).drop (128*block)).take 128 := by
  have length:=sha384_padding_length (message.map UInt8.toNat)
  simp only [List.length_map] at length
  rw [sha384_multiblock_decoded_block_shape]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_take,List.length_drop,length]
    unfold sha384PaddedLength at hb ⊢
    omega
  · intro j hj hj'
    have jb : j<128 := by simpa using hj
    have pos : 128*block+j<sha384PaddedLength message.length := by
      unfold sha384PaddedLength at hb ⊢
      omega
    have actual:=sha384_batch_trace_byte message digest size tr h bound block j hb jb
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega),Option.getD_some] at actual
    simpa [Nat.add_comm] using actual

end NearCompression
