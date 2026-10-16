import NearCompression.SHA384BatchedPublicRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

private def ivPre (message digest : List UInt8) : List Nat :=
  (message++digest).map UInt8.toNat ++ [1,0,0,0] ++ sha384BatchPayload message ++
    sha384BatchCountBytes (sha384PaddedLength message.length/128)

private theorem iv_pre_length (message digest : List UInt8) (size : digest.length=48) :
    (ivPre message digest).length=message.length+56+64*(sha384PaddedLength message.length/128) := by
  simp only [ivPre,List.length_append,List.length_map,sha384_batch_payload_length,
    sha384_batch_count_bytes_length,size,List.length_cons,List.length_nil]
  omega

private theorem iv_layout (message digest : List UInt8) :
    sha384BatchedPublic message digest=
      (ivPre message digest).map Fp.ofNat ++
        (sha384BatchIVPayload.map Fp.ofNat ++ [1,0,0,0]) := by
  simp only [sha384BatchedPublic,sha384BatchedPublicNat,ivPre,List.map_append,List.append_assoc]
  rfl

theorem sha384_batched_iv_content (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchIVSegment message.length).record (sha384BatchedPublic message digest) 0=
      sha384BatchIVPayload.map Fp.ofNat := by
  simp only [PubSeg.record,PubSeg.startOffset,sha384BatchIVSegment,List.map_nil,List.nil_append,
    Nat.zero_mul,Nat.add_zero]
  apply List.ext_getElem
  · simp [sha384_batch_iv_payload_length]
  · intro i hi hi'
    have bound : i<32 := by simpa using hi
    simp only [List.getElem_map,List.getElem_range]
    rw [iv_layout]
    have preLen : ((ivPre message digest).map Fp.ofNat).length=
        message.length+56+64*(sha384PaddedLength message.length/128) := by
      simp only [List.length_map,iv_pre_length message digest size]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [preLen];omega :
      ((ivPre message digest).map Fp.ofNat).length≤message.length+56+64*(sha384PaddedLength message.length/128)+i),
      preLen,Nat.add_sub_cancel_left,List.getElem?_append_left (by simp [sha384_batch_iv_payload_length];omega :
        i<(sha384BatchIVPayload.map Fp.ofNat).length),List.getElem?_eq_getElem hi',Option.getD_some]
    simp only [List.getElem_map]

theorem sha384_batched_iv_count_byte (message digest : List UInt8) (size : digest.length=48)
    (i : Nat) (hi : i<4) :
    (sha384BatchedPublic message digest).getD
      (message.length+88+64*(sha384PaddedLength message.length/128)+i) 0=if i=0 then 1 else 0 := by
  rw [iv_layout,←List.append_assoc]
  have len : ((ivPre message digest).map Fp.ofNat ++ sha384BatchIVPayload.map Fp.ofNat).length=
      message.length+88+64*(sha384PaddedLength message.length/128) := by
    simp only [List.length_append,List.length_map,iv_pre_length message digest size,sha384_batch_iv_payload_length]
    omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [len];omega :
    ((ivPre message digest).map Fp.ofNat ++ sha384BatchIVPayload.map Fp.ofNat).length≤
      message.length+88+64*(sha384PaddedLength message.length/128)+i),len,Nat.add_sub_cancel_left]
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;> rfl

theorem sha384_batched_iv_count (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchIVSegment message.length).count (sha384BatchedPublic message digest)=1 := by
  have c0:=sha384_batched_iv_count_byte message digest size 0 (by decide)
  have c1:=sha384_batched_iv_count_byte message digest size 1 (by decide)
  have c2:=sha384_batched_iv_count_byte message digest size 2 (by decide)
  have c3:=sha384_batched_iv_count_byte message digest size 3 (by decide)
  simp only [PubSeg.count,sha384BatchIVSegment,show List.range 4=[0,1,2,3] from rfl,
    List.map_cons,List.map_nil,c0,c1,c2,c3,leNat]
  decide

/-- Canonical public expansion discharges both IV layout premises. -/
theorem sha384_batched_public_initial (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P) :
    sha512DecodedState (tr.cell 0 0)=sha384ChainIV :=
  sha384_batch_initial _ _ tr h bound (sha384_batched_iv_count message digest size)
    (sha384_batched_iv_content message digest size)

end NearCompression
