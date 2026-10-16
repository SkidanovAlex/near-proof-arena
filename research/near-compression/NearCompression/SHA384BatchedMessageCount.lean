import NearCompression.SHA384BatchedMessageRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

theorem sha384_batched_message_count_byte (message digest : List UInt8) (size : digest.length=48)
    (j : Nat) (hj : j<4) :
    (sha384BatchedPublic message digest).getD
      (message.length+52+64*(sha384PaddedLength message.length/128)+j) 0=
      Fp.ofNat ((sha384PaddedLength message.length/128)/256^j%256) := by
  let pre := (message++digest).map UInt8.toNat ++ [1,0,0,0] ++ sha384BatchPayload message
  let tail := sha384BatchIVPayload ++ [1,0,0,0]
  have layout : sha384BatchedPublic message digest=pre.map Fp.ofNat ++
      ((sha384BatchCountBytes (sha384PaddedLength message.length/128)).map Fp.ofNat ++ tail.map Fp.ofNat) := by
    simp only [sha384BatchedPublic,sha384BatchedPublicNat,pre,tail,List.map_append,List.append_assoc]
  have len : (pre.map Fp.ofNat).length=message.length+52+64*(sha384PaddedLength message.length/128) := by
    simp only [List.length_map,pre,List.length_append,List.length_map,size,sha384_batch_payload_length,
      List.length_cons,List.length_nil]
    omega
  rw [layout]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [len];omega :
      (pre.map Fp.ofNat).length≤message.length+52+64*(sha384PaddedLength message.length/128)+j),
    len,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp [sha384_batch_count_bytes_length];omega :
      j<((sha384BatchCountBytes (sha384PaddedLength message.length/128)).map Fp.ofNat).length)]
  simp only [sha384BatchCountBytes,List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some]

theorem sha384_batched_message_count_digit (message digest : List UInt8) (size : digest.length=48)
    (j : Nat) (hj : j<4) :
    ((sha384BatchedPublic message digest).getD
      (message.length+52+64*(sha384PaddedLength message.length/128)+j) 0).toNat=
      (sha384PaddedLength message.length/128)/256^j%256 := by
  rw [sha384_batched_message_count_byte message digest size j hj,Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have small : (sha384PaddedLength message.length/128)/256^j%256<256 := Nat.mod_lt _ (by decide)
  unfold P
  omega

/-- Four canonical base256 digits reconstruct any32bit natural count. -/
theorem sha384_batch_count_reconstruction (count : Nat) (bound : count<4294967296) :
    count%256+256*(count/256%256+256*(count/65536%256+256*(count/16777216%256)))=count := by
  omega

/-- The actual canonical public layout has precisely one record per block;
there is no caller-provided count or tag-uniqueness premise. -/
theorem sha384_batched_message_count (message digest : List UInt8) (size : digest.length=48)
    (bound : sha384PaddedLength message.length/128<P) :
    (sha384BatchMessageSegment message.length).count (sha384BatchedPublic message digest)=
      sha384PaddedLength message.length/128 := by
  have d0:=sha384_batched_message_count_digit message digest size 0 (by decide)
  have d1:=sha384_batched_message_count_digit message digest size 1 (by decide)
  have d2:=sha384_batched_message_count_digit message digest size 2 (by decide)
  have d3:=sha384_batched_message_count_digit message digest size 3 (by decide)
  simp only [PubSeg.count,sha384BatchMessageSegment,show List.range 4=[0,1,2,3] from rfl,
    List.map_cons,List.map_nil,leNat]
  have val (x : Fp) : PubVal.val x=x.toNat := rfl
  simp only [val]
  rw [d0,d1,d2,d3]
  simp only [Nat.pow_zero,Nat.div_one,Nat.pow_one,Nat.reducePow,Nat.mul_zero,Nat.add_zero]
  apply sha384_batch_count_reconstruction
  unfold P at bound
  omega

end NearCompression
