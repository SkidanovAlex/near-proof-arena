import NearCompression.SHA384DirectInput
import NearCompression.SHA384BatchedIVLayout

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def sha384DirectPublic (digest : List UInt8) : List Fp :=
  digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0] ++
    sha384BatchIVPayload.map Fp.ofNat ++ [1,0,0,0]

def sha384DirectDigestSegment : PubSeg :=
  {bus:=3,send:=false,width:=48,countAt:=48,start:=0}

def sha384DirectIVSegment : PubSeg :=
  {bus:=5,send:=true,width:=32,countAt:=84,start:=52}

theorem sha384_direct_public_length (digest : List UInt8) (size : digest.length=48) :
    (sha384DirectPublic digest).length=88 := by
  simp [sha384DirectPublic,sha384_batch_iv_payload_length,size]

theorem sha384_direct_public_digest_byte (digest : List UInt8) (size : digest.length=48)
    (i : Nat) (hi : i<48) :
    (sha384DirectPublic digest).getD i 0=Fp.ofNat (digest.getD i 0).toNat := by
  unfold sha384DirectPublic
  rw [List.append_assoc,List.append_assoc]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa [size] using hi :
    i<(digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat)).length)]
  simp [List.getElem?_map,List.getElem?_eq_getElem (by omega : i<digest.length)]

private theorem suffix_layout (digest : List UInt8) :
    sha384DirectPublic digest=(digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0]) ++
      (sha384BatchIVPayload.map Fp.ofNat ++ [1,0,0,0]) := by
  simp only [sha384DirectPublic,List.append_assoc]

theorem sha384_direct_public_iv_byte (digest : List UInt8) (size : digest.length=48)
    (i : Nat) (hi : i<32) :
    (sha384DirectPublic digest).getD (52+i) 0=(sha384BatchIVPayload.map Fp.ofNat).getD i 0 := by
  rw [suffix_layout]
  have len : (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0]).length=52 := by simp [size]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [len];omega :
    (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0]).length≤52+i),len,Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa [sha384_batch_iv_payload_length] using hi :
      i<(sha384BatchIVPayload.map Fp.ofNat).length)]

theorem sha384_direct_public_count_byte (digest : List UInt8) (size : digest.length=48)
    (iv : Bool) (i : Nat) (hi : i<4) :
    (sha384DirectPublic digest).getD ((if iv then 84 else 48)+i) 0=if i=0 then 1 else 0 := by
  cases iv
  · unfold sha384DirectPublic
    rw [List.append_assoc,List.append_assoc]
    have len : (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat)).length=48 := by simp [size]
    simp only [Bool.false_eq_true,ite_false,List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [len];omega : (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat)).length≤48+i),
      len,Nat.add_sub_cancel_left,List.getElem?_append_left (by simpa using hi : i<([1,0,0,0]:List Fp).length)]
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl <;> rfl
  · unfold sha384DirectPublic
    have len : (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0] ++ sha384BatchIVPayload.map Fp.ofNat).length=84 := by
      simp [size,sha384_batch_iv_payload_length]
    simp only [ite_true,List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [len];omega :
      (digest.map (fun (b : UInt8)=>Fp.ofNat b.toNat) ++ [1,0,0,0] ++ sha384BatchIVPayload.map Fp.ofNat).length≤84+i),len,Nat.add_sub_cancel_left]
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl <;> rfl

theorem sha384_direct_segment_count (digest : List UInt8) (size : digest.length=48) (iv : Bool) :
    (if iv then sha384DirectIVSegment else sha384DirectDigestSegment).count (sha384DirectPublic digest)=1 := by
  have c0:=sha384_direct_public_count_byte digest size iv 0 (by decide)
  have c1:=sha384_direct_public_count_byte digest size iv 1 (by decide)
  have c2:=sha384_direct_public_count_byte digest size iv 2 (by decide)
  have c3:=sha384_direct_public_count_byte digest size iv 3 (by decide)
  cases iv <;> simp only [ite_true,ite_false,Bool.false_eq_true] at *
  all_goals simp only [PubSeg.count,sha384DirectIVSegment,sha384DirectDigestSegment,
    show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,c0,c1,c2,c3,leNat]
  all_goals decide

theorem sha384_direct_digest_record (digest : List UInt8) (size : digest.length=48) :
    sha384DirectDigestSegment.record (sha384DirectPublic digest) 0=
      digest.map (fun b=>Fp.ofNat b.toNat) := by
  simp only [PubSeg.record,PubSeg.startOffset,sha384DirectDigestSegment,List.map_nil,
    List.nil_append,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
  apply List.ext_getElem
  · simp [size]
  · intro i hi hi'
    have bound : i<48 := by simpa using hi
    simp only [List.getElem_map,List.getElem_range]
    rw [sha384_direct_public_digest_byte digest size i bound]
    simp [List.getD,List.getElem?_eq_getElem (by omega : i<digest.length)]

theorem sha384_direct_iv_record (digest : List UInt8) (size : digest.length=48) :
    sha384DirectIVSegment.record (sha384DirectPublic digest) 0=
      sha384BatchIVPayload.map Fp.ofNat := by
  simp only [PubSeg.record,PubSeg.startOffset,sha384DirectIVSegment,List.map_nil,
    List.nil_append,Nat.zero_mul,Nat.add_zero]
  apply List.ext_getElem
  · simp [sha384_batch_iv_payload_length]
  · intro i hi hi'
    have bound : i<32 := by simpa using hi
    simp only [List.getElem_map,List.getElem_range]
    rw [sha384_direct_public_iv_byte digest size i bound]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi',Option.getD_some,List.getElem_map]

theorem sha384_direct_batched_iv_record (message digest : List UInt8) (size : digest.length=48) :
    sha384DirectIVSegment.record (sha384DirectPublic digest) 0=
      (sha384BatchIVSegment message.length).record (sha384BatchedPublic message digest) 0 := by
  rw [sha384_direct_iv_record digest size,sha384_batched_iv_content message digest size]

end NearCompression
