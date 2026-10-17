import NearCompression.SHA384DirectCounts
import NearCompression.SHA384DirectProjection

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

private theorem flat_length {A : Type} (n width : Nat) (f : Nat → List A)
    (shape : ∀ i,(f i).length=width) : ((List.range n).flatMap f).length=n*width := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.flatMap_append,ih,shape,Nat.succ_mul]

theorem sha384_direct_canonical_block (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (digest : List UInt8) (size : digest.length=48)
    (b : Nat) (hb : b<sha384PaddedLength n/128) :
    (sha384BatchMessageSegment n).record
      (sha384BatchedPublic (sha384DirectMessageBytes n pub tr) digest) b=
      Fp.ofNat b :: (List.range 16).flatMap (fun w=>(List.range 4).map (fun l=>
        (sha384DirectLimb n b w l).eval tr 2 0 pub)) := by
  simp only [PubSeg.record,PubSeg.startOffset,sha384BatchMessageSegment,List.map_cons,List.map_nil,
    List.singleton_append,List.nil_append,Nat.zero_add]
  apply congrArg (List.cons (Fp.ofNat b))
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
    exact (flat_length 16 4 _ (by intro w;simp)).symm
  · intro i hi hi'
    have bound : i<64 := by simpa using hi
    have w : i/4<16 := by omega
    have l : i%4<4 := Nat.mod_lt _ (by decide)
    have index : i/4*4+i%4=i := by omega
    have read:=sha384_flat_payload_index 16 4
      (fun w=>(List.range 4).map (fun l=>(sha384DirectLimb n b w l).eval tr 2 0 pub))
      (by intro w;simp) (i/4) (i%4) w l (0:Fp)
    rw [index] at read
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi',Option.getD_some] at read
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range l,Option.map_some,Option.getD_some] at read
    simp only [List.getElem_map,List.getElem_range]
    rw [read,sha384_direct_limb n pub tr b (i/4) (i%4) hb w l]
    rw [sha384_batched_public_field_lookup]
    have payload:=sha384_batched_public_payload_index (sha384DirectMessageBytes n pub tr) digest size b (i/4) (i%4)
      (by simpa only [sha384_direct_message_bytes_length] using hb) w l
    rw [sha384_direct_message_bytes_length] at payload
    have offset : n+52+(b*64+i/4*4+i%4)=n+52+b*64+i := by omega
    rw [offset] at payload
    rw [payload,sha384_direct_message_bytes_exact n fixed pub tr h]

/-- The complete direct send list equals the canonical public message list,
including order and multiplicity, rather than just matching membership. -/
theorem sha384_direct_canonical_records (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (digest : List UInt8) (size : digest.length=48) (bound : sha384PaddedLength n/128<P) :
    (sha384BatchMessageSegment n).msgs
      (sha384BatchedPublic (sha384DirectMessageBytes n pub tr) digest)=sha384DirectBlockRecords n pub tr := by
  have count:=sha384_batched_message_count (sha384DirectMessageBytes n pub tr) digest size
    (by simpa only [sha384_direct_message_bytes_length] using bound)
  rw [sha384_direct_message_bytes_length] at count
  unfold PubSeg.msgs
  rw [count]
  apply List.map_congr_left
  intro b hb
  exact sha384_direct_canonical_block n fixed pub tr h digest size b (List.mem_range.mp hb)

end NearCompression
