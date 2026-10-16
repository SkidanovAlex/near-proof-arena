import NearCompression.SHA384DirectPublic
import NearCompression.SHA384BatchedSoundness

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def sha384BatchDigestSegment (n : Nat) : PubSeg :=
  {bus:=3,send:=false,width:=48,countAt:=n+48,start:=n}

theorem sha384_direct_batched_digest_count (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchDigestSegment message.length).count (sha384BatchedPublic message digest)=1 := by
  have c0:=sha384_batched_digest_count_layout message digest size 0 (by decide)
  have c1:=sha384_batched_digest_count_layout message digest size 1 (by decide)
  have c2:=sha384_batched_digest_count_layout message digest size 2 (by decide)
  have c3:=sha384_batched_digest_count_layout message digest size 3 (by decide)
  simp only [PubSeg.count,sha384BatchDigestSegment,show List.range 4=[0,1,2,3] from rfl,
    List.map_cons,List.map_nil,c0,c1,c2,c3,leNat]
  decide

theorem sha384_direct_batched_digest_record (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchDigestSegment message.length).record (sha384BatchedPublic message digest) 0=
      sha384DirectDigestSegment.record (sha384DirectPublic digest) 0 := by
  rw [sha384_direct_digest_record digest size]
  have layout := congrArg (List.map Fp.ofNat) (sha384_batched_digest_layout message digest size)
  simp only [List.map_map,Function.comp_def,Fp.ofNat_toNat] at layout
  simpa only [PubSeg.record,PubSeg.startOffset,sha384BatchDigestSegment,List.map_nil,
    List.nil_append,Nat.zero_mul,Nat.add_zero] using layout

theorem sha384_direct_batched_digest_messages (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchDigestSegment message.length).msgs (sha384BatchedPublic message digest)=
      sha384DirectDigestSegment.msgs (sha384DirectPublic digest) := by
  have direct:=sha384_direct_segment_count digest size false
  change sha384DirectDigestSegment.count (sha384DirectPublic digest)=1 at direct
  simp only [PubSeg.msgs,sha384_direct_batched_digest_count message digest size,direct,
    show List.range 1=[0] from rfl,List.map_cons,List.map_nil,
    sha384_direct_batched_digest_record message digest size]

/-- The canonical statement has sufficient room for every digest, padded
block and IV record. The block bound also makes its four count bytes exact. -/
theorem sha384_direct_batched_public_fit (message digest : List UInt8) (size : digest.length=48)
    (bound : sha384PaddedLength message.length/128<P) :
    pubFit (sha384BatchedAir message.length) (sha384BatchedPublic message digest)=true := by
  have digestCount:=sha384_direct_batched_digest_count message digest size
  have blockCount:=sha384_batched_message_count message digest size bound
  have ivCount:=sha384_batched_iv_count message digest size
  have layout : (sha384BatchedAir message.length).pubSegs=
      [sha384BatchDigestSegment message.length,sha384BatchMessageSegment message.length,
       sha384BatchIVSegment message.length] := rfl
  unfold pubFit
  rw [layout]
  simp only [List.all_cons,List.all_nil]
  simp only [PubSeg.fits,Bool.and_eq_true,decide_eq_true_eq]
  rw [digestCount,blockCount,ivCount]
  simp only [sha384_batched_public_length message digest size,
    PubSeg.startOffset,sha384BatchDigestSegment,sha384BatchMessageSegment,sha384BatchIVSegment,
    sha384BatchedAir,Nat.one_mul]
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,True.intro⟩

end NearCompression
