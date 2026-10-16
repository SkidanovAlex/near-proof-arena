import NearCompression.SHA384DirectRecords
import NearCompression.SHA384DirectPublicFit

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem sha384_direct_batched_iv_messages (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchIVSegment message.length).msgs (sha384BatchedPublic message digest)=
      sha384DirectIVSegment.msgs (sha384DirectPublic digest) := by
  have direct:=sha384_direct_segment_count digest size true
  change sha384DirectIVSegment.count (sha384DirectPublic digest)=1 at direct
  simp only [PubSeg.msgs,sha384_batched_iv_count message digest size,direct,
    show List.range 1=[0] from rfl,List.map_cons,List.map_nil,
    sha384_batched_iv_content message digest size,sha384_direct_iv_record digest size]

private theorem tagged_count (xs : List (List Fp)) (bus b : Nat) (side s : Bool) (message : List Fp) :
    ((xs.map (fun m=>(bus,side,m))).filter (fun x=>decide (x=(b,s,message)))).length=
      if bus=b ∧ side=s then xs.count message else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hb:bus=b <;> by_cases hs:side=s <;> by_cases hm:x=message <;>
      simp_all [List.count_cons]

/-- Full exact public-count substitution, including the dynamic block sends.
This closes the count premise of the structural direct-to-batched projection. -/
theorem sha384_direct_public_counts (n : Nat) (fixed : List (Nat × Nat))
    (digest : List UInt8) (size : digest.length=48) (tr : Trace Fp)
    (h : HoldsP (sha384DirectInputAir n fixed) (sha384DirectPublic digest) tr)
    (bound : sha384PaddedLength n/128<P) (bus : Nat) (side : Bool) (msg : List Fp) :
    pubCount (sha384BatchedAir n)
      (sha384BatchedPublic (sha384DirectMessageBytes n (sha384DirectPublic digest) tr) digest) bus side msg=
      tableBusCount (sha384DirectInputTable n fixed).interactions tr 2 (sha384DirectPublic digest) bus side msg+
      pubCount (sha384DirectInputAir n fixed) (sha384DirectPublic digest) bus side msg := by
  let message:=sha384DirectMessageBytes n (sha384DirectPublic digest) tr
  have length : message.length=n:=sha384_direct_message_bytes_length n _ tr
  have dg:=sha384_direct_batched_digest_messages message digest size
  have iv:=sha384_direct_batched_iv_messages message digest size
  rw [length] at dg iv
  have blocks:=sha384_direct_canonical_records n fixed (sha384DirectPublic digest) tr h digest size bound
  have oldLayout : (sha384BatchedAir n).pubSegs=
    [sha384BatchDigestSegment n,sha384BatchMessageSegment n,sha384BatchIVSegment n] := rfl
  have newLayout : (sha384DirectInputAir n fixed).pubSegs=
    [sha384DirectDigestSegment,sha384DirectIVSegment] := rfl
  rw [sha384_direct_input_count]
  unfold pubCount pubMsgs
  rw [oldLayout,newLayout]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [dg,iv,blocks]
  simp only [List.filter_append,List.length_append]
  simp only [tagged_count,sha384BatchDigestSegment,sha384DirectDigestSegment,
    sha384BatchIVSegment,sha384DirectIVSegment,sha384BatchMessageSegment]
  simp only [eq_comm (a:=true) (b:=side)]
  omega

end NearCompression
