import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Rcpt.Ids
import ZkFormal.NearV3.Public.BoundaryDefs

/-! Routing boundary records at positions 0 through 64, including end sentinels. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

theorem boundaryPayload_length (bounds : List Interval) :
    (boundaryPayload bounds).length = BND_STRIDE*bounds.length := by simp [boundaryPayload]

theorem boundaryPayload_width (bounds : List Interval) :
    ∀ row ∈ boundaryPayload bounds, row.length = boundaryPlan.width := by
  intro row hr
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
  rfl

theorem boundaryPayload_getD (bounds : List Interval) {x : Nat}
    (hx : x < BND_STRIDE*bounds.length) :
    (boundaryPayload bounds).getD x [] = boundaryRow bounds x := by
  rw [← List.getElem_eq_getD (h := (show x < (boundaryPayload bounds).length by
    rw [boundaryPayload_length]; exact hx)) []]
  simp only [boundaryPayload,List.getElem_map,List.getElem_range]

theorem boundary_record (bounds : List Interval) {x : Nat} (hx : x < BND_STRIDE*bounds.length) :
    recordValues boundaryPlan x ((boundaryPayload bounds).getD x []) =
      [Fp.ofNat x] ++ (boundaryRow bounds x).map byteF := by
  rw [boundaryPayload_getD bounds hx]
  simp only [recordValues,boundaryPlan,Nat.zero_add,List.map_nil,List.nil_append]
  rfl

theorem descriptor_boundary_record (header : ByteString) (blocks : List Payload)
    (bounds : List Interval) {i x : Nat} (hi : i < blocks.length)
    (hb : blocks.getD i [] = boundaryPayload bounds) (hx : x < BND_STRIDE*bounds.length)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor boundaryPlan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) x =
      [Fp.ofNat x] ++ (boundaryRow bounds x).map byteF := by
  rw [descriptor_record boundaryPlan header blocks hi
    (by rw [hb,boundaryPayload_length]; exact hx)
    (by rw [hb]; exact boundaryPayload_width bounds) ho,hb]
  exact boundary_record bounds hx

end ZkFormal.NearV3.Public
