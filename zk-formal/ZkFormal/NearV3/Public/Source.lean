import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Rcpt.Ids
import NearSpecV3.PrepD0
import ZkFormal.NearV3.Public.SourceDefs

/-! Claim-derived receipt source records, in applied order. Equal-key root
consistency is a separate semantic obligation of prepared-statement assembly. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

theorem sourcePayload_length (sources : List SrcList) :
    (sourcePayload sources).length = sources.length := by simp [sourcePayload]

theorem sourcePayload_getD (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    (sourcePayload sources).getD j [] = sourceRow sources j := by
  rw [← List.getElem_eq_getD (h := (show j < (sourcePayload sources).length by
    rw [sourcePayload_length]; exact hj)) []]
  simp only [sourcePayload,List.getElem_map,List.getElem_range]

theorem sourcePayload_width (sources : List SrcList)
    (hr : ∀ s ∈ sources, s.root.length = 32) :
    ∀ row ∈ sourcePayload sources, row.length = sourcePlan.width := by
  intro row hrow
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
  have hj := List.mem_range.mp hj
  have hroot := hr sources[j] (List.getElem_mem hj)
  unfold sourceRow
  rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
  simpa [sourcePlan] using hroot

theorem source_record (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    recordValues sourcePlan j ((sourcePayload sources).getD j []) =
      [Fp.ofNat j, Fp.ofNat (sourceDupByte sources j),
        Fp.ofNat (if sourceRep sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [sourcePayload_getD sources hj]
  unfold recordValues sourcePlan sourceRow
  unfold sourceDupByte
  cases sourceDup sources j <;> cases sourceConsistent sources j <;> cases sourceRep sources j <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_add,List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append] <;> rfl

theorem descriptor_source_record (header : ByteString) (blocks : List Payload)
    (sources : List SrcList) {i j : Nat} (hi : i < blocks.length)
    (hb : blocks.getD i [] = sourcePayload sources) (hj : j < sources.length)
    (hr : ∀ s ∈ sources, s.root.length = 32)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor sourcePlan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      [Fp.ofNat j, Fp.ofNat (sourceDupByte sources j),
        Fp.ofNat (if sourceRep sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [descriptor_record sourcePlan header blocks hi
    (by rw [hb,sourcePayload_length]; exact hj)
    (by rw [hb]; exact sourcePayload_width sources hr) ho,hb]
  exact source_record sources hj

end ZkFormal.NearV3.Public
