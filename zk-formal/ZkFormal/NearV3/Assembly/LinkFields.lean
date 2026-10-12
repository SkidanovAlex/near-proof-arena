import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges

/-!
# ZkFormal.NearV3.Assembly.LinkFields — view-level `GoodV3` fields from the records

Each lemma closes one field of `ExtFieldsV3` (`LinkCoreV3Stmt`) for the reconstruction whose
receipts are the receipt view's lists (`x.receipts = r.lists`).

* `receiptCount_of_records` — `h.n = x.applied.length`: the receipt view counts its receipts
  against the packed header's `n` (`RcptV3Wf.count`), which is the hint's `n` (`prepD0`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-- Public elements of a packed byte statement are bytes. -/
theorem pubNat_pubOf_lt (bs : List UInt8) (i : Nat) :
    ZkFormal.Near.pubNat (ZkFormal.Udr.pubOf Fp bs) i < 256 := by
  unfold ZkFormal.Near.pubNat
  rw [ZkFormal.NearV3.Public.pub_getD]
  change (Fp.ofNat (bs.getD i 0).toNat).toNat < 256
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by have := (bs.getD i 0).toNat_lt; unfold ZkFormal.Algebra.P; omega)]
  exact (bs.getD i 0).toNat_lt

/-- **`receiptCount`.** -/
theorem receiptCount_of_records {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat}
    {ls : ZkFormal.NearV3.RcptV3Vs} (hp : prepD0 cb h = .ok p)
    (hw : ZkFormal.NearV3.RcptV3Wf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls)
    (x : ExtV3) (hx : x.receipts = ls) :
    h.n = x.applied.length := by
  have hc := hw.count (fun i _ => pubNat_pubOf_lt _ _)
  rw [ZkFormal.NearV3.RcptV3Proof.prepared_receipt_count hp oh (prepD0_roots hp)] at hc
  obtain ⟨pc, -, hb⟩ := ZkFormal.NearV3.Sched.bind_ok hp
  have hn := (ZkFormal.NearV3.RcptV3Proof.prepBody_count_guard hb).1
  rw [← hn, ← hc]
  simp only [ExtV3.applied, hx, ZkFormal.NearV3.flatR, List.length_flatMap, List.length_map]

/-- **`pathDepth`** from source selection: every used proof is a checked source entry of the
dictionary (`SourceSemanticsV3.selected`), whose path is a source-proof block of `srcpV3`, and
those blocks have `≤ Dp0` items (`V3RecordsWf.srcpDepth`, A10 in the AIR). -/
theorem pathDepth_of_selected {k : WalkD0} {x : ExtV3}
    (hsel : ∀ b ∈ k.sourceBlks, ∀ s ci, (s, ci) ∈ b.slots → s.heightIncluded == b.hdr.height →
      ∃ e : SourceEntryV3, Sum.inl e ∈ x.dictionary ∧
        lookupLast (chunkHash s.inner ci.encodedMerkleRoot)
          (x.dictionary.map DictionaryEntryV3.entry) = some e.entry)
    (hD : ∀ e : SourceEntryV3, Sum.inl e ∈ x.dictionary → e.path.path.length ≤ Dp0) :
    ∀ e ∈ usedProofs k (stateWitnessOfV3 k x), e.proof.path.length ≤ Dp0 := by
  intro e he
  simp only [usedProofs, stateWitnessOfV3_entries, List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨b, hb, ⟨s, ci⟩, hs, hl⟩ := he
  split at hl
  · rename_i hh
    obtain ⟨e', he', hl'⟩ := hsel b hb s ci hs hh
    rw [hl'] at hl
    cases hl
    simpa [SourceEntryV3.entry] using hD e' he'
  · cases hl

end ZkFormal.NearV3.Assembly
