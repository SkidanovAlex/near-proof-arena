import ZkFormal.NearV3.Render.HonestBalanceRcl
import ZkFormal.NearV3.Public.ReceiptIndex
import ZkFormal.NearV3.Render.PaddedSrcpDD
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Rcpt.Candidates.PreparedVerified
import ZkFormal.NearV3.Rcpt.Candidates.DedupActualTraffic

/-!
# Honest SRC balance (prepared public segment → table 20, `SrcpDD`)

The prepared statement's source segment sends `sourceRecords p` = `[j, dup byte_j, rep_j] ++ root_j`
per applied list (`Public.prepared_source_records`, `SRC34`).  The honest dedup source table built
from the prepared sources (`DedupCompile.blocks`, repetition bits `sourceRepeated`) receives
`[j, dup_j, rep_j] ++ root_j`; the two agree when every later occurrence of a key has the
earlier occurrence's metadata (`sourceConsistent`, implied by `sourceMetadataConsistent`, which an
accepted witness has: `relD0a_prepared_metadata`).
-/

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.RcptSkeleton ZkFormal.NearV3.Rcpt.Candidates

theorem dd_src_recvs (bs : List SrcpB) (rep : Nat → Bool) :
    (DedupRender.traffic bs rep).recvs B_SRC = (List.range bs.length).map fun i =>
      [(bs.getD i default).j, (bs.getD i default).dup.toNat, (rep i).toNat] ++ (bs.getD i default).root := by
  simp only [DedupRender.traffic, show B_SRC ≠ B_SIZE by decide, ite_false, DedupRender.sourceMsgs]
  rw [← flatMap_singleton_map]
  apply ZkFormal.Near.Link.flatMap_congr'
  intro i _
  cases hd : (bs.getD i default).dup <;>
    (have hd' := hd; rw [List.getD_eq_getElem?_getD] at hd';
     simp [DedupRender.blockMsgs, DedupRender.rootMsgs, srcpLeafMsgs, srcpItemMsgs, hd', B_SRC, B_BYTES,
      B_DIGEST, B_RCL, List.getD_eq_getElem?_getD])

/-- Metadata consistency makes every occurrence consistent with the earlier ones. -/
theorem sourceConsistent_of_metadata (sources : List SrcList)
    (h : sourceMetadataConsistent sources = true) {j : Nat} (hj : j < sources.length) :
    ZkFormal.NearV3.Public.sourceConsistent sources j = true := by
  simp only [sourceMetadataConsistent, List.all_eq_true] at h
  unfold ZkFormal.NearV3.Public.sourceConsistent
  rw [List.all_eq_true]
  intro s hs
  have ht : sources.getD j ⟨[],0,[]⟩ ∈ sources := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  exact h s (List.mem_of_mem_take hs) _ ht

/-- The public `dup` byte of a consistent source is its `dup` bit. -/
theorem dupByte_eq (sources : List SrcList) (h : sourceMetadataConsistent sources = true)
    {j : Nat} (hj : j < sources.length) :
    ZkFormal.NearV3.Public.sourceDupByte sources j = (ZkFormal.NearV3.Public.sourceDup sources j).toNat := by
  unfold ZkFormal.NearV3.Public.sourceDupByte
  rw [sourceConsistent_of_metadata sources h hj]
  cases ZkFormal.NearV3.Public.sourceDup sources j <;> rfl

/-- **SRC balances** for the honest dedup blocks of consistent prepared sources. -/
theorem honest_src_balance_dd (p : Prep) (entries : List ProofEntry)
    (hm : sourceMetadataConsistent p.lists = true) :
    (DedupRender.traffic (DedupCompile.blocks p.lists entries) (sourceRepeated p.lists)).recvs B_SRC =
      ZkFormal.NearV3.Public.preparedOn p B_SRC true := by
  rw [ZkFormal.NearV3.Public.prepared_source_records, dd_src_recvs, DedupCompile.blocks_length]
  unfold ZkFormal.NearV3.Public.sourceRecords
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  have hg : (DedupCompile.blocks p.lists entries).getD j default = DedupCompile.block p.lists entries j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [DedupCompile.blocks_length] using hj),
      Option.getD_some]
    simp [DedupCompile.blocks]
  have hr : (if ZkFormal.NearV3.Public.sourceRep p.lists j = true then 1 else 0) =
      (sourceRepeated p.lists j).toNat := by
    show (if sourceRepeated p.lists j = true then 1 else 0) = _
    cases sourceRepeated p.lists j <;> rfl
  rw [hg, dupByte_eq p.lists hm hj, hr]
  rfl

end ZkFormal.NearV3.Render
