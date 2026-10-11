import ZkFormal.NearV3.Render.HonestBalanceRcl
import ZkFormal.NearV3.Public.ReceiptIndex

/-!
# Honest SRC balance (prepared public segment → `srcpV3`)

The prepared statement's source segment sends `sourceRecords p` = `[j, dup_j] ++ root_j` per
applied list (`Public.prepared_source_records`); the honest `srcpV3` built from the used
source proofs with those roots and duplicate flags receives exactly these messages.
-/

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.RcptSkeleton

theorem srcp_src_recvs (xs : List SrcpGen.ProofInput) :
    (srcpTraffic (SrcpGen.blocksOfProofs xs)).recvs B_SRC = (List.ofFn fun i : Fin xs.length =>
      [i.val, if xs[i].dup then 1 else 0] ++ xs[i].root.map UInt8.toNat) := by
  simp +decide [srcpTraffic, srcpBlockMsgs, srcpRootMsgs, srcpLeafMsgs, srcpItemMsgs,
    SrcpGen.blocksOfProofs, SrcpGen.blockOfProof]
  rw [flatMap_singleton_map, List.map_ofFn]
  rfl

/-- **SRC balances**: the honest source-proof table receives exactly the prepared statement's
source records, when its inputs carry the prepared roots and duplicate flags in list order. -/
theorem honest_src_balance (p : Prep) (xs : List SrcpGen.ProofInput)
    (hsrc : xs.map (fun y => (y.root, y.dup)) = (List.range p.lists.length).map
      (fun j => ((p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j))) :
    (srcpTraffic (SrcpGen.blocksOfProofs xs)).recvs B_SRC =
      ZkFormal.NearV3.Public.preparedOn p B_SRC true := by
  rw [ZkFormal.NearV3.Public.prepared_source_records, srcp_src_recvs]
  have hl : xs.length = p.lists.length := by simpa using congrArg List.length hsrc
  apply List.ext_getElem
  · simp [ZkFormal.NearV3.Public.sourceRecords, hl]
  · intro i h1 h2
    have hi : i < xs.length := by simpa using h1
    have hi' : i < p.lists.length := by omega
    have hg := congrArg (fun l => l[i]?) hsrc
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_range hi',
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg
    simp only [List.getElem_ofFn, ZkFormal.NearV3.Public.sourceRecords, List.getElem_map,
      List.getElem_range]
    simp only [Fin.getElem_fin]
    simp only [hg.1, hg.2]

end ZkFormal.NearV3.Render
