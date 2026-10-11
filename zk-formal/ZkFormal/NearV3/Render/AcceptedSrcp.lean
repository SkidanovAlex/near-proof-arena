import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Render.HonestBalanceSrc

/-!
# The honest `srcpV3` inputs of an accepted witness

One proof input per prepared source occurrence, in prepared (applied) order: the prepared
root, the prepared duplicate flag and the witness entry selected for the occurrence's key
(`sourceEntry`, last wins).  These satisfy the RCL and SRC alignment premises with the honest
receipt input (`acceptedSrcp_rcl`, `acceptedSrcp_src`), so `honest_rcl_balance` and
`honest_src_balance` hold for the accepted witness without further hypotheses.
-/

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra
open ZkFormal.NearV3.Assembly.RcptSkeleton ZkFormal.NearV3.Rcpt.Candidates

/-- The honest source-proof inputs. -/
def acceptedSrcpInputs (p : Prep) (w : StateWitness) : List SrcpGen.ProofInput :=
  (List.range p.lists.length).map fun j =>
    ⟨(p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j,
     sourceEntry w.entries (p.lists.getD j ⟨[], 0, []⟩)⟩

theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun j => f (l.getD j d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

/-- The RCL alignment premise: the srcp inputs carry the honest receipt lists in order. -/
theorem acceptedSrcp_rcl (p : Prep) (w : StateWitness) (ctx : ApplyCtx) :
    (acceptedSrcpInputs p w).map (fun y => y.entry.receipts) =
      (sourceInputLists ctx p.lists w.entries).map (List.map Input.receipt) := by
  rw [sourceInputLists_receipts, acceptedSrcpInputs, List.map_map]
  exact map_range_getD p.lists ⟨[], 0, []⟩ (fun s => (sourceEntry w.entries s).receipts)

/-- The SRC alignment premise: the srcp inputs carry the prepared roots and duplicate flags. -/
theorem acceptedSrcp_src (p : Prep) (w : StateWitness) :
    (acceptedSrcpInputs p w).map (fun y => (y.root, y.dup)) = (List.range p.lists.length).map
      (fun j => ((p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j)) := by
  simp [acceptedSrcpInputs, List.map_map, Function.comp_def]

/-- **RCL balances for an accepted witness** (no alignment hypothesis left). -/
theorem accepted_rcl_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    (hx : x.lists = sourceInputLists x.ctx x.p.lists x.w.entries) :
    (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_RCL =
      (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs x.p x.w))).recvs B_RCL :=
  honest_rcl_balance pub x ok _ (by rw [hx]; exact acceptedSrcp_rcl x.p x.w x.ctx)

/-- **SRC balances for an accepted witness** against the prepared source segment. -/
theorem accepted_src_balance (p : Prep) (w : StateWitness) :
    (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w))).recvs B_SRC =
      ZkFormal.NearV3.Public.preparedOn p B_SRC true :=
  honest_src_balance p _ (acceptedSrcp_src p w)

end ZkFormal.NearV3.Render
