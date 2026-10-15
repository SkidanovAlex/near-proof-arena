import ZkFormal.NearV3.D1.R.Base
import ZkFormal.NearV3.Assembly.RcptCandidateIndexedBytes

/-!
# `ZkFormal.NearV3.D1.R.Delta.Body` — body offsets from `O0`, and the D1 sends

Lane `v3-d1-phase2`, item V4.  Trace-free facts about the D1 view definitions
(`D1/R/ViewDefs`):

* `bOffsG o0` is D0a's `bOffs` with the start `o0` instead of `8` (`bOffsG_add`);
* the extracted byte messages from body position `o0` are the D1 BYTES sends
  (`chainByteMsgs_eq_viewG`, D0a's `chainByteMsgs_eq_view` at `o0`);
* off `BYTES`, the D1 sends with `t0 = m0 = 0` are D0a's (`sends3G_eq`);
* the semantic body end (`flat_views_bodyG`).
-/

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof (ListBlock RS rcptOf)

theorem bOffsG_add (o0 : Nat) (xs : List RcptE) (r : Nat) : bOffsG o0 xs r + 8 = bOffs xs r + o0 := by
  unfold bOffsG bOffs; omega

theorem view_bOffsG (o0 : Nat) (tr : Trace Fp) (tt : Nat) (bs : List ListBlock)
    (j : Nat) (hj : j < bs.length) (k : Nat) (hk : k ≤ bs[j].receipts.length) :
    bOffsG o0 (flatR (bs.map (ListBlock.view tr tt))) (baseR (bs.map (ListBlock.view tr tt)) j + k) =
      o0 + ((bs.take j).map fun B => B.refundBytes tr tt).sum +
        ((bs[j].receipts.take k).map fun y => rfLen (rcptOf tr tt y)).sum := by
  have h1 := bOffsG_add o0 (flatR (bs.map (ListBlock.view tr tt))) (baseR (bs.map (ListBlock.view tr tt)) j + k)
  rw [view_bOffs tr tt bs j hj k hk] at h1
  omega

theorem blockByteMsgs_viewG (o0 t0 m0 : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (bs : List ListBlock) (j : Nat) (hj : j < bs.length) :
    blockByteMsgs tr tt pub bs[j] j (((bs.take j).map fun B => B.receipts.length).sum)
      (o0 + ((bs.take j).map fun B => B.refundBytes tr tt).sum) =
    emitAt (msgId K_RC j) 0 (hdrBytes pub ((bs.map (ListBlock.view tr tt)).getD j default)) ++
      (located (bs.map (ListBlock.view tr tt)) j).flatMap
        (fun (r, o, x) => rSendsG o0 t0 m0 pub (flatR (bs.map (ListBlock.view tr tt))) j r o x B_BYTES) := by
  have hget : (bs.map (ListBlock.view tr tt)).getD j default = bs[j].view tr tt := by
    rw [getD_eq_getElem' _ default (by simpa using hj), List.getElem_map]
  unfold blockByteMsgs located
  simp only [hget, ReceiptCandidateProof.ListBlock.view_length, List.flatMap_map]
  apply congrArg (List.append (emitAt (msgId K_RC j) 0 (hdrBytes pub (bs[j].view tr tt))))
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  unfold receiptByteMsgs
  rw [getD_eq_getElem' bs[j].receipts default hk]
  have hgetR : (bs[j].view tr tt).rs.getD k default = rcptOf tr tt bs[j].receipts[k] := by
    change (bs[j].receipts.map (rcptOf tr tt)).getD k default = _
    rw [getD_eq_getElem' _ default (by simpa using hk), List.getElem_map]
  rw [hgetR, view_lOffs]
  simp only [rSendsG, ite_true, rcptBytesV]
  rw [view_bOffsG o0 tr tt bs j hj k (by omega), view_baseR]

/-- The extracted byte messages from body position `o0` are the D1 BYTES sends. -/
theorem chainByteMsgs_eq_viewG (o0 t0 m0 : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (bs : List ListBlock) :
    chainByteMsgs tr tt pub bs 0 0 o0 = rcptSends3G o0 t0 m0 pub (bs.map (ListBlock.view tr tt)) B_BYTES := by
  rw [chainByteMsgs_indexed]
  simp only [rcptSends3G, List.length_map, show B_BYTES ≠ B_RCL by decide, ite_true, ite_false,
    List.append_nil, Nat.zero_add]
  apply flatMap_congr'
  intro j hj
  have hj := List.mem_range.mp hj
  rw [getD_eq_getElem' bs ⟨0, []⟩ hj]
  exact blockByteMsgs_viewG o0 t0 m0 tr tt pub bs j hj

theorem rSendsG_eq (o0 : Nat) (pub : List Fp) (xs : List RcptE) (j r o : Nat) (x : RcptE) {b : Nat}
    (hb : b ≠ B_BYTES) : rSendsG o0 0 0 pub xs j r o x b = rSends pub xs j r o x b := by
  simp only [rSendsG, rSends, if_neg hb, Nat.add_zero]

/-- Off `BYTES`, the sends with `t0 = m0 = 0` are D0a's. -/
theorem sends3G_eq (o0 : Nat) (pub : List Fp) (ls : RcptV3Vs) {b : Nat} (hb : b ≠ B_BYTES) :
    rcptSends3G o0 0 0 pub ls b = rcptSends3 pub ls b := by
  unfold rcptSends3G rcptSends3
  simp only [rSendsG_eq o0 pub _ _ _ _ _ hb]

theorem flat_views_bodyG (o0 : Nat) (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    bOffsG o0 (flatR (bs.map (ListBlock.view tr tt))) (flatR (bs.map (ListBlock.view tr tt))).length =
      o0 + (bs.map fun B => B.refundBytes tr tt).sum := by
  simp only [bOffsG, List.take_length]
  congr 1
  induction bs with
  | nil => simp [flatR]
  | cons B bs ih =>
    simp only [flatR, List.map_cons, List.flatMap_cons, List.map_append, List.sum_append] at ih ⊢
    rw [ih, List.sum_cons]
    congr 1
    simp [RcptV3Proof.ListBlock.view, RcptV3Proof.ListBlock.viewReceipts, List.map_map, Function.comp_def]
    rfl

end ZkFormal.NearV3.D1.RcptD1
