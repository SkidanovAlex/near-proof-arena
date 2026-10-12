import ZkFormal.NearV3.Render.HonestBalanceRcpt
import ZkFormal.NearV3.Assembly.RcptCanonicalGroupedEncoding
import ZkFormal.NearV3.Assembly.RcptCanonicalNativeEncoding
import ZkFormal.NearV3.Render.PaddedSrcp

/-!
# Honest RCL balance (`rcptV3` → `srcpV3`)

The honest receipt view's per-list encodings are the native `Receipt.encode` bytes
(`grouped_encodingsU`, the grouped-encoding identity on the unpatched trace), so `rcptV3`
announces `RCL (j, 12 + Σ |encode r|)` for every applied list `j`; `srcpV3` built from the
used source proofs of the same lists receives `RCL (j, |u64 toShard ++ encodeReceipts rs|)`.
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- The routing-q patch does not touch any byte field of the encoding. -/
theorem patch_enc (tr : Trace Fp) (y : RS) :
    (rcptOf (RoutingQCandidate.patchTrace tr 0) 0 y).enc = (rcptOf tr 0 y).enc := by
  simp only [RcptV.enc, rcptOf, patch_byte_slice]

section
variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)

include hw in
private theorem native_entities_encodingU (es pre : List EntityPlan)
    (he : entityPlans lists=pre++es) :
    (nativeEntities (pre.flatMap EntityPlan.rows).length es).map
      (decodedEncodingToken (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback))=
      es.map nativeEncodingToken := by
  induction es generalizing pre with
  | nil => rfl
  | cons p es ih =>
    simp only [nativeEntities,List.map_cons]
    have hei : entityPlans lists=(pre++[p])++es := by simpa only [List.append_assoc,List.singleton_append] using he
    have ht := ih (pre++[p]) hei
    simp only [List.flatMap_append,List.flatMap_singleton,List.length_append] at ht
    rw [ht]
    congr 1
    cases p with
    | header lp => rfl
    | receipt rp =>
      have hb : plannedRows lists=pre.flatMap EntityPlan.rows++plannedReceiptRows rp++es.flatMap EntityPlan.rows := by
        rw [←entityPlans_rows,he]
        simp only [List.flatMap_append,List.flatMap_cons,EntityPlan.rows,List.append_assoc]
      have hp : EntityPlan.receipt rp∈entityPlans lists := by rw [he];simp
      apply congrArg some
      have h := native_receipt_encoding own ctx lists log constants pub digests fallback headerFallback
        rp _ _ hb (entityPlans_receipt_wf lists hw rp hp)
      rw [patch_enc] at h
      exact h

include hw in
/-- Grouped native encodings on the plain (unpatched) honest trace. -/
theorem grouped_encodingsU (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    (bs.map (fun B=>(B.view (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0).rs.map (fun x=>x.enc)))=
      lists.map (fun xs=>xs.map (fun x=>x.receipt.encode.map UInt8.toNat)) := by
  have he := decoded_native_sequenceU own ctx lists log constants pub digests fallback headerFallback hw hh
    hL _ e (ListChain.decoded hc) (ReceiptCandidateProof.ListChain.end_padding hc).2
  have ht := congrArg (List.map (decodedEncodingToken
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback))) he
  rw [decoded_encoding_tokens] at ht
  have hn := native_entities_encodingU own ctx lists log constants pub digests fallback headerFallback hw
    (entityPlans lists) [] rfl
  simp only [List.flatMap_nil,List.length_nil] at hn
  rw [hn,native_encoding_tokens] at ht
  have hg := congrArg decodeGroups ht
  simpa only [decode_group_tokens] using hg
end

/-- The honest receipt view's per-list encodings are the native encodings. -/
theorem nativeRcptLists_enc (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    (nativeRcptLists pub x).map (fun L => L.rs.map (fun r => r.enc)) =
      x.lists.map (fun xs => xs.map (fun y => y.receipt.encode.map UInt8.toNat)) := by
  have hL := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL
  have h := grouped_encodingsU x.own x.ctx x.lists 22 _ pub _ _ _ ok.wf (by decide) hL bs e hc
  rw [native_chain pub x ok hc] at h
  rw [nativeRcptLists, List.map_map]
  exact h

theorem flatMap_singleton_map {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem rcl_sends (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_RCL = (List.range ls.length).map (fun j =>
      [j, 12 + ((ls.getD j default).rs.map (fun r => r.enc.length)).sum]) := by
  have hr : ∀ (xs : List RcptE) (j r o : Nat) (y : RcptE), rSends pub xs j r o y B_RCL = [] := by
    intro xs j r o y
    simp only [rSends, show B_RCL ≠ B_BYTES by decide, show B_RCL ≠ B_KEYNIB by decide,
      show B_RCL ≠ B_MEM by decide, show B_RCL ≠ B_RIDS by decide, show B_RCL ≠ B_MPOS by decide,
      show B_RCL ≠ B_SREC by decide, show B_RCL ≠ B_AKC by decide, show B_RCL ≠ B_BND by decide,
      ite_false]
  unfold rcptSends3
  simp only [show B_RCL ≠ B_BYTES by decide, ite_false, ite_true, List.nil_append, hr,
    ZkFormal.Near.flatMap_nil_fun, List.append_nil]
  rw [flatMap_singleton_map]
  apply List.map_congr_left
  intro j _
  simp [lOffs, List.take_length]

end ZkFormal.NearV3.Assembly.RcptSkeleton

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.RcptSkeleton

theorem srcp_rcl_recvs (xs : List SrcpGen.ProofInput) :
    (srcpTraffic (SrcpGen.blocksOfProofs xs)).recvs B_RCL = (List.ofFn fun i : Fin xs.length =>
      [i.val, (u64 xs[i].entry.proof.toShard ++ encodeReceipts xs[i].entry.receipts).length]) := by
  simp +decide [srcpTraffic, srcpBlockMsgs, srcpRootMsgs, srcpLeafMsgs, srcpItemMsgs,
    SrcpGen.blocksOfProofs, SrcpGen.blockOfProof]
  rw [flatMap_singleton_map, List.map_ofFn]
  rfl

theorem concatAll_length (l : List Bytes) : (concatAll l).length = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [concatAll, ih]

theorem encodeReceipts_length (rs : List Receipt) :
    (encodeReceipts rs).length = 4 + (rs.map (fun r => r.encode.length)).sum := by
  simp [encodeReceipts, u32, leN, concatAll_length, List.map_map, Function.comp_def]
  omega

/-- **RCL balances** between the honest receipt table and the honest source-proof table built
from the used source proofs of the same applied lists (`hxs`, in list order). -/
theorem honest_rcl_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    (xs : List SrcpGen.ProofInput)
    (hxs : xs.map (fun y => y.entry.receipts) = x.lists.map (List.map Input.receipt)) :
    (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_RCL =
      (srcpTraffic (SrcpGen.blocksOfProofs xs)).recvs B_RCL := by
  have he := nativeRcptLists_enc pub x ok
  have hl1 : (nativeRcptLists pub x).length = x.lists.length := by
    simpa using congrArg List.length he
  have hl2 : xs.length = x.lists.length := by simpa using congrArg List.length hxs
  show rcptSends3 pub (nativeRcptLists pub x) B_RCL = _
  rw [rcl_sends, srcp_rcl_recvs]
  apply List.ext_getElem
  · simp [hl1, hl2]
  · intro i h1 h2
    have hi1 : i < (nativeRcptLists pub x).length := by simpa using h1
    have hi : i < x.lists.length := by omega
    have hi2 : i < xs.length := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hg := congrArg (fun l => l[i]?) he
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi,
      Option.map_some, Option.some.injEq] at hg
    have hr := congrArg (fun l => l[i]?) hxs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi2, List.getElem?_eq_getElem hi,
      Option.map_some, Option.some.injEq] at hr
    have hs : ((nativeRcptLists pub x).getD i default).rs.map (fun r => r.enc.length) =
        (x.lists[i]).map (fun y => y.receipt.encode.length) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]
      have := congrArg (List.map List.length) hg
      simpa [List.map_map, Function.comp_def] using this
    simp only [Fin.getElem_fin]
    rw [hs, List.length_append, encodeReceipts_length, hr]
    simp [u64, leN, List.map_map, Function.comp_def]
    omega

end ZkFormal.NearV3.Render
