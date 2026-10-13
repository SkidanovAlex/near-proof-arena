import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Assembly.QueueGlobalBalance
import ZkFormal.NearV3.Assembly.QueueShardBalance
import ZkFormal.NearV3.Render.PaddedRcpt
import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Render.PaddedRcptR
import ZkFormal.NearV3.Candidates.NativeReceiptIdBytes

/-!
# Honest bus balance on the receipt-side buses (trace-free, over the renders' native lists)

Each lemma states that the honest renders' traffic functions balance on one bus, as a
permutation of message lists, over the same native inputs the renders take.

* `QVC` (queue-value provider counters; used only by `qvV3`): `qvNative_qvc_balance`;
* `QSH` (shard bytes and counts; used only by `qvV3`): `qvNative_qsh_balance`;
* `SIZE` (`nodeV3`, `valV3`, `srcpV3` → `sizeV3`): `honest_size_balance` with `honestSizeV`;
* `RIDS` (`rcptV3` → `sortV3`): `honest_rids_balance` — the honest receipt views carry the
  native receipt ids (`located_idsU`), so their sends are the native sort input's receives.
-/

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.NearV3.Assembly

/-- **QVC balances on the honest `qvV3` traffic**: every provider counter opened by a record
at `0` is advanced by its reads and closed at its user count (`plan_qvc_balance`). -/
theorem qvNative_qvc_balance {pre : NearSpec.PTrie} {v : MainValues} (pres : List NearSpec.PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    ((qvNativeTraffic pre v pres).sends ValueTable.B_QVC).Perm
      ((qvNativeTraffic pre v pres).recvs ValueTable.B_QVC) := by
  have hb := plan_qvc_balance pres hh
  simp only at hb
  rw [← ZkFormal.NearV3.Candidates.NativeQueueCounters.resolve_eq] at hb
  have hk : ValueTable.B_QVC ≠ B_KEYNIB := by decide
  have hvb : ValueTable.B_QVC ≠ B_VBYTES := by decide
  have hw : ∀ sd, (fun w : Walk => w.repairedWordMessages ValueTable.B_QVC sd) =
      (fun w => w.counterWordMessages sd) := by
    intro sd; funext w
    simp [Walk.repairedWordMessages, Walk.wordMessages, hk]
  have hrec : ∀ (f : ValueGen.Record → List Nat) (g : QueueProvider → List Nat),
      (∀ p, f (queueRecord p) = g p) → ∀ ps : List QueueProvider, (queueRecords ps).map f = ps.map g := by
    intro f g h ps
    simp only [queueRecords, List.map_map]
    exact List.map_congr_left (fun p _ => h p)
  simp only [qvNativeTraffic, repairedTraffic, qvNativeWalks, qvNativeRecords, ValueGen.canonicalTraffic,
    hw, hvb, ite_false, ite_true]
  rw [hrec (fun v => [v.vid, v.tau, v.mode, 0]) (fun p => queueCounterMsg p 0) (fun p => rfl),
    hrec (fun v => [v.vid, v.tau, v.mode, v.users]) (fun p => queueCounterMsg p p.users) (fun p => rfl)]
  exact hb

/-- **QSH balances on the honest `qvV3` traffic** (`plan_qsh_balance`): record shard bytes and
buffered counts are exactly the walks' shard words. -/
theorem qvNative_qsh_balance {pre : NearSpec.PTrie} {v : MainValues} (pres : List NearSpec.PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    ((qvNativeTraffic pre v pres).sends B_QSH).Perm ((qvNativeTraffic pre v pres).recvs B_QSH) := by
  have hb := plan_qsh_balance pres (ZkFormal.NearV3.Candidates.NativeQueueIds.resolve pre v pres) hh
  simp only at hb
  have hk : B_QSH ≠ B_KEYNIB := by decide
  have hq : B_QSH ≠ ValueTable.B_QVC := by decide
  have hv : B_QSH ≠ B_VBYTES := by decide
  have hf : B_QSH ≠ B_FINAL := by decide
  have hs : (fun w : Walk => w.repairedWordMessages B_QSH true) = (fun _ => []) := by
    funext w; simp [Walk.repairedWordMessages, Walk.wordMessages, hk, hq]
  have hr : (fun w : Walk => w.repairedWordMessages B_QSH false) = (fun w => w.shardWordMessages) := by
    funext w; simp [Walk.repairedWordMessages, Walk.wordMessages, hq, hf]
  simp only [qvNativeTraffic, repairedTraffic, qvNativeWalks, qvNativeRecords, ValueGen.canonicalTraffic,
    hs, hr, hv, hq, ite_false, ite_true, List.append_nil]
  have h0 : (plan pre v pres (ZkFormal.NearV3.Candidates.NativeQueueIds.resolve pre v pres)).flatMap
      (fun _ => ([] : List Msg)) = [] := List.flatMap_eq_nil_iff.2 (fun _ _ => rfl)
  rw [h0, List.nil_append]
  exact hb

/-- The honest size totals: non-duplicate node bytes, non-duplicate value bytes, source-proof
bytes (what the three senders announce). -/
def honestSizeV (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) : SizeV :=
  ⟨((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum,
   ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum, srcpSize bs⟩

/-- **SIZE balances**: the three honest senders' messages are exactly the honest size table's
receives. -/
theorem honest_size_balance (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) :
    (nodeTraffic3 vs).sends B_SIZE ++ (valTraffic es).sends B_SIZE ++ (srcpTraffic bs).sends B_SIZE =
      (sizeTraffic (honestSizeV vs es bs)).recvs B_SIZE := by
  simp +decide [nodeTraffic3, nodeSends3, valTraffic, valSends, srcpTraffic, sizeTraffic, honestSizeV]

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- The located views of the plain (unpatched) honest trace carry the native receipt ids. -/
theorem located_idsU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀ xs ∈ lists, ∀ x ∈ xs, x.receipt.wf = true) :
    (locatedViews (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback)
      lists).map (fun r => r.rid) =
      lists.flatten.map (fun x => x.receipt.receiptId.map UInt8.toNat) := by
  have horder : (receiptLocations 0 (entityPlans lists)).map (fun x => x.2.input) = lists.flatten := by
    rw [receiptLocations_inputs, entityPlans_inputs]
  rw [← horder, List.map_map]
  simp only [locatedViews, List.map_map]
  apply List.map_congr_left
  intro x hx
  obtain ⟨before, after, hb, hoff⟩ := native_locations_block lists x.1 x.2 hx
  have hi : x.2.input ∈ lists.flatten := by
    rw [← horder]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨xs, hxs, hix⟩ := List.mem_flatten.mp hi
  have hid : x.2.input.receipt.receiptId.length = 32 := by
    have h := hw xs hxs x.2.input hix
    simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq] at h
    grind only
  dsimp only [Function.comp_def]
  rw [hoff]
  exact native_rid_slice own ctx lists log constants pub digests fallback headerFallback x.2 before after hb hid

/-- **RIDS balances**: the honest receipt table's id messages are exactly the honest sort
table's receives for the applied receipts in order. -/
theorem honest_rids_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_RIDS =
      (sortTraffic (Candidates.NativeSortIds.input (x.lists.flatten.map Input.receipt))).recvs B_RIDS := by
  apply Candidates.NativeReceiptIdBytes.view_ids
  rw [nativeRcptLists_flat pub x ok, List.map_map]
  exact located_idsU x.own x.ctx x.lists 22 _ pub _ _ _ ok.wf

end ZkFormal.NearV3.Assembly.RcptSkeleton
