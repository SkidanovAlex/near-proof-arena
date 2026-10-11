import ZkFormal.NearV3.Assembly.RcptViewV3
import ZkFormal.NearV3.Assembly.RcptCandidateTotalBounds
import ZkFormal.NearV3.Assembly.RcptCandidateTokenPublic
import ZkFormal.NearV3.Assembly.RcptCandidateRclDecode

/-!
# ZkFormal.NearV3.Assembly.RcptViewCounts — the repaired receipt view with its counts

`rcptV3_view_counts` is `RcptViewV3.rcptV3_view_nearAir` (same proof) with two more
conclusions: at most `2^22` lists and `2^22` receipts (each list takes ≥ 12 rows, each receipt
≥ 1 row, the table has `≤ 2^22` rows).  The receipt `BYTES` ids are canonical under these
bounds (`RcptLink.receipt_bytes_ids`), which the `BYTES` kind registry uses.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

theorem rcptV3_view_counts {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsize : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    {tr : Trace Fp}
    (hH : HoldsP nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr) :
    ∃ ls, ZkFormal.NearV3.RcptV3Wf (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.RcptV3.interactions tr T_RCPT
        (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (ZkFormal.NearV3.rcptTraffic3
          (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls) ∧
      ls.length ≤ 2 ^ 22 ∧ (ZkFormal.NearV3.flatR ls).length ≤ 2 ^ 22 := by
  generalize hpub : Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh) = pub at hH ⊢
  have hL : TableLocal receiptArithmeticCandidate tr T_RCPT pub := rcptLocal hH
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL
  have ht := ReceiptCandidateProof.ListChain.view_traffic hL hc
  have hranges : ReceiptPublicRanges pub := by
    rw [← hpub]; exact prepared_receipt_ranges hp oh (prepD0_roots hp) hsize
  have hmem : ∀ m : List Fp,
      0 < tableBusCount RcptV3.interactions tr T_RCPT pub B_MEM false m → (m.getD 1 0).toNat ≤ 2 ^ 22 := by
    intro m hpos
    have hconv : ∀ v : Msg, v.getD 1 0 ≤ 2 ^ 22 → (v.toFp.getD 1 0).toNat ≤ 2 ^ 22 := by
      intro v hv
      have heq : (v.toFp.getD 1 0).toNat = (v.getD 1 0) % P := by
        cases v with
        | nil => rfl
        | cons a vs => cases vs with
          | nil => rfl
          | cons b tail => exact Fp.toNat_ofNat b
      rw [heq, Nat.mod_eq_of_lt (by unfold P; omega)]; exact hv
    rcases mem_send_sources hH m hpos with h16 | h17
    · rw [(ht B_MEM m).1] at h16
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp h16)
      exact hconv v (ReceiptCandidateProof.receipt_memory_provider_bound hL hc hv)
    · obtain ⟨as, -, tA⟩ := acctView hH
      rw [(tA B_MEM m).1] at h17
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp h17)
      exact hconv v (by rw [ReceiptCandidateProof.account_memory_provider_zero hv]; omega)
  have hprov : ∀ B ∈ bs, ∀ y ∈ B.receipts, (rcptOf tr T_RCPT y).tprev ≤ 2 ^ 22 := by
    intro B hB y hy
    have hx : rcptOf tr T_RCPT y ∈ flatR (bs.map (ListBlock.view tr T_RCPT)) := by
      rw [flat_views]
      exact List.mem_map.mpr ⟨y, List.mem_flatMap.mpr ⟨B, hB, hy⟩, rfl⟩
    let x := rcptOf tr T_RCPT y
    let mm : Msg := [x.kslot, x.tprev, 0, x.bef.getD 0 0, x.lk.getD 0 0, x.st.getD 0 0]
    have hm : mm ∈ rcptRecvs3 (bs.map (ListBlock.view tr T_RCPT)) B_MEM :=
      ReceiptCandidateProof.memory_version_read hx
    have hp' : 0 < tableBusCount RcptV3.interactions tr T_RCPT pub B_MEM false mm.toFp := by
      rw [(ht B_MEM mm.toFp).2]
      exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨mm, hm, rfl⟩)
    have hb := hmem mm.toFp hp'
    have hc' := ReceiptCandidateProof.extracted_previous_canonical hx
    simpa [mm, x, Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc'] using hb
  have hcnt : (bs.map (ListBlock.view tr T_RCPT)).length ≤ 2 ^ 22 ∧
      (ZkFormal.NearV3.flatR (bs.map (ListBlock.view tr T_RCPT))).length ≤ 2 ^ 22 := by
    have hlist := ReceiptCandidateProof.ListChain.length_le_rows hc
    have hreceipts := ReceiptCandidateProof.receipt_counts_le_rows bs
    have hrows := ReceiptCandidateProof.ListChain.rows hc
    have hlast := (ReceiptCandidateProof.ListChain.last_row hL hc).2.1
    have hheight := ReceiptCandidateProof.height_le hL
    simp only [List.length_map, ReceiptCandidateProof.flat_views_length]
    omega
  exact ⟨_, ReceiptCandidateProof.ListChain.view_wf hL hc
    (ReceiptPublicAdmission.ranges_candidate hranges) hprov, ht, hcnt⟩

end ZkFormal.NearV3.Assembly
