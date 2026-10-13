import ZkFormal.NearV3.Assembly.ViewsV3
import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.Assembly.RcptCandidateMemoryProviders
import ZkFormal.NearV3.Assembly.RcptCandidateFamilyPublicMemory
import ZkFormal.NearV3.Assembly.RcptCandidatePublicAdmission
import ZkFormal.NearV3.Assembly.PrepFacts
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges
import ZkFormal.NearV3.Assembly.RcptCandidateBounds
import ZkFormal.NearV3.Assembly.RcptCandidateRouteRows

/-!
# ZkFormal.NearV3.Assembly.RcptViewV3 — the view of the repaired receipt table

`nearAirV3` table 16 is `RcptV3.tableQ` (= `ReceiptCandidateRouting.candidateTable`:
`RcptV3.tableR` = `receiptArithmeticCandidate` (system-gas and 13-bit deposit-age repairs)
plus the routing-index range check; every extracted receipt has `q < 128`).  The repaired view gives the **same** `RcptV3Wf` and exact
traffic as the original (`ReceiptCandidateProof.ListChain.view_wf`/`view_traffic`).  Its
13-bit age no-wrap needs every previous version `tprev ≤ 2^22`; that comes from the global
`MEM` balance of `HoldsP nearAirV3`: only `rcptV3` (16) and `acctV3` (17) touch `MEM`, the
prepared public segments carry none, account opens have version `0` and receipt writes have
version `r + 1 ≤ 2^22`.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof RcptSkeleton

set_option maxRecDepth 16384 in
/-- On the installed table 16 every extracted receipt (a `Layout`) has interval index `< 128`
(the first receiver row carries the range check). -/
theorem extracted_q_ltQ {tr : Trace Fp} {tt : Nat} {pub : List Fp} {y : RS}
    (h : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) : (rcptOf tr tt y).q < 128 := by
  have hb := repaired_local_base h
  have F := route_receiver hb lay
  have hz : 0 < y.Lv := by have hh := lay.pos; omega
  have hs : tr.cell tt (lkRow y 0) sV = 1 := by simpa using F.fld.st 0 hz
  have hf : tr.cell tt (lkRow y 0) fs = 1 := by simpa using F.fld.fs 0 hz
  have hq := repaired_first_receiver_q hb h (route_height hb lay 0 (by omega)) hs hf
  have he := F.consts 0 hz RcptV3.q (by simp [rconsts])
  simp only [Nat.add_zero] at he
  change cv tr tt y.s RcptV3.q < 128
  simpa only [cv, he] using hq

/-- Every receipt of the complete physical list view has `q < 128` (installed table 16). -/
theorem view_q {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {bs : List ListBlock} {e : Nat} (hc : ListChain tr tt 0 bs e) :
    ∀ x ∈ ZkFormal.NearV3.flatR (bs.map (ListBlock.view tr tt)), x.q < 128 := by
  intro x hx
  rw [flat_views] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨B, hB, hy⟩ := List.mem_flatMap.mp hy
  exact extracted_q_ltQ h ((hc.blocks B hB).layouts y hy)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

theorem tableBusCount_nobus {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {b : Nat} (h : ∀ i ∈ is, i.bus ≠ b) (s : Bool) (m : List Fp) :
    tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  have : (List.range (tr.height t)).flatMap (fun r => rowTraffic is tr t r pub b s) = [] :=
    List.flatMap_eq_nil_iff.2 fun r _ => by
      unfold rowTraffic
      exact List.flatMap_eq_nil_iff.2 fun i hi => by simp [h i hi]
  rw [this]; rfl

/-- Only tables 16 (`rcptV3`) and 17 (`acctV3`) have `MEM` interactions. -/
theorem nearAir_mem_tables : ∀ t (ht : t < nearTablesFull.length), t ≠ T_RCPT → t ≠ T_ACCT →
    ∀ i ∈ (nearTablesFull[t]'ht).interactions, i.bus ≠ B_MEM := by
  have hh : (List.range nearTablesFull.length).all (fun t => t == 16 || t == 17 ||
      (nearTablesFull.getD t default).interactions.all (fun i => i.bus != B_MEM)) = true := by
    decide +kernel
  intro t ht h16 h17 i hi
  have h := List.all_eq_true.mp hh t (List.mem_range.2 ht)
  have h16' : (t == 16) = false := by simpa using (show t ≠ 16 from h16)
  have h17' : (t == 17) = false := by simpa using (show t ≠ 17 from h17)
  simp only [h16', h17', beq_iff_eq, false_or, Bool.false_or] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at h
  have := List.all_eq_true.mp h i hi
  simpa using this

theorem nat_le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem nat_sum_eq_zero {l : List Nat} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.sum_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem mapIdx_sum_ge {α : Type} (l : List α) (f : Nat → α → Nat) (i : Nat) (hi : i < l.length) :
    f i (l[i]'hi) ≤ (l.mapIdx f).sum := by
  apply nat_le_sum_of_mem
  rw [List.mem_iff_getElem]
  exact ⟨i, by simpa using hi, by simp⟩

theorem mapIdx_sum_zero {α : Type} (l : List α) (f : Nat → α → Nat)
    (h : ∀ i (hi : i < l.length), f i (l[i]'hi) = 0) : (l.mapIdx f).sum = 0 := by
  apply nat_sum_eq_zero
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [List.getElem_mapIdx]
  exact h i (by simpa using hi)

/-- A positively received receipt `MEM` message is sent by `rcptV3` or `acctV3`. -/
theorem mem_send_sources {pub : List Fp} {tr : Trace Fp}
    (hH : HoldsP nearAirV3 pub tr) (m : List Fp)
    (hpos : 0 < tableBusCount RcptV3.interactions tr T_RCPT pub B_MEM false m) :
    0 < tableBusCount RcptV3.interactions tr T_RCPT pub B_MEM true m ∨
      0 < tableBusCount AcctV3.interactions tr T_ACCT pub B_MEM true m := by
  have hb := hH.balance B_MEM m
  rw [ReceiptFamilyMemory.prepared_mem_count_zero nearAirV3 rfl pub true m,
    ReceiptFamilyMemory.prepared_mem_count_zero nearAirV3 rfl pub false m,
    busCount_nearAirV3, busCount_nearAirV3] at hb
  have hrecv := mapIdx_sum_ge nearTablesFull
    (fun t T => tableBusCount T.interactions tr t pub B_MEM false m) 16 (by decide)
  have hrecv' : tableBusCount RcptV3.interactions tr T_RCPT pub B_MEM false m ≤
      (nearTablesFull.mapIdx fun t T => tableBusCount T.interactions tr t pub B_MEM false m).sum :=
    hrecv
  refine Classical.byContradiction fun hn => ?_
  simp only [not_or, Nat.not_lt, Nat.le_zero] at hn
  have hz := mapIdx_sum_zero nearTablesFull
    (fun t T => tableBusCount T.interactions tr t pub B_MEM true m) (fun t ht => by
      by_cases h16 : t = T_RCPT
      · subst h16; exact hn.1
      · by_cases h17 : t = T_ACCT
        · subst h17; exact hn.2
        · exact tableBusCount_nobus (nearAir_mem_tables t ht h16 h17) true m)
  omega

/-- **`RcptV3ViewStmt` for the installed `nearAirV3` table 16**: the same `RcptV3Wf` and
exact traffic as the original view, from successful preparation, the packed public-size
bound and `HoldsP` (for the `MEM` version bound); plus the routing-index bound `q < 128` of
every receipt (from the table-16 range check). -/
theorem rcptV3_view_nearAir {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsize : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    {tr : Trace Fp}
    (hH : HoldsP nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr) :
    ∃ ls, ZkFormal.NearV3.RcptV3Wf (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.RcptV3.interactions tr T_RCPT
        (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (ZkFormal.NearV3.rcptTraffic3
          (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls) ∧
      ∀ x ∈ ZkFormal.NearV3.flatR ls, x.q < 128 := by
  generalize hpub : Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh) = pub at hH ⊢
  have hL : TableLocal receiptArithmeticCandidate tr T_RCPT pub := rcptLocal hH
  have hQ : TableLocal ReceiptCandidateRouting.candidateTable tr T_RCPT pub := rcptLocalQ hH
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
  exact ⟨_, ReceiptCandidateProof.ListChain.view_wf hL hc
    (ReceiptPublicAdmission.ranges_candidate hranges) hprov, ht,
    ReceiptCandidateProof.view_q hQ hc⟩

end ZkFormal.NearV3.Assembly
