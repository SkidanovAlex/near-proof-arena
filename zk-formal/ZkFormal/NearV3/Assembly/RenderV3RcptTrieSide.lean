import ZkFormal.NearV3.Assembly.TrieSide
import ZkFormal.NearV3.Assembly.RenderV3RcptSha
import ZkFormal.NearV3.Assembly.RenderV3SrcpSha
import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Candidates.AcceptedSourceShaContract

/-!
# Receipt side + trie side of the completeness obligation for an accepted witness

`rcpt_trie_side` combines `rcpt_side_balanced` (tables 16–20, 22) with `TrieSide.trie_side_exact`
(tables 0–7, 21), discharging every receipt-side premise of the trie side:

* receipt SHA family (`AcceptedV3.receipt_sha`: rows `≤ 1,373,299`, bytes `< 256`, every RC digest
  output enabled) and the source family as the source table emits it, duplicates included
  (`AcceptedV3.srcShaAll`: rows `≤ 2,257,792`, messages `≤ 35` rows, bytes `< 256`);
* VSLOT (`AcceptedV3.vslot_views`), `RcptKeys`, `RcptFinal` (`AcceptedV3.rcpt_keys`/`rcpt_final`);
* the receipt/source halves of `BYTES` and `DIGEST` (tables 16, 17, 20, 23 and the account/post-slot
  cross term; `receipt_sha`, `srcp_bytes`, `srcp_digests`, `account_digests`).

Premises left: the exact size budget `TrieSide.SizeBudget A`, and inside the `BYTES` / `DIGEST`
conclusions the codec identities (table 11, scheduler lane).
-/

namespace ZkFormal.NearV3.Assembly.RcptTrieSide

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate RcptSkeleton RcptBal ZkFormal.NearV3.UnfoldA7 TrieA7

set_option maxHeartbeats 4000000 in
/-- **Receipt side + trie side** of an accepted witness (see the module doc). -/
theorem rcpt_trie_side {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (hovh : TrieSide.SizeBudget A) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide)),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
      CallPin A.k A.m A.steps us ∧
      (∃ (Js : List UpsInst) (hok : UpsRenderOk Js), r7 = upsRenderV3 A.pub Js hok ∧
        ExtOf r7.tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))) ∧
        Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)) ∧
        Js.map Assembly.UpsS0F.s0fOf = (A.m.pre :: A.steps.map ImplicitStepV3.pre).mapIdx
          (fun i t => Assembly.UpsS0F.s0fPair ((A.m.pre :: A.steps.map ImplicitStepV3.pre).take i) t)) ∧
      -- lane v3-render-vbytes: the value render's base traffic (for `VBYTES`)
      ExtOf r4.tf (valTraffic (TrieNative.vals A.m A.steps)) ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨0, by decide⟩ = r0 → R ⟨1, by decide⟩ = r1 → R ⟨2, by decide⟩ = r2 → R ⟨3, by decide⟩ = r3 →
        R ⟨4, by decide⟩ = r4 → R ⟨5, by decide⟩ = r5 → R ⟨6, by decide⟩ = r6 → R ⟨7, by decide⟩ = r7 →
        R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨17, by decide⟩ = A.rcptRenders.acct →
        R ⟨18, by decide⟩ = A.rcptRenders.akey → R ⟨19, by decide⟩ = A.rcptRenders.bnd →
        R ⟨20, by decide⟩ = A.rcptRenders.srcp → R ⟨21, by decide⟩ = r21 →
        R ⟨22, by decide⟩ = A.rcptRenders.qv → R ⟨23, by decide⟩ = A.mrkAcc →
        R.tf 24 = sortTraffic (Candidates.NativeSortIds.input (A.rcptInput.lists.flatten.map Input.receipt)) →
        -- receipt-side buses
        (BusBalanced R B_SREC ∧ BusBalanced R B_RCL ∧ BusBalanced R B_AKC ∧ BusBalanced R B_RIDS ∧
          BusBalanced R B_MEM ∧ BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC ∧
          BusBalanced R B_QSH ∧ BusBalanced R B_SRC ∧ BusBalanced R B_BNDP ∧ BusBalanced R B_BND) ∧
        -- trie-side buses
        (R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧ R.BalancedAt B_DIGS ∧
          R.BalancedAt B_DUP ∧ R.BalancedAt B_EDGE ∧ R.BalancedAt B_BMAP ∧ R.BalancedAt B_MIDROOT ∧
          R.BalancedAt B_ROOT ∧ R.BalancedAt B_UPB ∧ R.BalancedAt B_MEMD ∧ R.BalancedAt B_RPL ∧
          R.BalancedAt B_RPLV) ∧
        -- shared buses
        R.BalancedAt B_SIZE ∧ R.BalancedAt B_VSLOT ∧ R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL ∧
        ((∀ m, cnt ((R.tf 11).sends B_BYTES) m = cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m) →
          R.BalancedAt B_BYTES) ∧
        ((∀ m, cnt ((R.tf 11).recvs B_DIGEST) m = cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) →
          R.BalancedAt B_DIGEST) := by
  obtain ⟨receipt, hrr, hbr, hRB, hRD⟩ := A.receipt_sha
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, hpin, hups, hval, hall⟩ :=
    TrieSide.trie_side_exact A receipt A.srcShaAll hrr A.srcShaAll_rows A.srcShaAll_msgRows hbr
      A.srcShaAll_bytes hovh
  refine ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, hpin, hups, hval, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 h24
  obtain ⟨hcore, hsize, hbytes, hdig, hvslot, hkey⟩ := hall R e0 e1 e2 e3 e4 e5 e6 e7 e21
  have t16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput := bundle_tf_eq R 16 _ h16
  have t17 : R.tf 17 = acctV3Traffic A.accts := bundle_tf_eq R 17 _ h17
  have t20 : R.tf 20 = A.ddTraffic := bundle_tf_eq R 20 _ h20
  have t23 : R.tf 23 = A.mrkAcc.tf := bundle_tf_eq R 23 _ h23
  refine ⟨rcpt_side_balanced A R h16 h17 h18 h19 h20 h22 h24, hcore, hsize h20,
    hvslot h17 (A.vslot_views hr hkf), (hkey h16 h22 A.rcpt_keys A.rcpt_final).1,
    (hkey h16 h22 A.rcpt_keys A.rcpt_final).2, ?_, ?_⟩
  · intro hc
    apply hbytes hc
    intro m
    have h1 := hRB m
    have h2 := A.srcp_bytes m
    rw [t16, t17, t20, t23]
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, Sha.Gen.expectedBytes, List.flatMap_append,
      List.map_append, List.count_append] at h1 h2 ⊢
    omega
  · intro hc
    apply hdig hc
    intro m
    have h1 := hRD m
    have h2 := A.srcp_digests m
    have h3 := A.account_digests q hr hkf m
    rw [AcceptedV3.rcShaAll] at h2
    rw [t16, t20, t23]
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, Sha.Gen.expectedDigests, List.filter_append,
      List.map_append, List.count_append] at h1 h2 h3 ⊢
    omega

end ZkFormal.NearV3.Assembly.RcptTrieSide
