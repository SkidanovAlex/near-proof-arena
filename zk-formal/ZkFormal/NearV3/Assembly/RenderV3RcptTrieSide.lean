import ZkFormal.NearV3.Assembly.TrieSide
import ZkFormal.NearV3.Assembly.RenderV3RcptSha
import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Candidates.AcceptedSourceShaContract

/-!
# Receipt side + trie side of the completeness obligation for an accepted witness

`rcpt_trie_side` combines `rcpt_side_balanced` (tables 16–20, 22) with `TrieSide.trie_side`
(tables 0–7, 21), discharging every receipt-side premise of `trie_side`:

* receipt SHA family (`AcceptedV3.receipt_sha`: rows `≤ 1,373,299`, bytes `< 256`) and the source
  family `sourceShaMessages A.p.lists A.w.entries` (`source_rows_A10`, `AcceptedSourceShaContract`);
* VSLOT (`AcceptedV3.vslot_views`), `RcptKeys`, `RcptFinal` (`AcceptedV3.rcpt_keys`/`rcpt_final`);
* the receipt halves (tables 16, 17, 23 and the account/post-slot cross term) of `BYTES` and
  `DIGEST`.

Premises left (explicit): the size budget `hovh` (`trie_side`'s, see the lane log: not implied by
acceptance as stated), and inside the `BYTES` / `DIGEST` conclusions the codec identities
(table 11, scheduler lane) and the source-table identities `SrcpBytes` / `SrcpDigests` (table 20
vs the deduplicated source family; open — see the lane log).
-/

namespace ZkFormal.NearV3.Assembly.RcptTrieSide

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate RcptSkeleton RcptBal ZkFormal.NearV3.UnfoldA7 TrieA7

/-- Source-table `BYTES` sends = the prepared source SHA messages' bytes (open). -/
def SrcpBytes {cb wb : Bytes} (A : AcceptedV3 cb wb) : Prop :=
  ∀ m, cnt ((srcpTraffic (SrcpGen.blocksOfProofs A.srcps)).sends B_BYTES) m =
    cnt (Sha.Gen.expectedBytes (sourceShaMessages A.p.lists A.w.entries)) m

/-- Source-table `DIGEST` receives = the source path digests + the receipt-list RC digests (open). -/
def SrcpDigests {cb wb : Bytes} (A : AcceptedV3 cb wb) : Prop :=
  ∀ m, cnt ((srcpTraffic (SrcpGen.blocksOfProofs A.srcps)).recvs B_DIGEST) m =
    cnt (Sha.Gen.expectedDigests (sourceShaMessages A.p.lists A.w.entries)) m +
      cnt (Sha.Gen.expectedDigests (sourceRcShaJobs A.k.H.shardId A.p.lists A.w.entries)) m

set_option maxHeartbeats 4000000 in
/-- **Receipt side + trie side** of an accepted witness (see the module doc). -/
theorem rcpt_trie_side {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (hovh : ovhNat A.pub + 2000000 + srcpSize (SrcpGen.blocksOfProofs A.srcps) ≤ 8388608) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide)),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
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
          SrcpBytes A → R.BalancedAt B_BYTES) ∧
        ((∀ m, cnt ((R.tf 11).recvs B_DIGEST) m = cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) →
          SrcpDigests A → R.BalancedAt B_DIGEST) := by
  obtain ⟨receipt, hrr, hbr, hRB, hRD⟩ := A.receipt_sha
  have hpr := TrieShaTwo.source_rows_A10 A.h A.hp A.hf A.hd
  obtain ⟨-, hsm, hbs⟩ := Candidates.AcceptedSourceShaContract.accepted A.h A.hp A.hf A.hd
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, hall⟩ :=
    TrieSide.trie_side A receipt (sourceShaMessages A.p.lists A.w.entries) hrr hpr hsm hbr hbs hovh
  refine ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 h24
  obtain ⟨hcore, hsize, hbytes, hdig, hvslot, hkey⟩ := hall R e0 e1 e2 e3 e4 e5 e6 e7 e21
  have t16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput := bundle_tf_eq R 16 _ h16
  have t17 : R.tf 17 = acctV3Traffic A.accts := bundle_tf_eq R 17 _ h17
  have t20 : R.tf 20 = srcpTraffic (SrcpGen.blocksOfProofs A.srcps) := bundle_tf_eq R 20 _ h20
  have t23 : R.tf 23 = A.mrkAcc.tf := bundle_tf_eq R 23 _ h23
  refine ⟨rcpt_side_balanced A R h16 h17 h18 h19 h20 h22 h24, hcore, hsize h20,
    hvslot h17 (A.vslot_views hr hkf), (hkey h16 h22 A.rcpt_keys A.rcpt_final).1,
    (hkey h16 h22 A.rcpt_keys A.rcpt_final).2, ?_, ?_⟩
  · intro hc hs
    apply hbytes hc
    intro m
    have h1 := hRB m
    have h2 := hs m
    rw [t16, t17, t20, t23]
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, Sha.Gen.expectedBytes, List.flatMap_append,
      List.map_append, List.count_append] at h1 h2 ⊢
    omega
  · intro hc hs
    apply hdig hc
    intro m
    have h1 := hRD m
    have h2 := hs m
    have h3 := A.account_digests q hr hkf m
    rw [t16, t20, t23]
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, Sha.Gen.expectedDigests, List.filter_append,
      List.map_append, List.count_append] at h1 h2 h3 ⊢
    omega

end ZkFormal.NearV3.Assembly.RcptTrieSide
