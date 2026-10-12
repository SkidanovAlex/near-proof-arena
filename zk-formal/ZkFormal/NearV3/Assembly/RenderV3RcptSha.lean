import ZkFormal.NearV3.Assembly.RenderV3RcptTrie
import ZkFormal.NearV3.Assembly.TrieShared
import ZkFormal.NearV3.Render.MrkAccepted
import ZkFormal.NearV3.Render.PaddedMrk
import ZkFormal.NearV3.Candidates.ReceiptSourcePublicBody
import ZkFormal.NearV3.Candidates.ReceiptPublicByteCount
import ZkFormal.NearV3.Candidates.ReceiptDigestPartition

/-!
# Receipt-side SHA family and the receipt halves of the `BYTES` / `DIGEST` identities

For an accepted witness `A`, the receipt SHA job family
`ReceiptGatedShaJobs.jobs A.pub ls A.accts (fun _ => false)` (the
duplicate-gated receipt/refund/PEO/RC/account/Merkle jobs of `ReceiptSourcePublicBody.native`,
`ls` the honest receipt list view) has `≤ 1,373,299` SHA rows and bytes `< 256`, and

* `BYTES`: tables 16 (`rcptTrafficB`), 17 (`acctV3Traffic A.accts`) and 23 (the accepted outcome
  Merkle render) send exactly its bytes plus the public refund fragments
  (`pubCount nearAirV3 A.pub B_BYTES false`);
* `DIGEST`: its digests are received by tables 16 and 23, by the source table (the RC digests
  `sourceRcShaJobs`, every occurrence's output enabled: duplicate occurrences too, as the source
  table receives one per occurrence) and by the node table's post-slot digests (the account jobs,
  `TrieShared.vslot_accepted`, for any `oldPost` the trie side exports).
-/

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.NearV3.Rcpt.Candidates

/-- The outcome trace itself carries the table-23 render traffic. -/
theorem outcome_traffic_v3 (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length ≤ 4481)
    (hp : ∀ i < 4, pub.getD (ZkFormal.NearV3.PH_N + i) 0 = Fp.ofNat (os.length / 256 ^ i % 256))
    (ho : ∀ i < 32, pub.getD (ZkFormal.NearV3.PH_OUT + i) 0 =
      Fp.ofNat (((NearSpec.outcomeRoot os).getD i 0).toNat)) :
    TableTraffic MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub
      (ZkFormal.NearV3.Assembly.mrkTrafficE pub (decide (os = [])) (generatedView os.length (mrkLevels os))) := by
  have hL := outcome_local os pub hn hp ho
  by_cases he : os = []
  · subst he
    have hc0 : MerkleEmpty.countE.eval (outcomeTrace [] pub) T_MRK 0 pub = 0 :=
      MerkleEmpty.count_zero _ 0 pub (fun i hi => by rw [hp i hi, List.length_nil, Nat.zero_div, Nat.zero_mod]; rfl)
    obtain ⟨-, hz⟩ := MerkleEmpty.empty_view hL hc0
    intro b m
    simp only [ZkFormal.NearV3.Assembly.mrkTrafficE, decide_true, ite_true, List.map_nil, List.count_nil]
    exact ⟨hz b true m, hz b false m⟩
  · have hn1 : 1 ≤ os.length := List.length_pos_iff.mpr he
    simp only [ZkFormal.NearV3.Assembly.mrkTrafficE, he, decide_false, Bool.false_eq_true, ite_false]
    exact outcome_nonempty_traffic os pub hn1 hn

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Assembly.AcceptedV3
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Candidates RcptSkeleton RcptV3Proof
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- The accepted outcome Merkle render (table 23). -/
noncomputable def mrkAcc : TableRenderV3 A.pub 23 (by decide) :=
  mrkRender_accepted A.hp A.hk A.hw A.h A.hm 0

theorem accountJobs_bytes : ∀ M ∈ accountShaJobs A.accts, ∀ b ∈ M.bytes, b < 256 := by
  intro M hM b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hM
  have hab := A.accts_spec.2.2.2 a ha
  rcases List.mem_append.mp hb with h | h
  · exact hab b (List.mem_append_right _ h)
  · exact hab b (List.mem_append_left _ (List.mem_of_mem_drop h))

/-- **The receipt SHA family and the receipt halves of BYTES / DIGEST.** -/
theorem receipt_sha : ∃ receipt : List Sha.Gen.Msg,
    (Sha.Gen.honestRows receipt).length ≤ 1373299 ∧
    (∀ M ∈ receipt, ∀ x ∈ M.bytes, x < 256) ∧
    (∀ m, cnt ((rcptTrafficB A.pub A.rcptInput).sends B_BYTES) m +
        cnt ((acctV3Traffic A.accts).sends B_BYTES) m + cnt (A.mrkAcc.tf.sends B_BYTES) m =
      cnt (Sha.Gen.expectedBytes receipt) m + ZkFormal.V2.pubCount nearAirV3 A.pub B_BYTES false m) ∧
    (∀ m, cnt (Sha.Gen.expectedDigests receipt) m =
      cnt ((rcptTrafficB A.pub A.rcptInput).recvs B_DIGEST) m + cnt (A.mrkAcc.tf.recvs B_DIGEST) m +
        cnt (Sha.Gen.expectedDigests ((sourceRcShaJobs A.k.H.shardId A.p.lists A.w.entries).map
          fun m => { m with dmult := true })) m +
        cnt (Sha.Gen.expectedDigests (jobsToSha (accountShaJobs A.accts))) m) := by
  have hbp := A.boundedPrep_eq
  have hA : ∀ msg, tableBusCount AccountEmpty.table.interactions A.acctAcc.tr 17
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes
        (RoutingBoundedLayout.boundedPrep A.p A.k.L A.k.H.shardId) 0)) B_BYTES true msg =
      cnt (acctV3Sends A.accts B_BYTES) msg := by
    intro msg; rw [hbp]; exact (A.acctAcc.traffic B_BYTES msg).1
  have hN := ReceiptSourcePublicBody.native A.hp A.hk A.hd A.hw A.rel A.hm 0
    A.rcptInput.accountId A.rcptInput.accessId A.rcptInput.constants A.rcptInput.digests
    A.rcptInput.fallback A.rcptInput.headerFallback A.accts A.accts_spec.2.2.1
    (by have := A.accts_spec.2.1; omega) A.accountJobs_bytes A.acctAcc.tr 17 hA
  dsimp only at hN
  rw [hbp] at hN
  obtain ⟨mid, so, steps, hsched, hledger, -, -, bs, e, -, -, -, -, -, -, -, -, hfull, hrc, hrows, hbytes,
    -, hphys⟩ := hN
  have hs : A.rcptInput.steps = steps := by
    show (match schedStep prims (A.m.ctx A.k) A.m.pre with
      | .ok (mid, _) => (nativeDepositLedger (A.m.ctx A.k) ⟨mid, [], [], 0, 0⟩
          ((sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries).flatten.map Input.receipt)).getD []
      | .error _ => []) = steps
    rw [hsched]; simp only [hledger, Option.getD_some]
  have hpatch := patched_counts A.pub A.rcptInput A.rcptOk
  have heq : RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0 =
      RoutingQCandidate.patchTrace (booleanReceiptTrace A.k.H.shardId (A.m.ctx A.k) (sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries) 22
        (completeReceiptConstants (A.m.ctx A.k) A.k A.rcptInput.accountId
          (depositConstants (depositPlanAccount steps)
            (depositAgeConstants (depositPlanPrevious (sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries)) A.rcptInput.constants)))
        (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) (nativeDigests (A.m.ctx A.k) A.rcptInput.digests)
        (completeReceiptAux (A.m.ctx A.k) A.k (sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries) A.rcptInput.accountId A.rcptInput.accessId
          (depositFinalAux (depositPlanPrevious (sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries)) (depositPlanAccount steps) A.rcptInput.fallback))
        (completeReceiptHeaders (depositHeaderAux A.rcptInput.headerFallback))) 0 := by
    unfold rcptTraceNative; rw [hs]; rfl
  rw [← heq] at hfull hphys hrows hbytes hrc
  obtain ⟨mn, mp, mo⟩ := mrk_premises_accepted A.hp A.hk A.hw A.h A.hm 0
  have hM := outcome_traffic_v3 A.m.result.outcomes A.pub mn mp mo
  have hpub : ∀ msg, ZkFormal.V2.pubCount nearAirV3 A.pub B_BYTES false msg =
      cnt (emitAt K_RF 8 ((A.p.body.drop 8).map UInt8.toNat)) msg := by
    intro msg
    have h := ReceiptPublicByteCount.accepted nearAirV3 A.hp A.hk A.hw A.h A.hm 0 rfl msg
    rw [hbp] at h
    exact h
  have hrcAll : ReceiptGatedShaJobs.rcJobs (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) (bs.map (ListBlock.view (RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0) 0)) (fun _ => false) =
      (sourceRcShaJobs A.k.H.shardId A.p.lists A.w.entries).map (fun m => { m with dmult := true }) := by
    rw [← hrc]
    simp [ReceiptGatedShaJobs.rcJobs, List.map_map, Function.comp_def]
  refine ⟨ReceiptGatedShaJobs.jobs (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) (bs.map (ListBlock.view (RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0) 0)) A.accts (fun _ => false), ?_, ?_, ?_, ?_⟩
  · rw [ReceiptGatedShaJobs.rows_unchanged]
    rw [ReceiptGatedShaJobs.rows_unchanged] at hrows
    exact hrows
  · intro M hM b hb
    simp only [ReceiptGatedShaJobs.jobs, List.mem_append] at hM hbytes
    rcases hM with hM | hM
    · simp only [ReceiptGatedShaJobs.rcJobs] at hM hbytes
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hM
      exact hbytes _ (Or.inl (List.mem_map.mpr ⟨q, hq, rfl⟩)) b hb
    · exact hbytes M (Or.inr hM) b hb
  · intro m
    have h1 := hphys m
    rw [ReceiptGatedShaJobs.bytes_unchanged] at h1
    rw [ReceiptGatedShaJobs.bytes_unchanged]
    have e16 : tableBusCount ReceiptCandidateRouting.candidateTable.interactions (RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0) 0 (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_BYTES true m =
        (((rcptTrafficB A.pub A.rcptInput).sends B_BYTES).map Msg.toFp).count m := (hpatch B_BYTES (by decide) m).1
    have e17 : tableBusCount AccountEmpty.table.interactions A.acctAcc.tr 17 (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_BYTES true m =
        ((acctV3Sends A.accts B_BYTES).map Msg.toFp).count m := (A.acctAcc.traffic B_BYTES m).1
    have e23 : tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace A.m.result.outcomes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0))) ZkFormal.Near.T_MRK (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_BYTES true m =
        ((A.mrkAcc.tf.sends B_BYTES).map Msg.toFp).count m := (hM B_BYTES m).1
    have ep := hpub m
    have h3 : ((acctV3Traffic A.accts).sends B_BYTES) = acctV3Sends A.accts B_BYTES := rfl
    rw [h3]
    rw [e16, e17, e23] at h1
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt] at h1 ep ⊢
    omega
  · intro m
    have h1 := hfull m
    have e16 : tableBusCount ReceiptCandidateRouting.candidateTable.interactions (RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0) 0 (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_DIGEST false m =
        (((rcptTrafficB A.pub A.rcptInput).recvs B_DIGEST).map Msg.toFp).count m := (hpatch B_DIGEST (by decide) m).2
    have e23 : tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace A.m.result.outcomes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0))) ZkFormal.Near.T_MRK (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_DIGEST false m =
        ((A.mrkAcc.tf.recvs B_DIGEST).map Msg.toFp).count m := (hM B_DIGEST m).2
    rw [e16, e23] at h1
    simp only [ReceiptGatedShaJobs.jobs] at h1 ⊢
    rw [hrc] at h1
    rw [hrcAll]
    simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, Sha.Gen.expectedDigests, List.map_append, List.filter_append,
      List.count_append] at h1 ⊢
    omega

/-- The account SHA digests are the node table's post-slot digests, for every `oldPost` the
trie side may export. -/
theorem account_digests {writes : List (List Nat × Bytes)} {oldPost : PTrie} (q : UseRequests)
    (hr : SizedAccountRun A.m.pre writes oldPost) (hkf : KeysFinal A.k A.w A.m writes oldPost) (m : List Fp) :
    cnt (Sha.Gen.expectedDigests (jobsToSha (accountShaJobs A.accts))) m =
      cnt ((TrieNative.nodes A.m A.steps oldPost writes q).flatMap postSlotDigests) m := by
  obtain ⟨hkeys, state, hup⟩ := hkf
  have hp := TrieShared.vslot_accepted A.hm hr hkeys hup (A.vslot_views hr ⟨hkeys, state, hup⟩) A.steps q
  rw [ReceiptDigestPartition.jobs_digests]
  exact (hp.map Msg.toFp).count_eq m

end ZkFormal.NearV3.Assembly.AcceptedV3
