import ZkFormal.NearV3.Assembly.RenderV3RcptSha

/-!
# `MPOS` (bus 9) balance of the honest render

Senders: the receipt table (16, one leaf position `[0, r, K_LEAF + 16 r, 68]` per applied
receipt) and the outcome Merkle table (23, one parent position per node); receiver: the outcome
Merkle table (23, the root position and every child position).  No public messages.

* `AcceptedV3.receipt_mpos`: the count identity on the traffic of the accepted receipt render
  (`rcptTrafficB A.pub A.rcptInput`) and the accepted outcome Merkle render (`A.mrkAcc`); from
  `ReceiptSourcePublicBody.native` (the receipt leaves are the native outcome preimages, so
  `MerkleRender.receipt_outcome_positions` closes the bus on the physical tables), transported
  to the render traffic by `patched_counts` and `outcome_traffic_v3` — the same route as
  `AcceptedV3.receipt_sha`.
* **`RenderBundleV3.balancedAt_mpos`**: every bundle carrying the accepted receipt render at 16
  and `A.mrkAcc` at 23 balances `MPOS`.
-/

namespace ZkFormal.NearV3.Assembly.AcceptedV3
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Candidates RcptSkeleton RcptV3Proof
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- **The `MPOS` identity of the accepted receipt and outcome Merkle renders.** -/
theorem receipt_mpos (m : List Fp) :
    cnt ((rcptTrafficB A.pub A.rcptInput).sends B_MPOS) m + cnt (A.mrkAcc.tf.sends B_MPOS) m =
      cnt (A.mrkAcc.tf.recvs B_MPOS) m := by
  have hbp := A.boundedPrep_eq
  have hA : ∀ msg, tableBusCount AccountEmpty.table.interactions A.acctAcc.tr 17
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes
        (RoutingBoundedLayout.boundedPrep A.p A.k.L A.k.H.shardId) 0)) B_BYTES true msg =
      ZkFormal.Near.cnt (acctV3Sends A.accts B_BYTES) msg := by
    intro msg; rw [hbp]; exact (A.acctAcc.traffic B_BYTES msg).1
  have hN := ReceiptSourcePublicBody.native A.hp A.hk A.hd A.hw A.rel A.hm 0
    A.rcptInput.accountId A.rcptInput.accessId A.rcptInput.constants A.rcptInput.digests
    A.rcptInput.fallback A.rcptInput.headerFallback A.accts A.accts_spec.2.2.1
    (by have := A.accts_spec.2.1; omega) A.accountJobs_bytes A.acctAcc.tr 17 hA
  dsimp only at hN
  rw [hbp] at hN
  obtain ⟨mid, so, steps, hsched, hledger, -, -, bs, e, -, -, -, -, -, hmpos, -⟩ := hN
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
  rw [← heq] at hmpos
  obtain ⟨mn, mp, mo⟩ := mrk_premises_accepted A.hp A.hk A.hw A.h A.hm 0
  have hM := outcome_traffic_v3 A.m.result.outcomes A.pub mn mp mo
  have h1 := hmpos m
  have e16 : tableBusCount ReceiptCandidateRouting.candidateTable.interactions
      (RoutingQCandidate.patchTrace (rcptTraceNative A.pub A.rcptInput) 0) 0
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_MPOS true m =
      (((rcptTrafficB A.pub A.rcptInput).sends B_MPOS).map Msg.toFp).count m :=
    (hpatch B_MPOS (by decide) m).1
  have e23s : tableBusCount MerkleEmpty.table.interactions
      (MerkleRender.outcomeTrace A.m.result.outcomes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)))
      ZkFormal.Near.T_MRK (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_MPOS true m =
      ((A.mrkAcc.tf.sends B_MPOS).map Msg.toFp).count m := (hM B_MPOS m).1
  have e23r : tableBusCount MerkleEmpty.table.interactions
      (MerkleRender.outcomeTrace A.m.result.outcomes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)))
      ZkFormal.Near.T_MRK (ZkFormal.Udr.pubOf Fp (Public.preparedBytes A.p 0)) B_MPOS false m =
      ((A.mrkAcc.tf.recvs B_MPOS).map Msg.toFp).count m := (hM B_MPOS m).2
  rw [e16, e23s, e23r] at h1
  simpa only [ZkFormal.NearV3.Assembly.cnt] using h1

end ZkFormal.NearV3.Assembly.AcceptedV3

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render RcptSkeleton

theorem covers_mpos_send : Covers B_MPOS true (fun t => t == 16 || t == 23) = true := by decide +kernel
theorem covers_mpos_recv : Covers B_MPOS false (fun t => t == 23) = true := by decide +kernel
theorem pub_mpos (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_MPOS s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`MPOS` balances** on every bundle carrying the accepted receipt render (16) and the
accepted outcome Merkle render (23). -/
theorem balancedAt_mpos {cb wb : NearSpec.Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    (h16 : R ⟨16, by decide⟩ = A.rcptRenders.rcpt) (h23 : R ⟨23, by decide⟩ = A.mrkAcc) :
    R.BalancedAt B_MPOS := by
  intro m
  rw [R.sum_tables true _ m _ covers_mpos_send, R.sum_tables false _ m _ covers_mpos_recv,
    pub_mpos, pub_mpos]
  have hf1 : (List.range 25).filter (fun t => t == 16 || t == 23) = [16, 23] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 23) = [23] := by decide
  have t16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput := bundle_tf_eq R 16 _ h16
  have t23 : R.tf 23 = A.mrkAcc.tf := bundle_tf_eq R 23 _ h23
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, t16, t23, Nat.add_zero]
  have := A.receipt_mpos m
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
