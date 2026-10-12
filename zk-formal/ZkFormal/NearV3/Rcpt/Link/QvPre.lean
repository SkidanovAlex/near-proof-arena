import ZkFormal.NearV3.Rcpt.Link.RcptHoldsB
import ZkFormal.NearV3.Qv.Preserve
import ZkFormal.NearV3.Qv.ReceiptPreserve

/-!
# ZkFormal.NearV3.Rcpt.Link.QvPre — the queue reads from the pre-state

The qv AIR authenticates all three main queue reads against one tree (the head-0 record trie,
`Qv.Extract.assemble_native_queue_reads`: `v.Valid ∧ v.Reads t t t`).  The runtime reads the
buffered index after the scheduler write and the yield index after the receipt writes; neither
write touches those keys (`schedStep_find_other`, `ledgerAll_find_other`).  Hence:

* `ledgerAll_find_other` — the ledger never changes a non-account key;
* **`reads_of_pre`** — `v.Reads pre pre pre` (+ `pre.wf`) ⇒ `v.Reads pre mid (T (valsAt n))`;
* **`mainRun_of_holdsP_pre`** — `mainRun_of_holdsP_route` with the queue-read premise in the
  pre-state form the qv AIR provides.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3

theorem ledgerAll_find_other (ctx : ApplyCtx) (key : List Nat) :
    ∀ (rs : List Receipt) (acc acc' : Acc), ledgerAll ctx acc rs = some acc' →
      (∀ r ∈ rs, key ≠ accountKeyPath r.receiverId) → acc'.trie.find key = acc.trie.find key
  | [], acc, acc', h, _ => by simp only [ledgerAll, Option.some.injEq] at h; subst h; rfl
  | r :: rs, acc, acc', h, hk => by
    simp only [ledgerAll] at h
    split at h
    · cases h
    · next a hstep =>
      have ih := ledgerAll_find_other ctx key rs a acc' h (fun r' hr' => hk r' (by simp [hr']))
      rw [ih]
      unfold ledgerStep at hstep
      split at hstep
      · split at hstep
        · next a' ha =>
          cases hstep
          exact Qv.applySystemReceipt_find_other ha key (hk r (by simp))
        · cases hstep
      · exact Qv.applyReceipt_find_other hstep key (hk r (by simp))

/-- **The main queue reads from the pre-state reads.** -/
theorem reads_of_pre {ctx : ApplyCtx} {pre mid : PTrie} {so : SchedOut} {v : Qv.MainValues}
    {M : RunModel} (hpw : pre.wf = true) (hs : schedStep prims ctx pre = .ok (mid, so))
    (hT0 : M.T (M.valsAt 0) = mid) (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOk3 ctx r)
    (hR : v.Reads pre pre pre) : v.Reads pre mid (M.T (M.valsAt M.rs.length)) := by
  obtain ⟨hd, hb, hg, hy⟩ := hR
  refine ⟨hd, by rw [Qv.schedStep_buffered_read hpw hs]; exact hb, ?_, ?_⟩
  · intro s hss
    obtain ⟨value, hv⟩ := hg s hss
    exact ⟨value, by rw [Qv.schedStep_group_read hpw hs]; exact hv⟩
  · have hled := M.ledgerAll_eq ctx hT hok
    have hfo := ledgerAll_find_other ctx keyYieldIdx M.rs _ _ hled
      (fun r _ => Qv.yield_ne_account r.receiverId)
    have h0 : (M.accAt ctx 0).trie = mid := by simp [RunModel.accAt, hT0]
    have hn : (M.accAt ctx M.rs.length).trie = M.T (M.valsAt M.rs.length) := rfl
    rw [← hn, hfo, h0, Qv.schedStep_find_other hpw hs keyYieldIdx (by decide)]
    exact hy

/-- **The receipt core with the queue reads in pre-state form** (`v.Valid ∧ v.Reads pre pre pre`,
as `Qv.Extract.assemble_native_queue_reads` gives them on the head-0 tree, and `pre.wf`). -/
theorem mainRun_of_holdsP_pre {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length)
    {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (S : ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values others shaS shaR) :
    ∃ pc, prepClaim cb = .ok pc ∧
      ∀ (base : Nat → Bytes) (Tf : (Nat → Bytes) → PTrie) (pre mid : PTrie) (so : SchedOut)
        (v : Qv.MainValues),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →
        pre.wf = true →
        v.Valid → v.Reads pre pre pre →
        (∀ x ∈ flatR r.lists, pc.ctxB2.layout.shardOf (toBytes x.v) = pc.ctxB2.own) →
        (∀ o, Scheduler.indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some o →
          ∀ k, (hk : k < pc.ctxB2.layout.shardIds.length) →
          ZkFormal.NearV3.Sched.fwdDemand p.fwd (o * pc.ctxB2.layout.shardIds.length + k) ≤
            so.grant pc.ctxB2.own pc.ctxB2.layout.shardIds[k]) →
        applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  obtain ⟨pc, hc, K⟩ := mainRun_of_holdsP_route hp hsz hH T W hn S
  obtain ⟨pc', hc', hb, hgp⟩ := gasPrice_pub oh hp
  rw [hc] at hc'
  cases hc'
  have H := recHyp_of hp hsz hH T W S
  refine ⟨pc, hc, ?_⟩
  intro base Tf pre mid so v L hpw hv hR hroute hL
  have hR' := reads_of_pre (M := recModel r.lists r.accts base Tf) hpw L.sched L.init L.trie
    (rcptOk_all H base Tf pc.ctxB2 hgp) hR
  rw [recModel_length] at hR'
  exact K base Tf pre mid so v L hv hR' hroute hL

end ZkFormal.NearV3.RcptLink
