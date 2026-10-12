import ZkFormal.NearV3.Rcpt.Link.QvAssemble
import ZkFormal.NearV3.Assembly.LinkMain
import ZkFormal.NearV3.Assembly.LinkTrieFam

/-!
# ZkFormal.NearV3.Rcpt.Link.QvMain — the receipt core at the trie link's pre trie, queue reads discharged

`walkHyp_holdsP`: the walk hypothesis over `allWalks r.walks r.ups` from `HoldsP`
(`UpsRows.ups_walkHyp_22` with the trie link's balances, `keynibOk_of`, `recBytes_of`).

`queue_main_holdsP`: the qv reads from `HoldsP` alone, on `Fpre r 0` (`= queueTree r.nodes r.values
r.heads 0` by definition): `v.Valid`, `v.Reads (Fpre r 0) (Fpre r 0) (Fpre r 0)`.

**`mainRun_of_holdsP_q`**: `QvPre.mainRun_of_holdsP_pre` at `pre := Fpre r 0` with `pre.wf`,
`v.Valid` and the queue reads discharged; it also exports, for lane v3-link's
`LinkMain.executions_of`, the buffered-shard list `bs` with `hbs` and the queue-key part of `hcov`
(`keyDelayedIdx`, `keyBufferedIdx`, `keyYieldIdx`, `keyGroupsData s` for `s ∈ bs` are found in
`Fpre r 0`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3

/-- The walk hypothesis of all walks (`walkV3`'s and the ups segments') from `HoldsP`. -/
theorem walkHyp_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    Walk3.WalkHyp (Link3.vpos (Link3.vid0 r.values)) r.nodes (Link3.valsOf3 r.nodes r.values) r.heads
      (UpsRows.allWalks r.walks r.ups) := by
  have L := trieLink_of hp hsz hH T W
  exact UpsRows.ups_walkHyp_22 W.nodes W.heads W.values W.walks W.walkSteps W.ups L.parent L.vparent
    L.edge L.bmap (LinkKeynib.keynibOk_of hp hsz hH T W) (recBytes_of W L) _

/-- **The main queue reads on the pre record tree, from `HoldsP`.** -/
theorem queue_main_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length) :
    ∃ v : Qv.MainValues, v.Valid ∧
      v.Reads (LinkImplicit.Fpre r 0) (LinkImplicit.Fpre r 0) (LinkImplicit.Fpre r 0) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨q, ss, hV, hR⟩ := queue_reads_holdsP hp hH T W hn (shaHyp_holds hp hsz hH T W) L.chain
    (walkHyp_holdsP hp hsz hH T W) (fun w hw => List.mem_append_left _ hw)
  exact ⟨_, hV, hR⟩

/-- **The receipt core at `pre := Fpre r 0`**, queue reads, `v.Valid` and `pre.wf` discharged;
with the buffered-shard list `bs` (`hbs`) and the queue-key coverage of `Fpre r 0`. -/
theorem mainRun_of_holdsP_q {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length) :
    ∃ pc bs, prepClaim cb = .ok pc ∧
      (∃ v, (LinkImplicit.Fpre r 0).find keyBufferedIdx = some v ∧ bufferedShards v = .ok bs) ∧
      (∀ key ∈ [keyDelayedIdx, keyBufferedIdx, keyYieldIdx] ++ bs.map keyGroupsData,
        (LinkImplicit.Fpre r 0).find key ≠ none) ∧
      ∀ (base : Nat → Bytes) (Tf : (Nat → Bytes) → PTrie) (mid : PTrie) (so : SchedOut),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 (LinkImplicit.Fpre r 0) mid so →
        (∀ x ∈ flatR r.lists, pc.ctxB2.layout.shardOf (toBytes x.v) = pc.ctxB2.own) →
        (∀ o, Scheduler.indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some o →
          ∀ k, (hk : k < pc.ctxB2.layout.shardIds.length) →
          ZkFormal.NearV3.Sched.fwdDemand p.fwd (o * pc.ctxB2.layout.shardIds.length + k) ≤
            so.grant pc.ctxB2.own pc.ctxB2.layout.shardIds[k]) →
        applyNewChunk prims pc.ctxB2 (LinkImplicit.Fpre r 0) ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨pc, hc, K⟩ := mainRun_of_holdsP_pre hp hsz hH T W hn (shaHyp_holds hp hsz hH T W)
  obtain ⟨v, hV, hR⟩ := queue_main_holdsP hp hsz hH T W hn
  have hwf := LinkMain.Fpre_wf W L (Nat.zero_le _)
  obtain ⟨hd, hb, hg, hy⟩ := hR
  refine ⟨pc, v.shards, hc, ⟨v.buffered, hb, (Qv.bufferedShards_iff _ _).mpr hV.2.1⟩, ?_,
    fun base Tf mid so M => K base Tf _ mid so v M hwf hV ⟨hd, hb, hg, hy⟩⟩
  intro key hk
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hk
  rcases hk with rfl | rfl | rfl | ⟨s, hs, rfl⟩
  · rw [hd]; simp
  · rw [hb]; simp
  · rw [hy]; simp
  · obtain ⟨w, hw⟩ := hg s hs
    rw [hw]; simp

end ZkFormal.NearV3.RcptLink
