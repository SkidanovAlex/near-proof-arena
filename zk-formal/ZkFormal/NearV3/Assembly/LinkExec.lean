import ZkFormal.NearV3.Assembly.LinkMainLink
import ZkFormal.NearV3.Assembly.LinkDelayed
import ZkFormal.NearV3.Assembly.LinkPrepCtx

/-!
# ZkFormal.NearV3.Assembly.LinkExec — the `executions` field with the trie / record premises closed

`LinkMain.executions_of` with, from `HoldsP`: `PostPreOff0` (`LinkPostRec.postPreOff0_holds`),
`DelayedCovered` (`LinkDelayed.delayedCovered_holds`), `hcov` (`LinkTrieOk.hcov_of` with the qv
reads of `RcptLink.mainRun_of_holdsP_q`), `hbs` (same), `hrun` (`mainRun_of_holdsP_q` with
`LinkMainLink.mainTrieLink_holds`, the prepared context `LinkPrepCtx`), `hpost`
(`LinkPostRec.post_holds`).  Remaining premises (exact):

* `hroute` — every applied receipt is routed to the own shard (blocked on table 16's `q < 128`
  check, lane v3-rcpt-sound's log);
* `hfwd` — the AIR's link-indexed forwarding demand is within the scheduler grant of instance `0`;
* `hhdr` — the header semantics of the resulting main execution.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkExec

open ZkFormal.NearV3 ZkFormal.NearV3.RcptLink LinkImplicit LinkTrieFam

theorem applied_eq {x : ExtV3} {r : V3Records} (hxr : x.receipts = r.lists) :
    x.applied = (rv r.lists).map RcptV.toReceipt := by
  simp only [ExtV3.applied, hxr, rv, flatR, List.map_flatMap, List.map_map]
  rfl

/-- **`executions`** (`ExtFieldsV3` of the reconstruction) from `HoldsP`, routing, the forwarding
check and the header semantics. -/
theorem executions_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map UpsRows.upsE)) (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    (hroute : ∀ pc, NearSpecV3.prepClaim cb = .ok pc →
      ∀ y ∈ flatR r.lists, pc.ctxB2.layout.shardOf (toBytes y.v) = pc.ctxB2.own)
    (hfwd : ∀ pc, NearSpecV3.prepClaim cb = .ok pc → ∀ (h0 : 0 < p.sched.length) o,
      NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o →
      ∀ oi, NearSpecV3.Scheduler.indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some oi →
        ∀ j, (hj : j < pc.ctxB2.layout.shardIds.length) →
        ZkFormal.NearV3.Sched.fwdDemand p.fwd (oi * pc.ctxB2.layout.shardIds.length + j) ≤
          (schedOut o).grant pc.ctxB2.own pc.ctxB2.layout.shardIds[j])
    (hhdr : ∀ bs out, (∃ v, (Fpre r 0).find NearSpecV3.keyBufferedIdx = some v ∧
        NearSpecV3.bufferedShards v = .ok bs) →
      NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (Fpre r 0) x.applied = .ok out →
      HeaderSemanticsV3 k h p ⟨block, previous, bs, Fpre r 0, out⟩ k.H.prevStateRoot) :
    ∃ m last, m.Valid k x ∧ ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k h p m last := by
  obtain ⟨pc, bs, hc, hbs, hfix, hgrp, K⟩ := mainRun_of_holdsP_q hp hsz hH T W hn
  -- the main instance's scheduler input
  obtain ⟨pc', hc', hb⟩ := Sched.bind_ok hp
  rw [hc] at hc'; cases hc'
  have hsched : p.sched = pc.sched := (prepBody_shape hb).2.1
  obtain ⟨h0c, hsp⟩ := LinkPrepCtx.prepClaim_sched0 hc
  have h0 : 0 < p.sched.length := by rw [hsched]; exact h0c
  have hctx : NearSpecV3.schedPub pc.ctxB2 = some p.sched[0] := by
    rw [hsp]; congr 1; simp only [hsched]
  obtain ⟨o, Q, ho, ML⟩ := LinkMainLink.mainTrieLink_holds hp hsz hH T W h0 hctx
  have hrun0 := K (preV r) (Tf r 0 (schedOut o).state) Q (schedOut o) ML (hroute pc hc)
    (hfwd pc hc h0 o ho)
  -- the prepared context is the walked chunk's
  have hC := (LinkPrepCtx.prepClaim_context_of
    (m := ⟨block, previous, bs, Fpre r 0,
      (recModel r.lists r.accts (preV r) (Tf r 0 (schedOut o).state)).mainOut pc.ctxB2⟩)
    (stateWitnessOfV3 k x) hc hw hmb hmp).ctx
  simp only [MainExecutionV3.ctx] at hC
  rw [hC, ← applied_eq hxr] at hrun0
  apply LinkMain.executions_of hp hsz hH T W hw (LinkPostRec.postPreOff0_holds hp hsz hH T W)
    (LinkDelayed.delayedCovered_holds hp hsz hH T W) hxn hxv hxh hmb hmp
    (LinkTrieOk.hcov_of hp hsz hH T W h0 hxr hfix hgrp) hbs hrun0
  · exact LinkPostRec.post_holds hp hsz hH T W hxh h0 ho
  · exact hhdr bs _ hbs hrun0

end LinkExec

end ZkFormal.NearV3.Assembly
