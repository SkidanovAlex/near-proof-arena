import ZkFormal.NearV3.Assembly.LinkFwd

/-!
# ZkFormal.NearV3.Assembly.LinkHdr — the claim-level fields of `HeaderSemanticsV3`

`prepBody`'s 3.7 header comparison (`prepBody_hdr`) and the prepared context
(`LinkPrepCtx.prepClaim_context_of`: `pc.H = k.H`, gas limit, congestion, allowed shard, RS
parameters) give the fields of `HeaderSemanticsV3` that do not depend on the run:
`stateRoot` (by `rfl` at `last = k.H.prevStateRoot`), `proposals`, `gasLimit`, `congestion`,
`bandwidthRequests`, `split`, `txRoot`, `preparedBody`, `encoded`, and the claim halves of
`gasUsed` (`k.H.prevGasUsed = h.n · G`) and `outgoingRoot` (`= outgoingReceiptsRoot k.L refunds`
for `decodeBody h.body = .ok refunds`).  **`hhdr_of`** reduces `hhdr` to the run fields
(`RunHdr`, lane v3-rcpt-sound).
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3 Sched

namespace LinkHdr

/-- The claim/hint checks of `prepBody`. -/
structure BodyHdr (pc : PrepC) (h : Hint) (p : Prep) : Prop where
  proposals : pc.H.proposals.isEmpty = true
  gasLimit : pc.H.gasLimit = pc.hdr.gasLimit
  gasUsed : pc.H.prevGasUsed = h.n * Params.G
  outgoing : ∃ refunds, decodeBody h.body = .ok refunds ∧
    pc.H.prevOutgoingReceiptsRoot = outgoingReceiptsRoot pc.L refunds
  congestion : pc.H.congestion = { pc.ownCongestion with allowedShard := pc.allowed }
  bw : pc.H.bwRequests.isEmpty = true
  split : pc.H.proposedSplit.isNone = true
  txRoot : pc.H.txRoot = zeroHash32
  encoded : encodedMerkleRoot pc.rsData pc.rsTotal h.body = some (pc.H.encodedMerkleRoot, pc.H.encodedLength)
  body : p.body = h.body

theorem check_ok {b : Bool} {m : String} {u : Unit} (h : check b m = .ok u) : b = true := by
  unfold check at h; split at h <;> simp_all

theorem prepBody_hdr {pc : PrepC} {hint : Hint} {p : Prep} (h : prepBody pc hint = .ok p) :
    BodyHdr pc hint p := by
  unfold prepBody at h
  obtain ⟨refunds, hr, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, c1, h⟩ := bind_ok h
  obtain ⟨_, c2, h⟩ := bind_ok h
  obtain ⟨_, c3, h⟩ := bind_ok h
  obtain ⟨_, c4, h⟩ := bind_ok h
  obtain ⟨_, c5, h⟩ := bind_ok h
  obtain ⟨_, c6, h⟩ := bind_ok h
  obtain ⟨_, c7, h⟩ := bind_ok h
  obtain ⟨_, c8, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · rename_i he; obtain ⟨_, he', -⟩ := bind_ok h; cases he'
  · rename_i emr len he
    obtain ⟨_, c9, h⟩ := bind_ok h
    obtain ⟨_, c10, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have := check_ok c1; have := check_ok c2; have := check_ok c3; have := check_ok c4
    have := check_ok c5; have := check_ok c6; have := check_ok c7; have := check_ok c8
    have := check_ok c9; have := check_ok c10
    simp only [beq_iff_eq] at *
    exact ⟨by assumption, by assumption, by assumption, ⟨refunds, hr, by assumption⟩, by assumption,
      by assumption, by assumption, by assumption, by subst_vars; rw [he], rfl⟩

/-- **The run fields of `HeaderSemanticsV3`** (lane v3-rcpt-sound), for the main run's output
`out` on the hint `h`. -/
structure RunHdr (k : WalkD0) (h : Hint) (out : MainOut) : Prop where
  outcomeRoot : k.H.prevOutcomeRoot = NearSpec.outcomeRoot out.outcomes
  gasUsed : out.gasUsed = h.n * Params.G
  tokensBurnt : k.H.prevBalanceBurnt = out.tokensBurnt
  outgoing : ∀ refunds, decodeBody h.body = .ok refunds → out.outgoing = refunds
  body : h.body = u32 0 ++ encodeReceipts out.outgoing

/-- **`hhdr`** from the claim checks and the run fields. -/
theorem hhdr_of {cb : Bytes} {h : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb h = .ok p) (hw : walkD0 cb = .ok k)
    {block previous : Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous) {bs : List Nat} {pre : PTrie} {out : MainOut}
    (R : RunHdr k h out) :
    HeaderSemanticsV3 k h p ⟨block, previous, bs, pre, out⟩ k.H.prevStateRoot := by
  obtain ⟨pc, hc, hb⟩ := bind_ok hp
  have B := prepBody_hdr hb
  have C := LinkPrepCtx.prepClaim_context_of (m := ⟨block, previous, bs, pre, out⟩)
    (stateWitnessOfV3 k ⟨[], [], [], [], []⟩) hc hw hmb hmp
  obtain ⟨refunds, hr, ho⟩ := B.outgoing
  have hH := C.header
  refine ⟨rfl, R.outcomeRoot, hH ▸ B.proposals, ?_, ?_, R.tokensBurnt, ?_, ?_, hH ▸ B.bw,
    hH ▸ B.split, hH ▸ B.txRoot, R.body, B.body, ?_⟩
  · rw [← hH, B.gasLimit, C.gasLimit]
  · rw [← hH, B.gasUsed, R.gasUsed]
  · rw [← hH, ho, C.layout, R.outgoing refunds hr]
  · rw [← hH, B.congestion, C.congestion, C.allowed, hH]
  · rw [← hH, ← C.rsData, ← C.rsTotal]; exact B.encoded

/-- **`executions`** from `HoldsP`, the routing premise and the run fields `RunHdr`. -/
theorem executions_run {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : ZkFormal.V2.HoldsP nearAirV3
      (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k)
    (hn : h.n = (ZkFormal.NearV3.flatR r.lists).length)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = LinkImplicit.xHeads (r.ups.map ZkFormal.NearV3.UpsRows.upsE)) (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    (hroute : ∀ pc, NearSpecV3.prepClaim cb = .ok pc →
      ∀ y ∈ ZkFormal.NearV3.flatR r.lists, pc.ctxB2.layout.shardOf (ZkFormal.Near.toBytes y.v) = pc.ctxB2.own)
    (hrun : ∀ bs out, (∃ v, (LinkImplicit.Fpre r 0).find NearSpecV3.keyBufferedIdx = some v ∧
        NearSpecV3.bufferedShards v = .ok bs) →
      NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (LinkImplicit.Fpre r 0) x.applied = .ok out → RunHdr k h out) :
    ∃ m last, m.Valid k x ∧ ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k h p m last :=
  LinkFwd.executions_holds' hp hsz hH T W hw hn hxn hxv hxh hxr hmb hmp hroute
    (fun bs out hb ha => hhdr_of hp hw hmb hmp (hrun bs out hb ha))

end LinkHdr

end ZkFormal.NearV3.Assembly
