import ZkFormal.NearV3.Rcpt.Link.RcptRoute
import ZkFormal.NearV3.Assembly.LinkHdr
import ZkFormal.NearV3.Candidates.ReceiptPreparedFields

/-!
# ZkFormal.NearV3.Rcpt.Link.RcptRunHdr — the run fields of the header semantics (`LinkHdr.RunHdr`)

* `mainOut_of_run` — every `out` of the main `applyNewChunk` at the walked block context is the
  ledger model's `mainOut` (determinism, with `mainRun_of_holdsP_r`, `LinkMainLink.mainTrieLink_holds`,
  `LinkFwd.hfwd_holds`, `LinkPrepCtx`);
* `decodeBody_shape` — `decodeBody b = .ok rs → b = u32 0 ++ u32 |rs| ++ b.drop 8`;
* `body_tail` — `h.body.drop 8` is the model's refunds, encoded;
* `walkD0_H`, `decodeChunkInner_burnt` — the claim's balance burnt is `< 2^128`;
* `burnt_pub` — `k.H.prevBalanceBurnt = leN' (pubBytes pub PH_BURNT 16)`;
* **`runHdr_of`** — `RunHdr k h out` given the outcome-root premise `hroot`.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Sched

/-! ## Body shape -/

theorem pMany_length {α : Type} {p : NearSpecV3.P α} :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes), pMany p n bs = .ok (xs, rest) → xs.length = n
  | 0, bs, xs, rest, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | n + 1, bs, xs, rest, h => by
    unfold pMany at h
    obtain ⟨⟨a, b1⟩, -, h⟩ := bind_ok h
    obtain ⟨⟨as, b2⟩, h2, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_cons, pMany_length n _ _ _ h2]

theorem decodeBody_shape {b : Bytes} {rs : List Receipt} (hd : decodeBody b = .ok rs) :
    b = u32 0 ++ u32 rs.length ++ b.drop 8 := by
  unfold decodeBody at hd
  obtain ⟨⟨ntx, b1⟩, h1, hd⟩ := bind_ok hd
  dsimp only at hd
  split at hd
  · cases hd
  next hntx =>
  obtain ⟨⟨rs', b2⟩, hv, hd⟩ := bind_ok hd
  dsimp only at hd
  split at hd
  · cases hd
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  subst hd
  unfold pVec at hv
  obtain ⟨⟨n, b3⟩, hn, hv⟩ := bind_ok hv
  have e1 := (ReexecV3D0.lift_readLE_inv (n := 4) h1).1
  have e2 := (ReexecV3D0.lift_readLE_inv (n := 4) hn).1
  have h0 : ntx = 0 := by simpa using hntx
  have hl := pMany_length _ _ _ _ hv
  subst h0
  rw [hl]
  have hb3 : b.drop 8 = b3 := by
    rw [e1, e2, ← List.append_assoc, List.drop_left' (by simp [leN_length])]
  rw [hb3, e1, e2]
  rfl

/-- **The body's tail is the model's refunds, encoded** (the `ht` of `refunds_of`). -/
theorem body_tail {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {pc : PrepC} (hc : prepClaim cb = .ok pc) (hb : prepBody pc h = .ok p)
    (hgp : pc.ctxB2.gasPrice =
      leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16))
    (base : Nat → NearSpec.Bytes) (Tf : (Nat → NearSpec.Bytes) → PTrie) :
    h.body.drop 8 = concatAll
      (((recModel r.lists r.accts base Tf).accAt pc.ctxB2 (flatR r.lists).length).refunds.map Receipt.encode) := by
  have hrfid : ∀ q, q < (flatR r.lists).length → ((flatR r.lists).getD q default).hr = true →
      toBytes ((flatR r.lists).getD q default).rfid =
        receiptIdFrom (toBytes ((flatR r.lists).getD q default).rid) pc.ctxB2.height 0 := by
    intro q hq hhr
    rw [getD_eq_getElem' _ default hq] at hhr ⊢
    rw [rfid_sha hp hsz hH T W hq hhr, toBytes_map_toNat', receiptIdFrom, ridPre, toBytes_append,
      toBytes_append, height_pub oh hp hc hb, zeros8_eq]
  obtain ⟨hs, -⟩ := rfStream_refunds H base Tf pc.ctxB2 hgp hrfid
  rw [← hs, rfStream_body hp hsz hH T W, toBytes_map_toNat',
    Rcpt.Candidates.NodePostUpdate.prepD0_body_eq hp]

/-! ## Balance burnt -/

set_option maxHeartbeats 4000000 in
theorem pChunkInner_burnt {b r : Bytes} {H : ChunkInner} (h : pChunkInner b = .ok (H, r)) :
    H.prevBalanceBurnt < 256 ^ 16 := by
  unfold pChunkInner at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simpa only [Params.two128] using ZkFormal.V3.pU128_lt (by assumption)

theorem decodeChunkInner_burnt {b : Bytes} {H : ChunkInner} (h : decodeChunkInner b = .ok H) :
    H.prevBalanceBurnt < 256 ^ 16 := by
  unfold decodeChunkInner at h
  obtain ⟨⟨ci, rest⟩, hci, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact pChunkInner_burnt hci

set_option maxHeartbeats 4000000 in
theorem walkD0_H {cb : Bytes} {k : WalkD0} (hw : walkD0 cb = .ok k) :
    ∃ c : NearSpecV3.Claim, decodeChunkInner c.chunkInner = .ok k.H := by
  unfold walkD0 at hw
  obtain ⟨c, -, hw⟩ := bind_ok hw
  obtain ⟨H, hH, hw⟩ := bind_ok hw
  refine ⟨c, ?_⟩
  repeat' (first
    | (obtain ⟨_, _, hw⟩ := bind_ok hw)
    | (split at hw)
    | (dsimp only at hw))
  all_goals try (cases hw; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hw
    subst hw
    exact hH

/-- **The public balance-burnt bytes are the claim's balance burnt.** -/
theorem burnt_pub {cb : Bytes} {h : Hint} {p : Prep} (oh : Nat) (hp : prepD0 cb h = .ok p)
    {k : WalkD0} (hw : walkD0 cb = .ok k) {m : MainExecutionV3}
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous) :
    (∀ i, i < 16 → pubNat (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) (PH_BURNT + i) < 256) ∧
    k.H.prevBalanceBurnt =
      leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_BURNT 16) := by
  obtain ⟨pc, hc, hb⟩ := bind_ok hp
  have hroots := ZkFormal.NearV3.Assembly.prepD0_roots hp
  have C := LinkPrepCtx.prepClaim_context_of (m := m)
    (stateWitnessOfV3 k ⟨[], [], [], [], []⟩) hc hw hmb hmp
  have hg : p.hdr.balanceBurnt = k.H.prevBalanceBurnt := by
    rw [(Candidates.ReceiptPreparedFields.body_fields hb).2.2.2,
      (Candidates.ReceiptPreparedFields.claim_fields hc).2, C.header]
  obtain ⟨c, hci⟩ := walkD0_H hw
  have hlt := decodeChunkInner_burnt hci
  have hpb : pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_BURNT 16 =
      (u128 p.hdr.balanceBurnt).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes, u128, leN_length])
    intro i h1 h2
    have hi : i < 16 := by simpa [pubBytes] using h1
    simp only [pubBytes, List.getElem_map, List.getElem_range]
    rw [pubNat_prepared, Candidates.ReceiptPreparedFields.burnt_byte p oh i hroots hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [u128, leN_length] using hi)]
    rfl
  refine ⟨fun i _ => by rw [pubNat_prepared]; exact UInt8.toNat_lt _, ?_⟩
  rw [hpb, hg, ZkFormal.Near.Link.leN'_eq]
  have : toBytes ((u128 k.H.prevBalanceBurnt).map UInt8.toNat) = u128 k.H.prevBalanceBurnt := by
    simp [toBytes, List.map_map, Function.comp_def]
  rw [this, u128, NearSpec.leNat_leN 16 _ hlt]

/-! ## The main output -/

/-- **Every main-run output at the walked block context is the ledger model's `mainOut`.** -/
theorem mainOut_of_run {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous) {out : MainOut}
    (ha : NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (LinkImplicit.Fpre r 0) x.applied = .ok out) :
    ∃ pc base Tf, prepClaim cb = .ok pc ∧ prepBody pc h = .ok p ∧
      pc.ctxB2 = NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice ∧
      out = (recModel r.lists r.accts base Tf).mainOut pc.ctxB2 := by
  obtain ⟨pc, -, hc, -, -, -, K⟩ := mainRun_of_holdsP_r hp hsz hH T W hn
  obtain ⟨pc', hc', hb⟩ := bind_ok hp
  rw [hc] at hc'; cases hc'
  have hsched : p.sched = pc.sched := (prepBody_shape hb).2.1
  obtain ⟨h0c, hsp⟩ := LinkPrepCtx.prepClaim_sched0 hc
  have h0 : 0 < p.sched.length := by rw [hsched]; exact h0c
  have hctx : NearSpecV3.schedPub pc.ctxB2 = some p.sched[0] := by
    rw [hsp]; congr 1; simp only [hsched]
  obtain ⟨o, Q, ho, ML⟩ := LinkMainLink.mainTrieLink_holds hp hsz hH T W h0 hctx
  have hrun0 := K (LinkTrieFam.preV r) (LinkTrieFam.Tf r 0 (schedOut o).state) Q (schedOut o) ML
    (fun oi hoi j hj => LinkFwd.hfwd_holds hp hsz hH T W pc hc h0 o ho oi hoi j hj)
  have hC := (LinkPrepCtx.prepClaim_context_of
    (m := ⟨block, previous, [], LinkImplicit.Fpre r 0, out⟩)
    (stateWitnessOfV3 k x) hc hw hmb hmp).ctx
  simp only [MainExecutionV3.ctx] at hC
  refine ⟨pc, LinkTrieFam.preV r, LinkTrieFam.Tf r 0 (schedOut o).state, hc, hb, hC, ?_⟩
  rw [hC, ← LinkExec.applied_eq hxr, ha] at hrun0
  rw [hC]; exact Except.ok.inj hrun0

/-! ## The run fields -/

/-- **`RunHdr`** (the run fields of `HeaderSemanticsV3`) from `HoldsP`, given the outcome root
`hroot` of the model's outcomes. -/
theorem runHdr_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    (hroot : ∀ pc, prepClaim cb = .ok pc → ∀ base Tf,
      k.H.prevOutcomeRoot = outcomeRoot ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2).outcomes)
    (out : MainOut)
    (ha : NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (LinkImplicit.Fpre r 0) x.applied = .ok out) :
    LinkHdr.RunHdr k h out := by
  obtain ⟨pc, base, Tf, hc, hb, -, rfl⟩ := mainOut_of_run hp hsz hH T W hw hn hxr hmb hmp ha
  obtain ⟨pc', hc', hb', hgp⟩ := gasPrice_pub oh hp
  rw [hc] at hc'; cases hc'
  have H := recHyp_of hp hsz hH T W (shaHyp_holds hp hsz hH T W)
  have hlen : (recModel r.lists r.accts base Tf).rs.length = (flatR r.lists).length := recModel_length
  obtain ⟨refunds, hd, -⟩ := (LinkHdr.prepBody_hdr hb).outgoing
  have hrf := refunds_of hp hsz hH T W H hc hb hgp base Tf hd
  have hout : ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2).outgoing = refunds := by
    simp only [RunModel.mainOut]; rw [hlen]; exact hrf
  refine ⟨hroot pc hc base Tf, ?_, ?_, ?_, ?_⟩
  · simp only [RunModel.mainOut, RunModel.accAt]; rw [hlen, hn]
  · obtain ⟨hbb, hpub⟩ := burnt_pub (m := ⟨block, previous, [], LinkImplicit.Fpre r 0,
      (recModel r.lists r.accts base Tf).mainOut pc.ctxB2⟩) oh hp hw hmb hmp
    obtain ⟨toks, -, h0, hwf, hfin⟩ := W.lists.toks
    have hw' : ∀ q, q < (flatR r.lists).length →
        ((flatR r.lists).getD q default).Wf q
          (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16)
          (toks.getD q 0) (toks.getD (q + 1) 0) := by
      intro q hq
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      exact hwf q hq
    rw [hpub, ← hfin hbb, ← tok_inv H base Tf pc.ctxB2 hgp h0 hw' _ (Nat.le_refl _)]
    simp only [RunModel.mainOut, RunModel.accAt]; rw [hlen]
  · intro refunds' hd'
    rw [hd] at hd'; cases hd'; exact hout
  · rw [hout]
    have hs := decodeBody_shape hd
    have ht := body_tail hp hsz hH T W H hc hb hgp base Tf
    rw [hrf] at ht
    rw [hs, ht]
    simp only [encodeReceipts, List.append_assoc]

end ZkFormal.NearV3.RcptLink
