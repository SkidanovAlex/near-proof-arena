import ZkFormal.NearV3.Rcpt.Link.RfEnc
import ZkFormal.NearV3.Rcpt.Link.RcptHolds
import ZkFormal.NearV3.Rcpt.Link.ValBytes
import ZkFormal.NearV3.Rcpt.Link.FwdLinks

/-!
# ZkFormal.NearV3.Rcpt.Link.RcptHoldsB — `RecBytes` and the refund identity discharged

* `rfStream_refunds` — under `RecHyp` (and the refund-id digests), the refund stream is the
  model's refund list, encoded, and every model refund has the `pRefund` shape;
* `decodeBody_tail` — `decodeBody b = .ok rs` and `b.drop 8 = concatAll (ms.map encode)` (with
  `ms` of refund shape) force `rs = ms` (`pRefund` is prefix-free on refund-shaped receipts);
* **`refunds_of`** — the run's refunds are `decodeBody h.body`'s (`hrf`);
* **`mainRun_of_holdsP_sha`** — `mainRun_of_holdsP` with `RecBytes` (`preB_of` under the trie
  link's `ShaHyp`, `burntBytes`, `ramtBytes`) and `hrf` discharged;
* **`mainRun_of_holdsP_fwd`** — moreover `hsz` from the AIR's link-indexed forwarding check on
  `p.fwd` (`FwdLinks.hsz_of_links`, A12 from `prepClaim_layout_wf`), given `own ∈ shardIds`.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Sched

theorem concatAll_map {α : Type} (F : α → Bytes) :
    ∀ l : List α, concatAll (l.map F) = l.flatMap F
  | [] => rfl
  | x :: l => by rw [List.map_cons, concatAll, concatAll_map F l, List.flatMap_cons]

theorem toBytes_flatMap' {α : Type} (f : α → List Nat) (l : List α) :
    toBytes (l.flatMap f) = l.flatMap (fun a => toBytes (f a)) := by
  simp only [toBytes, List.map_flatMap]

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (h : RecHyp pub ls as)
  (base : Nat → NearSpec.Bytes) (T : (Nat → NearSpec.Bytes) → PTrie)
include h

/-- **The refund stream is the model's refunds, encoded.** -/
theorem rfStream_refunds (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    (hrfid : ∀ q, q < (flatR ls).length → ((flatR ls).getD q default).hr = true →
      toBytes ((flatR ls).getD q default).rfid = receiptIdFrom (toBytes ((flatR ls).getD q default).rid) ctx.height 0) :
    toBytes (rfStream ls) =
      concatAll (((recModel ls as base T).accAt ctx (flatR ls).length).refunds.map Receipt.encode) ∧
    ∀ m ∈ ((recModel ls as base T).accAt ctx (flatR ls).length).refunds, ZkFormal.V3.refundShape m = true := by
  have hacc : ((recModel ls as base T).accAt ctx (flatR ls).length).refunds =
      (List.range (flatR ls).length).flatMap ((recModel ls as base T).refundOf ctx) := rfl
  rw [hacc]
  refine ⟨?_, ?_⟩
  · rw [concatAll_flatMap, concatAll_map, rfStream, ← range_flatMap_getD rfS default (flatR ls),
      toBytes_flatMap']
    apply ZkFormal.Near.Link.flatMap_congr'
    intro q hq
    have hq' := List.mem_range.mp hq
    exact (rfS_refundOf h base T ctx hgp hq' (hrfid q hq')).1
  · intro m hm
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hm
    have hq' := List.mem_range.mp hq
    exact (rfS_refundOf h base T ctx hgp hq' (hrfid q hq')).2 m hm

end Hyp

/-! ## Decoding the body -/

theorem borshBytes_length_ge (a : Bytes) : 4 ≤ (borshBytes a).length := by
  simp [borshBytes, u32, leN_length]

theorem pRefund_nil (x : Receipt × Bytes) : pRefund [] ≠ .ok x := by
  intro hx
  unfold pRefund at hx
  obtain ⟨⟨pred, r⟩, ha, -⟩ := bind_ok hx
  have := congrArg List.length (pAccountId_bytes ha)
  simp only [List.length_nil, List.length_append] at this
  have := borshBytes_length_ge pred
  omega

theorem encode_ne_nil (m : Receipt) : m.encode ≠ [] := by
  intro he
  have := congrArg List.length he
  simp only [Receipt.encode, List.length_append, List.length_nil] at this
  have := borshBytes_length_ge m.predecessorId
  omega

theorem pMany_refunds : ∀ (ms : List Receipt), (∀ m ∈ ms, ZkFormal.V3.refundShape m = true) →
    ∀ (n : Nat) (xs : List Receipt),
      pMany pRefund n (concatAll (ms.map Receipt.encode)) = .ok (xs, []) → xs = ms
  | [], _, 0, xs, hp => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at hp; exact hp.1.symm
  | [], _, n + 1, xs, hp => by
    unfold pMany at hp
    obtain ⟨x, hx, -⟩ := bind_ok hp
    exact absurd hx (pRefund_nil x)
  | m :: ms, hs, 0, xs, hp => by
    simp only [pMany, List.map_cons, concatAll, Except.ok.injEq, Prod.mk.injEq] at hp
    exact absurd (List.append_eq_nil_iff.mp hp.2).1 (encode_ne_nil m)
  | m :: ms, hs, n + 1, xs, hp => by
    unfold pMany at hp
    simp only [List.map_cons, concatAll] at hp
    rw [ZkFormal.V3.pRefund_encode m (hs m (by simp))] at hp
    obtain ⟨⟨ys, rest⟩, hy, he⟩ := bind_ok (show (pMany pRefund n (concatAll (ms.map Receipt.encode)) >>=
      fun (p : List Receipt × Bytes) => (pure (m :: p.1, p.2) : Except String (List Receipt × Bytes))) = .ok (xs, []) from hp)
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [pMany_refunds ms (fun x hx => hs x (by simp [hx])) n ys hy]

theorem decodeBody_tail {b : Bytes} {rs ms : List Receipt} (hd : decodeBody b = .ok rs)
    (hs : ∀ m ∈ ms, ZkFormal.V3.refundShape m = true)
    (ht : b.drop 8 = concatAll (ms.map Receipt.encode)) : rs = ms := by
  unfold decodeBody at hd
  obtain ⟨⟨ntx, b1⟩, h1, hd⟩ := bind_ok hd
  dsimp only at hd
  split at hd
  · cases hd
  obtain ⟨⟨rs', b2⟩, hv, hd⟩ := bind_ok hd
  dsimp only at hd
  split at hd
  · cases hd
  next hne =>
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  subst hd
  have hb2 : b2 = [] := by simpa using hne
  subst hb2
  unfold pVec at hv
  obtain ⟨⟨n, b3⟩, hn, hv⟩ := bind_ok hv
  have e1 := (ReexecV3D0.lift_readLE_inv (n := 4) h1).1
  have e2 := (ReexecV3D0.lift_readLE_inv (n := 4) hn).1
  have hb3 : b.drop 8 = b3 := by
    rw [e1, e2, ← List.append_assoc, List.drop_left' (by simp [leN_length])]
  rw [← hb3, ht] at hv
  exact pMany_refunds ms hs n rs' hv

/-! ## The refund identity from the trace -/

/-- **`hrf`**: the run's refunds are the decoded body's. -/
theorem refunds_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {pc : PrepC} (hc : prepClaim cb = .ok pc) (hb : prepBody pc h = .ok p)
    (hgp : pc.ctxB2.gasPrice =
      leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16))
    (base : Nat → NearSpec.Bytes) (Tf : (Nat → NearSpec.Bytes) → PTrie)
    {refunds : List Receipt} (hd : decodeBody h.body = .ok refunds) :
    ((recModel r.lists r.accts base Tf).accAt pc.ctxB2 (flatR r.lists).length).refunds = refunds := by
  have hrfid : ∀ q, q < (flatR r.lists).length → ((flatR r.lists).getD q default).hr = true →
      toBytes ((flatR r.lists).getD q default).rfid =
        receiptIdFrom (toBytes ((flatR r.lists).getD q default).rid) pc.ctxB2.height 0 := by
    intro q hq hhr
    rw [getD_eq_getElem' _ default hq] at hhr ⊢
    rw [rfid_sha hp hsz hH T W hq hhr, toBytes_map_toNat', receiptIdFrom, ridPre, toBytes_append,
      toBytes_append, height_pub oh hp hc hb, zeros8_eq]
  obtain ⟨hs, hshape⟩ := rfStream_refunds H base Tf pc.ctxB2 hgp hrfid
  symm
  apply decodeBody_tail hd hshape
  rw [← hs, rfStream_body hp hsz hH T W, toBytes_map_toNat',
    Rcpt.Candidates.NodePostUpdate.prepD0_body_eq hp]

/-! ## The receipt core with `RecBytes` and `hrf` discharged -/

/-- **The receipt core of `m.Valid.run` from the trace**, given the trie link's `ShaHyp` (lane
v3-link: `shaHyp_holds`).  Remaining: `MainTrieLink`, the queue reads, the demand check. -/
theorem mainRun_of_holdsP_sha {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length)
    {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (S : ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values others shaS shaR) :
    ∃ pc refunds, prepClaim cb = .ok pc ∧ decodeBody h.body = .ok refunds ∧
      ∀ (base : Nat → Bytes) (Tf : (Nat → Bytes) → PTrie) (pre mid : PTrie) (so : SchedOut)
        (v : Qv.MainValues),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →
        v.Valid →
        v.Reads pre mid (Tf ((recModel r.lists r.accts base Tf).valsAt (flatR r.lists).length)) →
        (∀ s ∈ statusShards pc.ctxB2, demand pc.ctxB2 refunds s ≤ so.grant pc.ctxB2.own s) →
        applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  have B : RecBytes r.lists r.accts :=
    ⟨preB_of hH T W S, burntBytes hp hsz hH T W, ramtBytes hp hsz hH T W⟩
  obtain ⟨pc, refunds, hc, hd, K⟩ := mainRun_of_holdsP hp hsz hH T W hn B
  obtain ⟨pc', hc', hb', hgp⟩ := gasPrice_pub oh hp
  rw [hc] at hc'
  cases hc'
  have H : RecHyp _ r.lists r.accts :=
    { mem := memHyp_of' hH T W
      wf := W.lists
      acct := W.accts
      preB := B.preB
      encB := LinkRidBytes.encBytes hp hsz hH T W
      burntB := B.burntB
      ramtB := B.ramtB
      bgpB := fun y hy => by
        simp only [pubBytes, List.mem_map, List.mem_range] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact pubNat_pubOf_lt _ _ }
  refine ⟨pc, refunds, hc, hd, ?_⟩
  intro base Tf pre mid so v L hv hR hdem
  exact K base Tf pre mid so v L hv hR (refunds_of hp hsz hH T W H hc hb' hgp base Tf hd) hdem

/-- **The receipt core with the per-shard demand check replaced by the AIR's link-indexed check
on the public `p.fwd`** (`fwdDemand p.fwd (o·n + r) ≤ so.grant own ids[r]`, `o = idx(own)`).
Remaining (lane v3-link): `MainTrieLink`, the queue reads, `ShaHyp`, `own ∈ shardIds` and the
identification of the scheduler table's link grant with `so.grant own ids[r]`. -/
theorem mainRun_of_holdsP_fwd {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
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
        (v : Qv.MainValues) (o : Nat),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →
        v.Valid →
        v.Reads pre mid (Tf ((recModel r.lists r.accts base Tf).valsAt (flatR r.lists).length)) →
        Scheduler.indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some o →
        (∀ k, (hk : k < pc.ctxB2.layout.shardIds.length) →
          ZkFormal.NearV3.Sched.fwdDemand p.fwd (o * pc.ctxB2.layout.shardIds.length + k) ≤
            so.grant pc.ctxB2.own pc.ctxB2.layout.shardIds[k]) →
        applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  obtain ⟨pc, refunds, hc, hd, K⟩ := mainRun_of_holdsP_sha hp hsz hH T W hn S
  obtain ⟨pc', refunds', hc', F⟩ := prepD0_fwd hp
  rw [hc] at hc'
  cases hc'
  rw [F.body] at hd
  cases hd
  refine ⟨pc, hc, ?_⟩
  intro base Tf pre mid so v o L hv hR ho hL
  rw [F.fwd] at hL
  exact K base Tf pre mid so v L hv hR (hsz_of_links (prepClaim_layout_wf hc) ho hL)

end ZkFormal.NearV3.RcptLink
