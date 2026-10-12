import ZkFormal.NearV3.Rcpt.Link.QvMain
import ZkFormal.NearV3.Rcpt.Link.AkeyAkc
import ZkFormal.NearV3.Assembly.PrepContext
import ZkFormal.NearV3.Rcpt.Link.BoundedNativeRouting
import ZkFormal.NearV3.Rcpt.Link.BndPublic
import ZkFormal.NearV3.Assembly.RenderV3RcptLayout
import ZkFormal.NearV3.Assembly.LinkClaim

/-!
# ZkFormal.NearV3.Rcpt.Link.RcptRoute — receipt routing from `HoldsP` (table 16's `q < 128` check)

* `rcpt_bnd_sends` / `rcpt_bnd_recvs`: the receipt view's `BND` traffic is the boundary requests'.
* `bnd_lookup_perm`: the exact `BND` balance (users rcpt 16, bnd 19; no public segment) in the form
  of `bnd_lookup_provider`; `bndp_count`: the `BNDP` balance (bnd receives, public sends
  `boundaryRecords p`).
* `prepClaim_ctx_walk`: `pc.ctxB2.layout = k.L ∧ pc.ctxB2.own = k.H.shardId`;
  `boundedPrep_self`: `boundedPrep p k.L k.H.shardId = p` (A12 `layoutWf`, checked by `prepClaim`).
* **`route_holdsP`**: given `hq : ∀ x ∈ flatR r.lists, x.q < 128`, every receipt routes to the own shard.
* **`mainRun_of_holdsP_r`**: `mainRun_of_holdsP_q` without the routing premise (`hq := W.listsQ`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly.RoutingBoundedLayout

def bndS (x : RcptE) : List Msg := x.rlk.map fun (p, l, h, hn, u) => [BND_STRIDE * x.q + p, l, h, hn, u + 1]
def bndR (x : RcptE) : List Msg := x.rlk.map fun (p, l, h, hn, u) => [BND_STRIDE * x.q + p, l, h, hn, u]

theorem rcpt_bnd_sends (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_BND = (flatR ls).flatMap bndS := by
  rw [← range_lists_flatMap]
  unfold rcptSends3
  apply ZkFormal.Near.Link.flatMap_congr'
  intro j _
  simp only [show B_BND ≠ B_BYTES by decide, show B_BND ≠ B_RCL by decide, ite_false, List.nil_append]
  apply ZkFormal.Near.Link.flatMap_congr'
  intro y _
  simp [rSends, bndS, B_AKC, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_SREC, B_BND]

theorem rcpt_bnd_recvs (ls : RcptV3Vs) : rcptRecvs3 ls B_BND = (flatR ls).flatMap bndR := by
  rw [← range_lists_flatMap]
  unfold rcptRecvs3
  apply ZkFormal.Near.Link.flatMap_congr'
  intro j _
  apply ZkFormal.Near.Link.flatMap_congr'
  intro y _
  simp [rRecvs, bndR, B_AKC, B_DIGEST, B_FINAL, B_MEM, B_SREC, B_BND]

theorem req_sends (ls : RcptV3Vs) :
    (boundaryRequests ls).map (fun r => r.1 ++ [r.2 + 1]) = (flatR ls).flatMap bndS := by
  simp only [boundaryRequests, List.map_flatMap, List.map_map]
  apply ZkFormal.Near.Link.flatMap_congr'
  intro x _
  simp only [bndS, BND_STRIDE]
  apply List.map_congr_left
  intro y _
  rfl

theorem req_recvs (ls : RcptV3Vs) :
    (boundaryRequests ls).map (fun r => r.1 ++ [r.2]) = (flatR ls).flatMap bndR := by
  simp only [boundaryRequests, List.map_flatMap, List.map_map]
  apply ZkFormal.Near.Link.flatMap_congr'
  intro x _
  simp only [bndR, BND_STRIDE]
  apply List.map_congr_left
  intro y _
  rfl

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- The exact `BND` lookup balance in `bnd_lookup_provider` form. -/
theorem bnd_lookup_perm (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ((r.bnds.map (fun e => e.rec4 ++ [0]) ++ (boundaryRequests r.lists).map (fun q => q.1 ++ [q.2 + 1])).map
        Msg.toFp).Perm
      ((r.bnds.map (fun e => e.rec4 ++ [e.U]) ++ (boundaryRequests r.lists).map (fun q => q.1 ++ [q.2])).map
        Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := B_BND) (U := [Assembly.T_RCPT, T_BND]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists, show isAt T_BND = BndV3.interactions from rfl, tcnt_of_traffic T.bnds,
    tcnt_of_traffic T.bnds] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, bndTraffic, bndSends,
    bndRecvs, show B_BND ≠ B_BNDP by decide] at h
  rw [rcpt_bnd_sends, rcpt_bnd_recvs] at h
  rw [req_sends, req_recvs]
  simp only [List.map_append, List.count_append] at h ⊢
  omega

end

private theorem mapError_ok_iff' {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
/-- The claim context is the walk's layout and own shard. -/
theorem prepClaim_ctx_walk {cb : Bytes} {pc : PrepC} {k : WalkD0}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) :
    pc.ctxB2.layout = k.L ∧ pc.ctxB2.own = k.H.shardId := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := ZkFormal.NearV3.Sched.bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff', pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := ZkFormal.NearV3.Sched.bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      exact ⟨rfl, rfl⟩

/-- The `BNDP` balance: the bnd records are the public boundary records. -/
theorem bndp_count {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp} {r : V3Records}
    (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r) :
    ∀ m, ZkFormal.Near.cnt (r.bnds.map BndE.rec4) m = ZkFormal.Near.cnt (ZkFormal.NearV3.Public.boundaryRecords p) m := by
  intro m
  have hroots := prepD0_roots hp
  have hl256 : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by
    unfold ZkFormal.Algebra.P at hsz; omega
  have hI := ZkFormal.NearV3.Public.prepared_receipt_index nearAirV3 p oh rfl hroots
    (prepD0_source_roots hp) hl256
  have hc := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl hroots
    (prepD0_source_roots hp) hl256).count B_BNDP true m
  rw [hI.2.1] at hc
  have h := hH.balance B_BNDP m
  rw [pubCount_noside (sd := false) (by decide +kernel), hc,
    busCount_users (U := [T_BND]) (by decide) (by decide) (by decide +kernel),
    busCount_users (U := [T_BND]) (by decide) (by decide) (by decide +kernel)] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt T_BND = BndV3.interactions from rfl, tcnt_of_traffic T.bnds, tcnt_of_traffic T.bnds] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, bndTraffic, bndSends, bndRecvs,
    show B_BNDP ≠ B_BND by decide, List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
  unfold ZkFormal.Near.cnt
  rw [← h]
  rfl

/-- A12: the bounded public representation is the prepared one. -/
theorem boundedPrep_self {cb : Bytes} {h : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb h = .ok p) (hw : walkD0 cb = .ok k) :
    boundedPrep p k.L k.H.shardId = p := by
  obtain ⟨pc, hc, -⟩ := ZkFormal.NearV3.Sched.bind_ok hp
  obtain ⟨k', hk', F⟩ := walkD0_of_prepClaim hc
  rw [hw] at hk'
  cases hk'
  have hb : boundedIntervals k.L k.H.shardId = p.bnds := by
    rw [ZkFormal.NearV3.Assembly.prepD0_routing_intervals hp hw]
    change ownIntervals (boundedLayout k.L) k.H.shardId = _
    rw [boundedLayout_wf _ F.layoutWf]
  unfold boundedPrep
  rw [hb]

/-- **Receipt routing from `HoldsP`** (table 16's `q < 128` check, as `hq`). -/
theorem route_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp} {r : V3Records}
    (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hq : ∀ x ∈ flatR r.lists, x.q < 128) {pc : PrepC} (hc : prepClaim cb = .ok pc) :
    ∀ x ∈ flatR r.lists, pc.ctxB2.layout.shardOf (toBytes x.v) = pc.ctxB2.own := by
  intro x hx
  obtain ⟨k, hw, -⟩ := walkD0_of_prepClaim hc
  obtain ⟨hL, hO⟩ := prepClaim_ctx_walk hc hw
  have hb : ∀ m, ZkFormal.Near.cnt (r.bnds.map BndE.rec4) m =
      ZkFormal.Near.cnt (ZkFormal.NearV3.Public.boundaryRecords (boundedPrep p k.L k.H.shardId)) m := by
    rw [boundedPrep_self hp hw]; exact bndp_count hp hsz hH T
  have hn := (boundaryRequests_bound W.lists W.listsCount.2)
  have hp' := bnd_lookup_provider r.bnds _ W.bnds (boundaryRequests_canonical W.lists hq) hn
    (bnd_lookup_perm hH T)
  have := bounded_prepared_native_routing hp hw W.lists r.bnds W.bnds hb hp' hx
  rw [hL, hO]
  exact this

/-- **The receipt core at `Fpre r 0` with routing discharged** (`hq := W.listsQ`: table 16's q check). -/
theorem mainRun_of_holdsP_r {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length) :
    ∃ pc bs, prepClaim cb = .ok pc ∧
      (∃ v, (LinkImplicit.Fpre r 0).find keyBufferedIdx = some v ∧ bufferedShards v = .ok bs) ∧
      (∀ key ∈ [keyDelayedIdx, keyBufferedIdx, keyYieldIdx], (LinkImplicit.Fpre r 0).find key ≠ none) ∧
      (∀ y ∈ bs, (LinkImplicit.Fpre r 0).find (keyGroupsData y) ≠ none) ∧
      ∀ (base : Nat → Bytes) (Tf : (Nat → Bytes) → PTrie) (mid : PTrie) (so : SchedOut),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 (LinkImplicit.Fpre r 0) mid so →
        (∀ o, Scheduler.indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some o →
          ∀ k, (hk : k < pc.ctxB2.layout.shardIds.length) →
          ZkFormal.NearV3.Sched.fwdDemand p.fwd (o * pc.ctxB2.layout.shardIds.length + k) ≤
            so.grant pc.ctxB2.own pc.ctxB2.layout.shardIds[k]) →
        applyNewChunk prims pc.ctxB2 (LinkImplicit.Fpre r 0) ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  obtain ⟨pc, bs, hc, hbs, hfix, hgrp, K⟩ := mainRun_of_holdsP_q hp hsz hH T W hn
  exact ⟨pc, bs, hc, hbs, hfix, hgrp, fun base Tf mid so M =>
    K base Tf mid so M (route_holdsP hp hsz hH T W W.listsQ hc)⟩

/-- **`hroute`** of lane v3-link's `executions_run`, from `HoldsP` (`W.listsQ`). -/
theorem hroute_holds {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ pc, prepClaim cb = .ok pc →
      ∀ y ∈ flatR r.lists, pc.ctxB2.layout.shardOf (toBytes y.v) = pc.ctxB2.own :=
  fun _ hc => route_holdsP hp hsz hH T W W.listsQ hc

end ZkFormal.NearV3.RcptLink
