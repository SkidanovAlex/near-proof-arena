import ZkFormal.NearV3.Assembly.RenderV3RcptAccepted
import ZkFormal.NearV3.Assembly.RenderV3Assemble
import ZkFormal.NearV3.Render.HonestBalanceSrec
import ZkFormal.NearV3.Render.HonestBalanceRcl
import ZkFormal.NearV3.Render.HonestBalanceSrc
import ZkFormal.NearV3.Public.ReceiptIndex
import ZkFormal.V2.PubIdx

/-!
# Receipt-side bus balances in the bundle's form (`RenderBundleV3.Balanced`, per bus)

`BusBalanced R b` is the bundle balance `R.Balanced` restricted to bus `b`: the sends of all 25
tables' honest traffic plus the public sends equal the receives plus the public receives
(`balanced_of_buses`: all buses ⇒ `R.Balanced`).

Generic reduction (`bundle_sum`): a table without an interaction on `(b, side)` contributes `0`
(its exact traffic counts the trace's messages, of which there are none), so each side's sum is
the sum over the tables using the bus (computed once by `decide`; `nearAirV3` users:
SREC 16|16, RCL 16|20, AKC 16,18|16,18, BND 16,19|16,19, BNDP –|19 (public send), RIDS 16|24,
SRC –|20 (public send), MEM 16,17|16,17, QSH 22|22, QVC 22|22).

For a bundle whose tables 16–20, 22 (and 24 for RIDS) carry the honest traffic of an accepted
witness `A` (hypotheses `h16 … : R.tf t = …`, satisfied by `AcceptedV3.rcptAcc …`):
* **unconditional**: SREC, RCL, AKC, RIDS, MEM, QSH, QVC; SRC (given the packed public size
  `< 256^4`, which `RenderWitnessV3` requires anyway via `< P`);
* **BND** under the explicit routing-coverage premise of `honest_bnd_balance` (every physical
  routing key of the honest receipt trace is a bounded boundary row);
* **BNDP** under the explicit decidable layout premise `A.bounds = A.p.bnds` (the bounded
  intervals are the published ones; false for malformed-but-accepted layouts with own shard 0
  and `|boundaries| > |shardIds|`, see the lane log).
-/

namespace ZkFormal.NearV3.Assembly.RcptBal
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open ZkFormal.NearV3.Render ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.RcptSkeleton

variable {pub : List Fp}

/-- The bundle balance on one bus. -/
def BusBalanced (R : RenderBundleV3 pub) (b : Nat) : Prop :=
  ∀ m,
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel true (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b true m =
      (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel false (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b false m

theorem balanced_of_buses (R : RenderBundleV3 pub) (h : ∀ b, BusBalanced R b) : R.Balanced :=
  fun b m => h b m

/-! ## Generic reduction to the bus users -/

/-- No interaction of table `t` on `(b, s)` (tables outside `S`). -/
def sideFree (b : Nat) (s : Bool) (S : List Nat) : Bool :=
  (List.range 25).all fun t => S.contains t ||
    (nearTablesFull.getD t default).interactions.all (fun i => !(i.bus == b && i.send == s))

theorem cnt_free (R : RenderBundleV3 pub) {t : Nat} (ht : t < 25) {b : Nat} {s : Bool}
    (h : (nearTablesFull.getD t default).interactions.all (fun i => !(i.bus == b && i.send == s)) = true)
    (m : List Fp) : cnt (sel s (R.tf t) b) m = 0 := by
  have ht' : t < nearAirV3.tables.length := ht
  have hT := R.traffic_at t ht'
  rw [← count_sel hT b s m, ZkFormal.Near.tableBusCount_eq]
  have hg : nearAirV3.tables[t] = nearTablesFull.getD t default := by
    show nearTablesFull[t] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < nearTablesFull.length from ht),
      Option.getD_some]
    rfl
  have hnil : (List.range (R.trace.height t)).flatMap
      (fun r => rowTraffic nearAirV3.tables[t].interactions R.trace t r pub b s) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r _
    apply List.flatMap_eq_nil_iff.mpr
    intro i hi
    rw [hg] at hi
    have hx := List.all_eq_true.mp h i hi
    have hn : ¬(i.bus = b ∧ i.send = s) := by
      intro ⟨h1, h2⟩
      simp [h1, h2] at hx
    simp only [hn, ite_false]
  rw [hnil]
  rfl

theorem mapIdx_sum_range {α : Type} (l : List α) (f : Nat → Nat) :
    (l.mapIdx fun t _ => f t).sum = ((List.range l.length).map f).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem sum_range_filter (f : Nat → Nat) (P : Nat → Bool) :
    ∀ n, (∀ t, t < n → P t = false → f t = 0) →
      ((List.range n).map f).sum = (((List.range n).filter P).map f).sum
  | 0, _ => rfl
  | n + 1, hz => by
    rw [List.range_succ, List.filter_append, List.map_append, List.map_append, List.sum_append,
      List.sum_append, sum_range_filter f P n (fun t ht hp => hz t (by omega) hp)]
    cases hp : P n
    · simp [hp, hz n (by omega) hp]
    · simp [hp]

/-- **Each side's bundle sum is the sum over the bus users.** -/
theorem bundle_sum (R : RenderBundleV3 pub) (b : Nat) (s : Bool) (S : List Nat)
    (hS : sideFree b s S = true) (m : List Fp) :
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel s (R.tf t) b) m).sum =
      (((List.range 25).filter (fun t => S.contains t)).map fun t => cnt (sel s (R.tf t) b) m).sum := by
  rw [mapIdx_sum_range nearTablesFull (fun t => cnt (sel s (R.tf t) b) m)]
  apply sum_range_filter _ _ 25
  intro t ht hp
  have hx := List.all_eq_true.mp hS t (List.mem_range.mpr ht)
  rw [hp, Bool.false_or] at hx
  exact cnt_free R ht hx m

/-- No public segment on `(b, s)`. -/
theorem pubCount_free (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp)
    (h : ZkFormal.NearV3.Public.preparedSegments.all (fun seg => !(seg.bus == b && seg.send == s)) = true) :
    pubCount nearAirV3 pub b s m = 0 := by
  unfold pubCount
  suffices ((pubMsgs nearAirV3 pub).filter (fun x => decide (x = (b, s, m)))) = [] by rw [this]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simp only [pubMsgs, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨seg, hseg, m', -, rfl⟩ := hx
  have hs := List.all_eq_true.mp h seg hseg
  intro he
  simp only [decide_eq_true_eq, Prod.mk.injEq] at he
  simp [he.1, he.2.1] at hs

/-- Public counts from the prepared records (packed size `< 256^4`). -/
theorem pubCount_prepared {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (hlen : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < 256 ^ 4) (b : Nat) (s : Bool)
    (m : List Fp) :
    pubCount nearAirV3 A.pub b s m =
      ((ZkFormal.NearV3.Public.preparedOn A.p b s).map (·.map Fp.ofNat)).count m := by
  unfold AcceptedV3.pub
  rw [(ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 A.p 0 rfl (prepD0_roots A.hp)
    (prepD0_source_roots A.hp) hlen).count b s m]
  congr 2

theorem cnt_append (l₁ l₂ : List Msg) (m : List Fp) : cnt (l₁ ++ l₂) m = cnt l₁ m + cnt l₂ m := by
  simp [cnt, List.count_append]

theorem cnt_perm {l₁ l₂ : List Msg} (h : (l₁.map Msg.toFp).Perm (l₂.map Msg.toFp)) (m : List Fp) :
    cnt l₁ m = cnt l₂ m := h.count_eq m

/-! ## The receipt-side buses of an accepted witness -/

variable {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)

theorem rcptB_sends {b : Nat} (hb : b ≠ B_BND) :
    (rcptTrafficB A.pub A.rcptInput).sends b =
      (rcptTraffic3 A.pub (nativeRcptLists A.pub A.rcptInput)).sends b :=
  (rcptTrafficB_other A.pub A.rcptInput b hb).1

theorem rcptB_recvs {b : Nat} (hb : b ≠ B_BND) :
    (rcptTrafficB A.pub A.rcptInput).recvs b =
      (rcptTraffic3 A.pub (nativeRcptLists A.pub A.rcptInput)).recvs b :=
  (rcptTrafficB_other A.pub A.rcptInput b hb).2

/-- **SREC** (receipt table only). -/
theorem srec_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput) : BusBalanced R B_SREC := by
  intro m
  rw [bundle_sum R B_SREC true [16] (by decide +kernel), bundle_sum R B_SREC false [16] (by decide +kernel),
    pubCount_free A.pub B_SREC true m (by decide +kernel), pubCount_free A.pub B_SREC false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16].contains t) = [16] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16]
  rw [rcptB_sends A (by decide), rcptB_recvs A (by decide)]
  have := cnt_perm (honest_srec_balance A.pub A.rcptInput A.rcptOk) m
  omega

/-- **RCL** (receipt sends, source-proof receives). -/
theorem rcl_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h20 : R.tf 20 = A.ddTraffic) : BusBalanced R B_RCL := by
  intro m
  rw [bundle_sum R B_RCL true [16] (by decide +kernel), bundle_sum R B_RCL false [20] (by decide +kernel),
    pubCount_free A.pub B_RCL true m (by decide +kernel), pubCount_free A.pub B_RCL false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16].contains t) = [16] := by decide
  have hg : (List.range 25).filter (fun t => [20].contains t) = [20] := by decide
  simp only [hf, hg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16, h20]
  rw [rcptB_sends A (by decide),
    accepted_rcl_balance A.pub A.rcptInput A.rcptOk rfl]
  unfold AcceptedV3.ddTraffic AcceptedV3.ddBlocks AcceptedV3.ddRep
  rw [dd_rcl_recvs]
  rfl

/-- **AKC** (receipt ↔ access-key providers). -/
theorem akc_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h18 : R.tf 18 = akeyTraffic A.akeys) : BusBalanced R B_AKC := by
  intro m
  rw [bundle_sum R B_AKC true [16, 18] (by decide +kernel),
    bundle_sum R B_AKC false [16, 18] (by decide +kernel),
    pubCount_free A.pub B_AKC true m (by decide +kernel), pubCount_free A.pub B_AKC false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16, 18].contains t) = [16, 18] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16, h18]
  rw [rcptB_sends A (by decide), rcptB_recvs A (by decide)]
  have hp := (honest_akc_balance A.pub A.rcptInput A.rcptOk A.akcOk).count_eq m
  rw [List.map_append, List.map_append, List.count_append, List.count_append] at hp
  unfold AcceptedV3.akeys
  simp only [cnt]
  omega

/-- **RIDS** (receipt ids into the sort table, `sortRenderV3`'s traffic). -/
theorem rids_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h24 : R.tf 24 = sortTraffic (Candidates.NativeSortIds.input
      (A.rcptInput.lists.flatten.map Input.receipt))) : BusBalanced R B_RIDS := by
  intro m
  rw [bundle_sum R B_RIDS true [16] (by decide +kernel), bundle_sum R B_RIDS false [24] (by decide +kernel),
    pubCount_free A.pub B_RIDS true m (by decide +kernel), pubCount_free A.pub B_RIDS false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16].contains t) = [16] := by decide
  have hg : (List.range 25).filter (fun t => [24].contains t) = [24] := by decide
  simp only [hf, hg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16, h24]
  rw [rcptB_sends A (by decide), honest_rids_balance A.pub A.rcptInput A.rcptOk]

/-- **MEM** (receipt ↔ account table, the native account views). -/
theorem mem_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h17 : R.tf 17 = acctV3Traffic A.accts) : BusBalanced R B_MEM := by
  intro m
  rw [bundle_sum R B_MEM true [16, 17] (by decide +kernel),
    bundle_sum R B_MEM false [16, 17] (by decide +kernel),
    pubCount_free A.pub B_MEM true m (by decide +kernel), pubCount_free A.pub B_MEM false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16, 17].contains t) = [16, 17] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16, h17]
  rw [rcptB_sends A (by decide), rcptB_recvs A (by decide)]
  have hp := ((honest_mem_balance A.pub A.rcptInput A.rcptOk A.accts_spec.1).map Msg.toFp).count_eq m
  rw [List.map_append, List.map_append, List.count_append, List.count_append] at hp
  simp only [cnt]
  omega

/-- **SRC** (published source records into the source-proof table). -/
theorem src_balanced (hlen : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < 256 ^ 4)
    (h20 : R.tf 20 = A.ddTraffic) : BusBalanced R B_SRC := by
  intro m
  rw [bundle_sum R B_SRC true [] (by decide +kernel), bundle_sum R B_SRC false [20] (by decide +kernel),
    pubCount_free A.pub B_SRC false m (by decide +kernel), pubCount_prepared A hlen B_SRC true m]
  have hf : (List.range 25).filter (fun t => ([] : List Nat).contains t) = [] := by decide
  have hg : (List.range 25).filter (fun t => [20].contains t) = [20] := by decide
  simp only [hf, hg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel,
    Bool.false_eq_true, ite_false, h20]
  unfold AcceptedV3.ddTraffic AcceptedV3.ddBlocks AcceptedV3.ddRep
  rw [accepted_src_balance_dd A.rel A.hp A.w]
  simp only [Nat.zero_add, Nat.add_zero]
  rfl

/-- **QVC** (queue-value provider counters, table 22 only). -/
theorem qvc_balanced (h22 : R.tf 22 = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)) :
    BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC := by
  intro m
  rw [bundle_sum R _ true [22] (by decide +kernel), bundle_sum R _ false [22] (by decide +kernel),
    pubCount_free A.pub _ true m (by decide +kernel), pubCount_free A.pub _ false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [22].contains t) = [22] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h22]
  have := cnt_perm ((qvNative_qvc_balance _ A.qvHolds).map Msg.toFp) m
  omega

/-- **QSH** (queue shard words, table 22 only). -/
theorem qsh_balanced (h22 : R.tf 22 = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)) :
    BusBalanced R B_QSH := by
  intro m
  rw [bundle_sum R _ true [22] (by decide +kernel), bundle_sum R _ false [22] (by decide +kernel),
    pubCount_free A.pub _ true m (by decide +kernel), pubCount_free A.pub _ false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [22].contains t) = [22] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h22]
  have := cnt_perm ((qvNative_qsh_balance _ A.qvHolds).map Msg.toFp) m
  omega

/-- **BND** (receipt routing lookups ↔ boundary rows), under the explicit coverage premise. -/
theorem bnd_balanced (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h19 : R.tf 19 = bndTraffic A.bnds)
    (hc : ∀ r ∈ RoutingQCandidate.physicalActiveRows (rcptTraceNative A.pub A.rcptInput) 0,
      RoutingQCandidate.physicalBoundaryKey (rcptTraceNative A.pub A.rcptInput) 0 r ∈
        A.bnds.map BndE.rec4) : BusBalanced R B_BND := by
  intro m
  rw [bundle_sum R B_BND true [16, 19] (by decide +kernel),
    bundle_sum R B_BND false [16, 19] (by decide +kernel),
    pubCount_free A.pub B_BND true m (by decide +kernel), pubCount_free A.pub B_BND false m (by decide +kernel)]
  have hf : (List.range 25).filter (fun t => [16, 19].contains t) = [16, 19] := by decide
  simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, h16, h19]
  have hp := ((honest_bnd_balance A.pub A.rcptInput A.bounds hc).map Msg.toFp).count_eq m
  rw [List.map_append, List.map_append, List.count_append, List.count_append] at hp
  unfold AcceptedV3.bnds
  simp only [cnt]
  omega

/-- **BNDP** (published boundary rows into the boundary table), under the explicit decidable
layout premise that the bounded intervals are the published ones. -/
theorem bndp_balanced (hlen : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < 256 ^ 4)
    (hb : A.bounds = A.p.bnds) (h19 : R.tf 19 = bndTraffic A.bnds) : BusBalanced R B_BNDP := by
  intro m
  rw [bundle_sum R B_BNDP true [] (by decide +kernel), bundle_sum R B_BNDP false [19] (by decide +kernel),
    pubCount_free A.pub B_BNDP false m (by decide +kernel), pubCount_prepared A hlen B_BNDP true m]
  have hf : (List.range 25).filter (fun t => ([] : List Nat).contains t) = [] := by decide
  have hg : (List.range 25).filter (fun t => [19].contains t) = [19] := by decide
  simp only [hf, hg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel,
    Bool.false_eq_true, ite_false, h19]
  rw [ZkFormal.NearV3.Public.prepared_boundary_records]
  have hrec : A.bnds.map BndE.rec4 = ZkFormal.NearV3.Public.boundaryRecords A.p := by
    have h := RoutingBoundedLayout.boundaryEntries_records A.p
      (RoutingQCandidate.physicalBoundaryKeys (rcptTraceNative A.pub A.rcptInput) 0)
    unfold AcceptedV3.bnds
    rw [hb]
    exact h
  simp only [bndTraffic, bndRecvs, ite_true]
  rw [hrec]
  simp only [Nat.zero_add, Nat.add_zero]
  rfl

end ZkFormal.NearV3.Assembly.RcptBal
