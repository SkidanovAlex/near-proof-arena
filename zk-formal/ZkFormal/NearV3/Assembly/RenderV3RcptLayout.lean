import ZkFormal.NearV3.Assembly.RenderV3RcptBalance
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRoutingIntervals
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedPreparedLength

/-!
# A12 (`c.layout_wf`) closes the published-interval gap of the receipt renders

Under A12 (`|boundaries| + 1 = |shardIds|`, a conjunct of `RelD0a`), the bounded layout is the
layout itself, so the bounded routing intervals the honest receipt render reads are exactly the
published `p.bnds` (`AcceptedV3.bounds_eq`, `boundedPrep_eq`).  Consequences for an accepted
witness `A`:

* `A.prepared_le`: `|preparedBytes A.p 0| ≤ 2^26` (from `accepted_prepared_length`), hence
  `A.prepared_lt_P` and `A.pubFit` (the size and fit conjuncts of `RenderWitnessV3`);
* `bndp_balanced_accepted`: the BNDP bus balances with no premise beyond the honest traffic.
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open RoutingBoundedLayout

/-- A12 on the layout of a walked claim. -/
theorem layoutWf_of_rel {B : Nat} {cb wb : Bytes} {k : WalkD0} (h : RelD0a B cb wb)
    (hk : walkD0 cb = .ok k) : k.L.boundaries.length + 1 = k.L.shardIds.length := by
  have ha := h.2.2.2.2.2.2.2.2
  simpa only [a12, hk, beq_iff_eq] using ha

/-- A well-formed layout is its own bounded layout. -/
theorem boundedLayout_wf (L : Layout) (h : L.boundaries.length + 1 = L.shardIds.length) :
    boundedLayout L = L := by
  cases L with
  | mk bd ids i2x =>
    simp only [boundedLayout] at *
    rw [List.take_of_length_le (by omega)]

namespace AcceptedV3

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

theorem layoutWf : A.k.L.boundaries.length + 1 = A.k.L.shardIds.length :=
  layoutWf_of_rel A.rel A.hk

/-- **The bounded routing intervals are the published ones.** -/
theorem bounds_eq : A.bounds = A.p.bnds := by
  rw [ZkFormal.NearV3.Assembly.prepD0_routing_intervals A.hp A.hk]
  change ownIntervals (boundedLayout A.k.L) A.k.H.shardId = _
  rw [boundedLayout_wf _ A.layoutWf]

theorem boundedPrep_eq : boundedPrep A.p A.k.L A.k.H.shardId = A.p := by
  have h : boundedIntervals A.k.L A.k.H.shardId = A.p.bnds := A.bounds_eq
  unfold boundedPrep
  rw [h]

/-- The packed public statement of an accepted witness fits `maxPub = 2^26`. -/
theorem prepared_le : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length ≤ 2 ^ 26 := by
  have h := ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_prepared_length A.hp A.hk A.hw
    A.h A.hm 0
  rwa [A.boundedPrep_eq] at h

theorem prepared_lt_P : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < ZkFormal.Algebra.P := by
  have := A.prepared_le
  unfold ZkFormal.Algebra.P
  omega

theorem prepared_lt_u32 : (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < 256 ^ 4 := by
  have := A.prepared_le
  omega

/-- **`pubFit`** of the certificate's public vector for an accepted witness. -/
theorem pubFit : ZkFormal.V2.pubFit nearAirV3 A.pub = true :=
  ZkFormal.NearV3.Public.prepared_pubFit nearAirV3 A.p 0 rfl (prepD0_roots A.hp)
    (prepD0_source_roots A.hp) A.prepared_le (by decide)

end AcceptedV3

namespace RcptBal

variable {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)

/-- **BNDP** for an accepted witness (A12 makes the bounded rows the published ones). -/
theorem bndp_balanced_accepted (h19 : R.tf 19 = bndTraffic A.bnds) : BusBalanced R B_BNDP :=
  bndp_balanced A R A.prepared_lt_u32 A.bounds_eq h19

/-- **SRC** for an accepted witness (no size premise). -/
theorem src_balanced_accepted
    (h20 : R.tf 20 = srcpTraffic (ZkFormal.NearV3.Render.SrcpGen.blocksOfProofs A.srcps)) : BusBalanced R B_SRC :=
  src_balanced A R A.prepared_lt_u32 h20

end RcptBal

end ZkFormal.NearV3.Assembly
