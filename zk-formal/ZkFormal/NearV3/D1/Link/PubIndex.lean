import ZkFormal.NearV3.D1.Link.Base
import ZkFormal.NearV3.Public.Index

/-!
# `ZkFormal.NearV3.D1.Link.PubIndex` — the public-bus index of the D1 tape (L1)

Lane `v3-d1-phase2`, item L1.  D0a's `prepared_pubIdx` / `prepared_pubIdx_recs`
(`Public/Index`) for the 15 segments of `nearAirV3D1`:

* `preparedRecordsD1 q seg`: the records of segment `seg` of the D1 tape (blocks `0 … 8` are
  `q.base`'s, so on D0a's nine segments they are D0a's `preparedRecords q.base`);
* `preparedD1_segment_msgs`, **`preparedD1_pubIdx`**;
* **`preparedD1_pubIdx_recs`**: off the six new `(bus, side)` pairs (`newPairs`: the body
  prefix sends on bus 0, and the sends on `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`), the records
  are D0a's `preparedOn q.base bus side`.  The generated copies call it with literal buses
  (`by decide`).
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpecV3 ZkFormal.V2 ZkFormal.Algebra ZkFormal.NearV3.Public ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

def preparedRecordsD1 (q : PrepD1) (seg : PubSeg) : List (List Nat) :=
  let rows := (preparedBlocksD1 q).getD (segmentIndex seg) []
  (List.range rows.length).map (fun j => recordNats seg j (rows.getD j []))

/-- The new segments' `(bus, side)` pairs. -/
def newPairs : List (Nat × Bool) :=
  [(0, true), (B_TXP, true), (B_SIG, true), (B_PKEY, true), (B_PLEAF, true), (B_PRID, true)]

theorem newSegs_pairs : ∀ s ∈ newSegs, (s.bus, s.send) ∈ newPairs := by
  rw [newSegs_eq]; decide

theorem preparedD1_segment_msgs (q : PrepD1) (ov : Nat) (hr : RootsSized q.base)
    (hs : ∀ s ∈ q.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ q.leaves, l.length = 32)
    (hlen : (preparedBytesD1 q ov).length < 256 ^ 4) (seg : PubSeg) (hseg : seg ∈ preparedSegmentsD1) :
    seg.msgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 q ov)) =
      (preparedRecordsD1 q seg).map (·.map Fp.ofNat) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hseg
  have hi : i < 15 := List.mem_range.mp hi
  have hbi : i < (preparedBlocksD1 q).length := by rw [preparedBlocksD1_length]; exact hi
  have hw := preparedD1_width q hr hs hleaves hi
  obtain ⟨hn, ho⟩ := descriptorD1_u32_bounds (plansD1.getD i sourcePlan) (headerBytesD1 q ov) (extBytes q)
    _ hbi (plansD1_width_positive hi) hw hlen
  unfold preparedRecordsD1
  rw [descriptor_index]
  change (descriptor (plansD1.getD i sourcePlan) 202 i).msgs
      (ZkFormal.Udr.pubOf Fp (encodeD1 (headerBytesD1 q ov) (extBytes q) (preparedBlocksD1 q))) = _
  rw [← headerBytesD1_length q ov hr, descriptorD1_msgs _ _ _ _ hbi hn hw ho, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [recordNats_field]
  rfl

/-- **The public-bus index of the D1 tape.** -/
def preparedD1_pubIdx (AP : AirP) (q : PrepD1) (ov : Nat) (hseg : AP.pubSegs = preparedSegmentsD1)
    (hr : RootsSized q.base) (hs : ∀ s ∈ q.base.lists, s.root.length = 32)
    (hleaves : ∀ l ∈ q.leaves, l.length = 32) (hlen : (preparedBytesD1 q ov).length < 256 ^ 4) :
    PubIdx AP (ZkFormal.Udr.pubOf Fp (preparedBytesD1 q ov)) Fp.ofNat := by
  apply pubIdx_of_segments AP _ Fp.ofNat (preparedRecordsD1 q)
  intro seg hmem
  apply preparedD1_segment_msgs q ov hr hs hleaves hlen seg
  rwa [hseg] at hmem

theorem preparedRecordsD1_old (q : PrepD1) {seg : PubSeg} (hseg : seg ∈ preparedSegments) :
    preparedRecordsD1 q seg = preparedRecords q.base seg := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hseg
  have hi : i < 9 := List.mem_range.mp hi
  unfold preparedRecordsD1 preparedRecords
  rw [descriptor_index, blocksD1_getD q hi]

/-- **Off the new pairs, the D1 records are D0a's.** -/
theorem preparedD1_pubIdx_recs (AP : AirP) (q : PrepD1) (ov : Nat) (hseg : AP.pubSegs = preparedSegmentsD1)
    (hr : RootsSized q.base) (hs : ∀ s ∈ q.base.lists, s.root.length = 32)
    (hleaves : ∀ l ∈ q.leaves, l.length = 32) (hlen : (preparedBytesD1 q ov).length < 256 ^ 4)
    (bus : Nat) (side : Bool) (hb : (bus, side) ∉ newPairs) :
    (preparedD1_pubIdx AP q ov hseg hr hs hleaves hlen).recs bus side = preparedOn q.base bus side := by
  change (AP.pubSegs.filter _).flatMap (preparedRecordsD1 q) = _
  rw [hseg, preparedSegmentsD1_split, List.filter_append, List.flatMap_append]
  have hnew : newSegs.filter (fun s => decide (s.bus = bus ∧ s.send = side)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs' he
    have := newSegs_pairs s hs'
    simp only [decide_eq_true_eq] at he
    rw [he.1, he.2] at this
    exact hb this
  rw [hnew, List.flatMap_nil, List.append_nil]
  unfold preparedOn
  apply ZkFormal.Near.flatMap_congr'
  intro s hs'
  exact preparedRecordsD1_old q (List.mem_filter.mp hs').1

end ZkFormal.NearV3.D1.Link
