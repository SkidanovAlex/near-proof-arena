import ZkFormal.NearV3.D1.Public.Split

/-!
# `ZkFormal.NearV3.D1.Public.NewSegs` — the six D1 segments' records (P0, part 4)

Lane `v3-d1-phase2`, item P0.  The descriptors `9 … 14` of the D1 tape read the six D1
payloads (`descriptorD1_msgs`): the body prefix, `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`.
`newMsgs_eq` writes the public messages of the six segments as the records of the prepared
data (`recordValues plan j row`, row by row), under the payload widths (`*_width`; the
leaves must be 32-byte digests).
-/

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 ZkFormal.Algebra NearSpecV3 ZkFormal.NearV3.Public ZkFormal.NearV3.D1

theorem prefix_width (body : NearSpec.Bytes) (o0 : Nat) :
    ∀ row ∈ prefixPayload body o0, row.length = bodyPrefixPlan.width := by
  intro row hrow
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hrow
  rfl

theorem txp_width (ops : List TxOp) : ∀ row ∈ txpPayload ops, row.length = txpPlan.width := by
  intro row hrow
  obtain ⟨o, -, hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  simp [opLane, txpPlan]

theorem sig_width (ops : List TxOp) : ∀ row ∈ sigPayload ops, row.length = sigPlan.width := by
  intro row hrow
  obtain ⟨o, -, rfl⟩ := List.mem_map.mp hrow
  rfl

theorem walkRecs_width (k : KeyWalk) : ∀ r ∈ walkRecs k, r.length = 6 := by
  intro r hr
  simp only [walkRecs, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨⟨s, t⟩, -, rfl⟩ | rfl <;> simp

theorem key_width (ws : List KeyWalk) : ∀ row ∈ keyPayload ws, row.length = keyPlan.width := by
  intro row hrow
  obtain ⟨k, -, hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hr
  simp only [List.length_map]
  exact walkRecs_width k r hr'

theorem leaf_width (ls : List NearSpec.Bytes) (hl : ∀ l ∈ ls, l.length = 32) :
    ∀ row ∈ leafPayload ls, row.length = leafPlan.width := hl

theorem rid_width (ids : List NearSpec.Bytes) : ∀ row ∈ ridPayload ids, row.length = ridPlan.width := by
  intro row hrow
  obtain ⟨d, -, hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hr
  rfl

theorem newSegs_eq : newSegs = [descriptor bodyPrefixPlan 202 9, descriptor txpPlan 202 10,
    descriptor sigPlan 202 11, descriptor keyPlan 202 12, descriptor leafPlan 202 13,
    descriptor ridPlan 202 14] := rfl

/-- The public messages of one segment, tagged. -/
def tagged (s : PubSeg) (rows : Payload) : List (Nat × Bool × List Fp) :=
  ((List.range rows.length).map fun j => recordValues s j (rows.getD j [])).map fun m => (s.bus, s.send, m)

variable (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
  (hlen : (preparedBytesD1 p ov).length < 256 ^ 4)
  (hleaves : ∀ l ∈ p.leaves, l.length = 32)
include hr hlen hleaves

theorem newSeg_msgs (plan : PubSeg) {i : Nat} (hi : 9 ≤ i) (hi' : i < 15) (hp : 0 < plan.width)
    (hw : ∀ row ∈ (preparedBlocksD1 p).getD i [], row.length = plan.width) :
    (descriptor plan 202 i).msgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) =
      (List.range ((preparedBlocksD1 p).getD i []).length).map
        (fun j => recordValues plan j (((preparedBlocksD1 p).getD i []).getD j [])) := by
  have hi1 : i < (preparedBlocksD1 p).length := by rw [preparedBlocksD1_length]; exact hi'
  obtain ⟨hn, ho⟩ := descriptorD1_u32_bounds plan (headerBytesD1 p ov) (extBytes p) _ hi1 hp hw hlen
  have e := descriptorD1_msgs plan (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p) hi1 hn hw ho
  rw [headerBytesD1_length p ov hr] at e
  exact e

/-- **The six D1 segments' public messages.** -/
theorem newMsgs_eq :
    newMsgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) =
      tagged bodyPrefixPlan (prefixPayload p.base.body p.o0) ++ tagged txpPlan (txpPayload p.ops) ++
      tagged sigPlan (sigPayload p.ops) ++ tagged keyPlan (keyPayload p.walks) ++
      tagged leafPlan (leafPayload p.leaves) ++ tagged ridPlan (ridPayload p.rids) := by
  unfold newMsgs
  rw [newSegs_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [newSeg_msgs p ov hr hlen hleaves bodyPrefixPlan (i := 9) (by decide) (by decide) (by decide)
      (prefix_width _ _),
    newSeg_msgs p ov hr hlen hleaves txpPlan (i := 10) (by decide) (by decide) (by decide) (txp_width _),
    newSeg_msgs p ov hr hlen hleaves sigPlan (i := 11) (by decide) (by decide) (by decide) (sig_width _),
    newSeg_msgs p ov hr hlen hleaves keyPlan (i := 12) (by decide) (by decide) (by decide) (key_width _),
    newSeg_msgs p ov hr hlen hleaves leafPlan (i := 13) (by decide) (by decide) (by decide)
      (leaf_width _ hleaves),
    newSeg_msgs p ov hr hlen hleaves ridPlan (i := 14) (by decide) (by decide) (by decide) (rid_width _)]
  rfl

end ZkFormal.NearV3.D1.Public

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 ZkFormal.Algebra NearSpecV3 ZkFormal.NearV3.Public ZkFormal.NearV3.D1

theorem descriptorD1_fits (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i maxPub : Nat} (hi : i < blocks.length) (hp : 0 < plan.width)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (hm : (encodeD1 header ext blocks).length ≤ maxPub) (hmax : maxPub < 256 ^ 4) :
    (descriptor plan header.length i).fits maxPub
      (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) = true := by
  obtain ⟨hn, ho⟩ := descriptorD1_u32_bounds plan header ext blocks hi hp hw (by omega)
  have hb := data_block_bound blocks hi
  rw [payload_length _ _ hw] at hb
  have he := encodeD1_length header ext blocks
  unfold PubSeg.fits
  rw [descriptorD1_offset plan header ext blocks hi ho, descriptorD1_count plan header ext blocks hi hn]
  simp only [descriptor, ZkFormal.Udr.pubOf, List.length_map, Bool.and_eq_true, decide_eq_true_eq]
  simp only [payloadOffset] at *
  constructor
  · omega
  · exact decide_eq_true (by omega)

theorem plansD1_width_positive {i : Nat} (hi : i < 15) : 0 < (plansD1.getD i sourcePlan).width := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨
      i=13 ∨ i=14 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem preparedD1_width (p : PrepD1) (hr : RootsSized p.base) (hs : ∀ s ∈ p.base.lists, s.root.length = 32)
    (hleaves : ∀ l ∈ p.leaves, l.length = 32) {i : Nat} (hi : i < 15) :
    ∀ row ∈ (preparedBlocksD1 p).getD i [], row.length = (plansD1.getD i sourcePlan).width := by
  by_cases h9 : i < 9
  · rw [blocksD1_getD p h9, plansD1_getD h9]; exact prepared_width p.base hr hs h9
  · have cases : i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prefix_width _ _
    · exact txp_width _
    · exact sig_width _
    · exact key_width _
    · exact leaf_width _ hleaves
    · exact rid_width _

/-- **Every D1 segment fits** (`pubFit nearAirV3D1`). -/
theorem preparedD1_pubFit (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length ≤ nearAirV3D1.maxPub) :
    pubFit nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) = true := by
  apply List.all_eq_true.mpr
  intro seg hmem
  change seg ∈ preparedSegmentsD1 at hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
  have hi : i < 15 := List.mem_range.mp hi
  have e := descriptorD1_fits (plansD1.getD i sourcePlan) (headerBytesD1 p ov) (extBytes p)
    (preparedBlocksD1 p) (i := i) (maxPub := nearAirV3D1.maxPub)
    (by rw [preparedBlocksD1_length]; exact hi) (plansD1_width_positive hi)
    (preparedD1_width p hr hs hleaves hi) hlen (by decide)
  rw [headerBytesD1_length p ov hr] at e
  exact e

end ZkFormal.NearV3.D1.Public
