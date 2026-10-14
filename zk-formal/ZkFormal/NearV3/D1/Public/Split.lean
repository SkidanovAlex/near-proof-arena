import ZkFormal.NearV3.D1.Public.Layout
import ZkFormal.NearV3.D1.Public.Ext
import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.NearV3.Public.PreparedFit
import ZkFormal.Near.Extract.Segments

/-!
# `ZkFormal.NearV3.D1.Public.Split` — the D1 public messages are D0a's plus six segments (P0, part 3)

Lane `v3-d1-phase2`, item P0.  `nearAirV3D1`'s 15 descriptors are D0a's nine
(`plansD1 = plans ++ …`) and six more.  The D1 tape's blocks `0 … 8` are D0a's blocks of
`p.base`, so each of the nine D0a descriptors reads the same records from the D1 tape as from
D0a's tape `preparedBytes p.base ov` (`descriptorD1_eq`).  Hence

  `pubMsgs nearAirV3D1 (pubOf D1-tape) = pubMsgs nearAirV3 (pubOf D0a-tape) ++ newMsgs`

(`pubMsgsD1_split`), and `pubCount` splits additively (`pubCountD1_split`): every D0a fact
about the public traffic of `prepD0`'s tape transfers to the D1 tape, for `p.base`.
-/

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 ZkFormal.Algebra NearSpecV3 ZkFormal.NearV3.Public ZkFormal.NearV3.D1

theorem encodeD1_length (header ext : ByteString) (blocks : List Payload) :
    (encodeD1 header ext blocks).length = dataStartD1 header ext blocks + (dataBytes blocks).length := by
  simp [encodeD1, dataStartD1, metadata_length, Nat.add_assoc]

theorem descriptorD1_u32_bounds (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length) (hp : 0 < plan.width)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (hlen : (encodeD1 header ext blocks).length < 256 ^ 4) :
    (blocks.getD i []).length < 256 ^ 4 ∧
      payloadOffset (dataStartD1 header ext blocks) blocks i < 256 ^ 4 := by
  have hb := data_block_bound blocks hi
  rw [payload_length _ _ hw] at hb
  have hm : (blocks.getD i []).length ≤ (blocks.getD i []).length * plan.width := by
    have := Nat.mul_le_mul_left (blocks.getD i []).length hp
    simpa using this
  rw [encodeD1_length] at hlen
  unfold payloadOffset
  constructor <;> omega

theorem plansD1_getD {i : Nat} (hi : i < 9) : plansD1.getD i sourcePlan = plans.getD i sourcePlan := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem blocksD1_getD (p : PrepD1) {i : Nat} (hi : i < 9) :
    (preparedBlocksD1 p).getD i [] = (preparedBlocks p.base).getD i [] := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

variable (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
  (hs : ∀ s ∈ p.base.lists, s.root.length = 32)
  (hlen : (preparedBytesD1 p ov).length < 256 ^ 4)
include hr hs hlen

theorem prepared_base_length_le : (preparedBytes p.base ov).length ≤ (preparedBytesD1 p ov).length := by
  have h0 := encode_length (headerBytes p.base ov) (preparedBlocks p.base)
  have h1 := encodeD1_length (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p)
  have e0 : preparedBytes p.base ov = encode (headerBytes p.base ov) (preparedBlocks p.base) := rfl
  have e1 : preparedBytesD1 p ov = encodeD1 (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p) := rfl
  have hd : dataBytes (preparedBlocksD1 p) = dataBytes (preparedBlocks p.base) ++
      dataBytes [prefixPayload p.base.body p.o0, txpPayload p.ops, sigPayload p.ops, keyPayload p.walks,
        leafPayload p.leaves, ridPayload p.rids] := by
    simp only [preparedBlocksD1, dataBytes, List.flatMap_append]
  rw [e0, e1, h0, h1, prepared_dataStart p.base ov hr, hd, List.length_append]
  unfold dataStartD1
  rw [headerBytesD1_length p ov hr, preparedBlocksD1_length, extBytes_length]
  simp only [EXT_LEN]; omega

/-- **Each D0a descriptor reads the same records from the D1 tape.** -/
theorem descriptorD1_eq {i : Nat} (hi : i < 9) :
    (descriptor (plans.getD i sourcePlan) 202 i).msgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) =
      (descriptor (plans.getD i sourcePlan) 202 i).msgs (ZkFormal.Udr.pubOf Fp (preparedBytes p.base ov)) := by
  have hw := prepared_width p.base hr hs hi
  have hp := plan_width_positive hi
  have hi1 : i < (preparedBlocksD1 p).length := by rw [preparedBlocksD1_length]; omega
  have hi0 : i < (preparedBlocks p.base).length := by rw [preparedBlocks_length]; exact hi
  have hw1 : ∀ row ∈ (preparedBlocksD1 p).getD i [], row.length = (plans.getD i sourcePlan).width := by
    rw [blocksD1_getD p hi]; exact hw
  obtain ⟨hn1, ho1⟩ := descriptorD1_u32_bounds _ (headerBytesD1 p ov) (extBytes p) _ hi1 hp hw1 hlen
  have hlen0 : (encode (headerBytes p.base ov) (preparedBlocks p.base)).length < 256 ^ 4 := by
    have := prepared_base_length_le p ov hr hs hlen
    exact Nat.lt_of_le_of_lt this hlen
  obtain ⟨hn0, ho0⟩ := descriptor_u32_bounds _ (headerBytes p.base ov) _ hi0 hp hw hlen0
  have e1 := descriptorD1_msgs (plans.getD i sourcePlan) (headerBytesD1 p ov) (extBytes p)
    (preparedBlocksD1 p) hi1 hn1 hw1 ho1
  have e0 := descriptor_msgs (plans.getD i sourcePlan) (headerBytes p.base ov) (preparedBlocks p.base)
    hi0 hn0 hw ho0
  rw [headerBytesD1_length p ov hr] at e1
  rw [headerBytes_length p.base ov hr] at e0
  unfold preparedBytesD1 preparedBytes
  rw [e1, e0, blocksD1_getD p hi]

/-- The six D1 segments. -/
def newSegs : List PubSeg := (List.range 6).map fun k => descriptor (plansD1.getD (9 + k) sourcePlan) 202 (9 + k)

/-- The public messages of the six D1 segments. -/
def newMsgs (pub : List Fp) : List (Nat × Bool × List Fp) :=
  newSegs.flatMap fun s => (s.msgs pub).map fun m => (s.bus, s.send, m)

omit hr hs hlen in
theorem preparedSegmentsD1_split : preparedSegmentsD1 = preparedSegments ++ newSegs := by
  rfl

omit hr hs hlen in
theorem preparedSegments_eq :
    preparedSegments = (List.range 9).map fun i => descriptor (plans.getD i sourcePlan) 202 i := rfl

/-- **The D1 public messages are D0a's (for `p.base`) and the six new segments'.** -/
theorem pubMsgsD1_split :
    pubMsgs nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) =
      pubMsgs ZkFormal.NearV3.Assembly.nearAirV3 (ZkFormal.Udr.pubOf Fp (preparedBytes p.base ov)) ++
        newMsgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) := by
  have key : (preparedSegments.flatMap fun s =>
      (s.msgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))).map fun m => (s.bus, s.send, m)) =
      (preparedSegments.flatMap fun s =>
      (s.msgs (ZkFormal.Udr.pubOf Fp (preparedBytes p.base ov))).map fun m => (s.bus, s.send, m)) := by
    rw [preparedSegments_eq, List.flatMap_map, List.flatMap_map]
    apply ZkFormal.Near.flatMap_congr'
    intro i hi
    rw [descriptorD1_eq p ov hr hs hlen (List.mem_range.mp hi)]
  unfold pubMsgs newMsgs
  rw [show nearAirV3D1.pubSegs = preparedSegmentsD1 from rfl,
    show ZkFormal.NearV3.Assembly.nearAirV3.pubSegs = preparedSegments from rfl,
    preparedSegmentsD1_split, List.flatMap_append, key]

theorem pubCountD1_split (b : Nat) (s : Bool) (m : List Fp) :
    pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) b s m =
      pubCount ZkFormal.NearV3.Assembly.nearAirV3 (ZkFormal.Udr.pubOf Fp (preparedBytes p.base ov)) b s m +
        ((newMsgs (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))).filter
          fun x => decide (x = (b, s, m))).length := by
  unfold pubCount
  rw [pubMsgsD1_split p ov hr hs hlen, List.filter_append, List.length_append]

end ZkFormal.NearV3.D1.Public
