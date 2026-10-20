import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.D1.Public.PreparedD1Defs

/-!
# `ZkFormal.NearV3.D1.Public.Layout` — segment records of the D1 tape (P0, part 2)

Lane `v3-d1-phase2`, item P0.  The D1 tape is `encodeD1 header ext blocks = header ‖
metadata ‖ ext ‖ data`: D0a's `encode` with the extension inserted before the payloads, so
that the metadata offsets start at `dataStartD1 = |header| + 8·|blocks| + |ext|`.  The three
packing facts of D0a's `Public.Layout` (count, offset, payload bytes) hold with this start
(`encodeD1_count`, `encodeD1_offset`, `encodeD1_payload`).  Hence D0a's segment lemmas carry
over (`descriptorD1_count`, `descriptorD1_offset`, `descriptorD1_record`, `descriptorD1_msgs`):
every descriptor `i` of the D1 tape reads exactly block `i`'s records.
-/

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 ZkFormal.Algebra ZkFormal.NearV3.Public

def dataStartD1 (header ext : ByteString) (blocks : List Payload) : Nat :=
  header.length + 8 * blocks.length + ext.length

theorem getD_middle_r (pre mid post : ByteString) {i : Nat} (hi : i < mid.length) :
    (pre ++ (mid ++ post)).getD (pre.length + i) 0 = mid.getD i 0 := by
  rw [← List.append_assoc]; exact getD_middle pre mid post hi

theorem encodeD1_count (header ext : ByteString) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (encodeD1 header ext blocks).getD (header.length + 8 * i + k) 0 =
      (NearSpec.u32 (blocks.getD i []).length).getD k 0 := by
  unfold encodeD1
  simp only [List.append_assoc]
  rw [show header.length + 8 * i + k = header.length + (8 * i + k) by omega,
    getD_middle_r _ _ _ (by rw [metadata_length]; omega)]
  exact metadata_count _ _ hi hk

theorem encodeD1_offset (header ext : ByteString) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (encodeD1 header ext blocks).getD (header.length + 8 * i + 4 + k) 0 =
      (NearSpec.u32 (payloadOffset (dataStartD1 header ext blocks) blocks i)).getD k 0 := by
  unfold encodeD1
  simp only [List.append_assoc]
  rw [show header.length + 8 * i + 4 + k = header.length + (8 * i + 4 + k) by omega,
    getD_middle_r _ _ _ (by rw [metadata_length]; omega)]
  exact metadata_offset _ _ hi hk

theorem encodeD1_payload (header ext : ByteString) (blocks : List Payload) {i c : Nat}
    (hi : i < blocks.length) (hc : c < (payloadBytes (blocks.getD i [])).length) :
    (encodeD1 header ext blocks).getD (payloadOffset (dataStartD1 header ext blocks) blocks i + c) 0 =
      (payloadBytes (blocks.getD i [])).getD c 0 := by
  unfold encodeD1
  have he : payloadOffset (dataStartD1 header ext blocks) blocks i + c =
      (header ++ metadata (header.length + 8 * blocks.length + ext.length) blocks ++ ext).length +
        ((dataBytes (blocks.take i)).length + c) := by
    simp [payloadOffset, dataStartD1, metadata_length, Nat.add_assoc]
  rw [he, getD_right]
  exact data_getD blocks hi hc

theorem descriptorD1_count (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length) (hn : (blocks.getD i []).length < 256 ^ 4) :
    (descriptor plan header.length i).count (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) =
      (blocks.getD i []).length := by
  apply count_of_u32 _ _ _ hn
  intro k hk
  rw [pub_getD]
  exact congrArg byteF (encodeD1_count header ext blocks hi hk)

theorem descriptorD1_offset (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length)
    (ho : payloadOffset (dataStartD1 header ext blocks) blocks i < 256 ^ 4) :
    (descriptor plan header.length i).startOffset (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) =
      payloadOffset (dataStartD1 header ext blocks) blocks i := by
  apply offset_of_u32 _ _ _ _ rfl ho
  intro k hk
  rw [pub_getD]
  exact congrArg byteF (encodeD1_offset header ext blocks hi hk)

theorem descriptorD1_record (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i j : Nat} (hi : i < blocks.length) (hj : j < (blocks.getD i []).length)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (ho : payloadOffset (dataStartD1 header ext blocks) blocks i < 256 ^ 4) :
    (descriptor plan header.length i).record (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) j =
      recordValues plan j ((blocks.getD i []).getD j []) := by
  have hr : ((blocks.getD i []).getD j []).length = plan.width := by
    apply hw
    rw [← List.getElem_eq_getD (h := hj) []]
    exact List.getElem_mem hj
  simp only [PubSeg.record, recordValues]
  change _ ++ _ ++ (List.range plan.width).map _ = _ ++ _ ++ _
  congr 1
  apply List.ext_getElem (by simpa only [List.length_map, List.length_range] using hr.symm)
  intro c hc hc'
  have hc0 : c < plan.width := by simpa using hc
  simp only [List.getElem_map, List.getElem_range]
  change (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)).getD
    ((descriptor plan header.length i).startOffset (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) +
      j * plan.width + c) 0 = _
  rw [descriptorD1_offset plan header ext blocks hi ho, pub_getD]
  rw [Nat.add_assoc, encodeD1_payload header ext blocks hi (by
    rw [payload_length _ _ hw]
    have := Nat.mul_le_mul_right plan.width (show j + 1 ≤ (blocks.getD i []).length by omega)
    simp only [Nat.add_mul, Nat.one_mul] at this
    omega), payload_getD _ _ hw hj hc0]
  rw [← List.getElem_eq_getD (h := (show c < ((blocks.getD i []).getD j []).length by omega)) 0]

/-- **Every D1 descriptor reads its block's records** (D0a's `descriptor_msgs` for
`encodeD1`). -/
theorem descriptorD1_msgs (plan : PubSeg) (header ext : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length)
    (hn : (blocks.getD i []).length < 256 ^ 4)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (ho : payloadOffset (dataStartD1 header ext blocks) blocks i < 256 ^ 4) :
    (descriptor plan header.length i).msgs (ZkFormal.Udr.pubOf Fp (encodeD1 header ext blocks)) =
      (List.range (blocks.getD i []).length).map
        (fun j => recordValues plan j ((blocks.getD i []).getD j [])) := by
  unfold PubSeg.msgs
  rw [descriptorD1_count plan header ext blocks hi hn]
  apply List.map_congr_left
  intro j hj
  exact descriptorD1_record plan header ext blocks hi (List.mem_range.mp hj) hw ho

end ZkFormal.NearV3.D1.Public
