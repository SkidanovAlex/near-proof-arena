import NearCompression.HonestBlockSequence

/-! Group only consecutive requests in the same block; preserve all write order. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def prependBlockRequest (block : Nat) (r : Nat × UInt8) : List BlockBatchPlan → List BlockBatchPlan
  | [] => [⟨r.1 / block, [(r.1 % block, r.2)]⟩]
  | p :: ps => if p.index = r.1 / block then
      { p with writes := (r.1 % block, r.2) :: p.writes } :: ps
    else ⟨r.1 / block, [(r.1 % block, r.2)]⟩ :: p :: ps

def groupBlockRequests (block : Nat) : List (Nat × UInt8) → List BlockBatchPlan
  | [] => []
  | r :: rs => prependBlockRequest block r (groupBlockRequests block rs)

theorem prepend_block_request_exact (block : Nat) (r : Nat × UInt8) (plan : List BlockBatchPlan) :
    blockPlanRequests block (prependBlockRequest block r plan) = r :: blockPlanRequests block plan := by
  have address : r.1 / block * block + r.1 % block = r.1 := by
    simpa [Nat.mul_comm] using Nat.div_add_mod r.1 block
  cases plan with
  | nil => simp [prependBlockRequest, blockPlanRequests, blockBatchRequests, address]
  | cons p ps =>
    simp only [prependBlockRequest]
    split
    · rename_i same
      simp [blockPlanRequests, blockBatchRequests, same, address]
    · simp [blockPlanRequests, blockBatchRequests, address]

theorem grouped_block_requests_exact (block : Nat) (requests : List (Nat × UInt8)) :
    blockPlanRequests block (groupBlockRequests block requests) = requests := by
  induction requests with
  | nil => rfl
  | cons r rs ih => rw [groupBlockRequests, prepend_block_request_exact, ih]

def blockPlanValid (block allocated : Nat) (plan : List BlockBatchPlan) : Prop :=
  ∀ p ∈ plan, p.index < allocated ∧ ∀ w ∈ p.writes, w.1 < block

theorem prepend_block_request_valid (block allocated : Nat) (positive : 0 < block)
    (r : Nat × UInt8) (bound : r.1 / block < allocated) (plan : List BlockBatchPlan)
    (valid : blockPlanValid block allocated plan) :
    blockPlanValid block allocated (prependBlockRequest block r plan) := by
  have offset : r.1 % block < block := Nat.mod_lt _ positive
  cases plan with
  | nil =>
    intro p hp
    simp only [prependBlockRequest, List.mem_singleton] at hp
    subst p
    refine ⟨bound, ?_⟩
    intro w hw
    have equal := List.mem_singleton.mp hw
    subst w
    exact offset
  | cons p ps =>
    have first := valid p (by simp)
    simp only [prependBlockRequest]
    split
    · intro q hq
      rcases List.mem_cons.mp hq with same | tail
      · subst q
        refine ⟨first.1, ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with equal | rest
        · subst w; exact offset
        · exact first.2 w rest
      · exact valid q (List.mem_cons_of_mem _ tail)
    · intro q hq
      rcases List.mem_cons.mp hq with same | tail
      · subst q
        refine ⟨bound, ?_⟩
        intro w hw
        have equal := List.mem_singleton.mp hw
        subst w
        exact offset
      · exact valid q tail

theorem grouped_block_requests_valid (block allocated : Nat) (positive : 0 < block)
    (requests : List (Nat × UInt8)) (bounds : ∀ r ∈ requests, r.1 / block < allocated) :
    blockPlanValid block allocated (groupBlockRequests block requests) := by
  induction requests with
  | nil => simp [groupBlockRequests, blockPlanValid]
  | cons r rs ih =>
    exact prepend_block_request_valid block allocated positive r (bounds r (by simp)) _
      (ih (fun q hq => bounds q (by simp [hq])))

def honestWriteBytesWitness (hash : Bytes → ByteArray) (s : St) (block count depth address : Nat)
    (data : ByteArray) : List PageBatchWitness :=
  honestBlockSequence hash block count depth s
    (groupBlockRequests block (byteWriteRequests address data))

theorem honest_write_bytes_witness_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (data : ByteArray)
    (inBounds : address + data.size ≤ s.pages.size * pageSize) :
    checkBlockBatchedWriteBytes hash (describeSubpageMemory hash s block count depth) address data
      (honestWriteBytesWitness hash s block count depth address data) =
      some (describeSubpageMemory hash (writeBytes s address data) block count depth) := by
  have bounds : ∀ r ∈ byteWriteRequests address data, r.1 / block < s.pages.size * count := by
    intro r member
    obtain ⟨i, hi, equal⟩ := List.mem_map.mp member
    subst r
    have hib : i < data.size := by simpa [List.mem_range'] using hi
    apply global_block_allocated s.pages (address + i) block count layout
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < pageSize)).mpr
    omega
  exact honest_block_batched_bytes_accepted hash digestBound block count depth positive layout s full capacity
    address data _ (grouped_block_requests_valid block _ positive _ bounds)
    (grouped_block_requests_exact block _)

end NearCompression
