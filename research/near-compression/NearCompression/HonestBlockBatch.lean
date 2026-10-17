import NearCompression.BlockBatchChain

/-! Honest witness construction and unconditional batch completeness.
The constructor rebuilds trees and is a reference algorithm, not an optimized prover. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem built_page_opening_wf (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (pages : Array ByteArray)
    (depth offset index : Nat) : pageOpeningWf (buildPageOpening hash pages depth offset index) := by
  have rootWf : ∀ t, bytesWireWf (pageTreeRoot hash t) := by
    intro t; cases t <;> exact digestBound _
  induction depth generalizing offset index with
  | zero => simp [buildPageOpening, pageOpeningWf]
  | succ depth ih =>
    simp only [buildPageOpening]
    split <;> intro x hx
    all_goals
      rcases List.mem_cons.mp hx with same | member
      · subst x; exact rootWf _
      · exact (ih _ _) x member

def honestBlockBatch (hash : Bytes → ByteArray) (s : St) (block count depth index : Nat)
    (writes : List (Nat × UInt8)) : PageBatchWitness :=
  { index, page := memoryPageAt (subpageDirectory s.pages block count) index,
    path := buildPageOpening (blockTreeHash hash block) (subpageDirectory s.pages block count) depth 0 index,
    writes }

theorem honest_block_batch_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : index < s.pages.size * count)
    (writes : List (Nat × UInt8)) (fits : ∀ w ∈ writes, w.1 < block) :
    let witness := honestBlockBatch hash s block count depth index writes
    checkBlockBatch hash (describeSubpageMemory hash s block count depth)
      witness.index witness.page witness.path witness.writes =
      some (describeSubpageMemory hash
        (executeByteRequests s (blockBatchRequests block index writes)) block count depth) := by
  dsimp only [honestBlockBatch]
  let directory := subpageDirectory s.pages block count
  have hi : index < directory.size := by simpa [directory, subpageDirectory] using allocated
  have member : memoryPageAt directory index ∈ directory.toList := by
    simp [memoryPageAt, Array.getElem?_eq_getElem hi]
  have size : (memoryPageAt directory index).size = block :=
    subpage_directory_entry_size s.pages full block count layout _ member
  have pageWf : bytesWireWf (memoryPageAt directory index) :=
    subpage_directory_wire_wf s.pages full block count layout _ member
  have pathWf := built_page_opening_wf (blockTreeHash hash block) (fun bs => digestBound _) directory depth 0 index
  have witnessWf : checkWriteWitnessWf
      ⟨0, 0, memoryPageAt directory index, buildPageOpening (blockTreeHash hash block) directory depth 0 index⟩ = true :=
    (check_write_witness_wf_correct _).mpr ⟨pageWf, pathWf⟩
  have root : pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth) =
      pageOpeningRoot (blockTreeHash hash block) (memoryPageAt directory index)
        (buildPageOpening (blockTreeHash hash block) directory depth 0 index) := by
    simpa only [Nat.zero_add, directory, buildSubpageTree] using
      (built_page_opening_root (blockTreeHash hash block) directory depth 0 index (by omega)).symm
  have updated : pageTreeRoot (blockTreeHash hash block)
      (buildSubpageTree (executeByteRequests s (blockBatchRequests block index writes)) block count depth) =
      pageOpeningRoot (blockTreeHash hash block) (applyPageWrites (memoryPageAt directory index) writes)
        (buildPageOpening (blockTreeHash hash block) directory depth 0 index) := by
    rw [block_batch_tree_exact s full block count depth index positive layout capacity allocated writes fits,
      built_opening_replacement_root]
    rfl
  dsimp only [directory] at size witnessWf root updated
  unfold checkBlockBatch
  dsimp only [describeSubpageMemory]
  have fitCheck : writes.all (fun w => decide (w.1 < block)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]; exact fits
  simp only [size, witnessWf, fitCheck, built_page_opening_directions, root,
    positive, layout, capacity, allocated, decide_true, Bool.true_and, Bool.and_true,
    decide_eq_true_eq, ite_true, beq_self_eq_true]
  rw [execute_byte_requests_page_count, updated]
  split
  · rfl
  · rename_i rejected
    exact False.elim (rejected fitCheck)

end NearCompression
