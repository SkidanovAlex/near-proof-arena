import NearCompression.ChunkOrdinalCoverage
namespace NearCompression

/-- The final interval contains only the remaining real nodes, without inventing
padding nodes or requiring a full-size last compression chunk. -/
def chunkNodeCount (total capacity chunk : Nat) : Nat := min capacity (total-capacity*chunk)

theorem chunk_node_count_le (total capacity chunk : Nat) : chunkNodeCount total capacity chunk≤capacity :=
  Nat.min_le_left _ _

/-- A declared node belongs to the exact possibly-short final interval. -/
theorem chunk_owner_interval (total capacity node : Nat) (positive : 0<capacity) (bound : node<total) :
    0<chunkNodeCount total capacity (node/capacity) ∧
      capacity*(node/capacity)+chunkNodeCount total capacity (node/capacity)≤total ∧
      node%capacity<chunkNodeCount total capacity (node/capacity) := by
  have decomposition := Nat.div_add_mod node capacity
  have remainder := Nat.mod_lt node positive
  unfold chunkNodeCount
  omega

/-- Exact local/global coordinate reconstruction preserves natural IDs. -/
theorem chunk_global_local (capacity node : Nat) : capacity*(node/capacity)+node%capacity=node :=
  Nat.div_add_mod node capacity

end NearCompression
