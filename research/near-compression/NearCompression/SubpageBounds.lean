import NearCompression.FullPages

/-! Derive block sizes and encoding bounds from full Wasm pages and layout. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem subpage_count_positive (block count : Nat) (layout : block * count = pageSize) : 0 < count := by
  by_cases hz : count = 0
  · simp [hz, pageSize] at layout
  · omega

theorem subpage_block_bound (block count : Nat) (layout : block * count = pageSize) : block ≤ pageSize :=
  Nat.le_of_dvd (by decide) ⟨count, layout.symm⟩

theorem allocated_subpage_exists (pages : Array ByteArray) (full : fullPages pages)
    (block count index : Nat) (layout : block * count = pageSize)
    (allocated : index < pages.size * count) :
    ∃ p, globalSubpageAt pages block count index = some p ∧ p.size = block := by
  have hc := subpage_count_positive block count layout
  have hi : index / count < pages.size := (Nat.div_lt_iff_lt_mul hc).mpr allocated
  let original := pages[index / count]
  have present : pages[index / count]? = some original := by simp [original, hi]
  have hp : original.size = pageSize := full original (by simp [original])
  have region : block * (index % count) + block ≤ original.size := by
    have h := Nat.mul_le_mul_left block (Nat.mod_lt index hc)
    simpa only [Nat.mul_succ, layout, hp] using h
  refine ⟨original.extract (block * (index % count)) (block * (index % count) + block), ?_, ?_⟩
  · simp only [globalSubpageAt, present, Option.map_some]
  · rw [ByteArray.size_extract, Nat.min_eq_left region]
    omega

theorem subpage_directory_entry_size (pages : Array ByteArray) (full : fullPages pages)
    (block count : Nat) (layout : block * count = pageSize)
    (p : ByteArray) (member : p ∈ (subpageDirectory pages block count).toList) : p.size = block := by
  obtain ⟨index, hi, he⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
  have bound : index < pages.size * count := by simpa [subpageDirectory] using hi
  obtain ⟨q, hq, size⟩ := allocated_subpage_exists pages full block count index layout bound
  have lookup := subpage_directory_lookup pages block count index bound
  rw [hq] at lookup
  have hp : (subpageDirectory pages block count)[index]? = some p := by
    rw [Array.getElem?_eq_getElem hi, he]
  rw [hp] at lookup
  have same : p = q := Option.some.inj lookup
  exact same ▸ size

theorem subpage_directory_wire_wf (pages : Array ByteArray) (full : fullPages pages)
    (block count : Nat) (layout : block * count = pageSize) :
    ∀ p ∈ (subpageDirectory pages block count).toList, bytesWireWf p := by
  intro p hp
  have hs := subpage_directory_entry_size pages full block count layout p hp
  have hb := subpage_block_bound block count layout
  simp only [bytesWireWf, Array.length_toList, ByteArray.size_data]
  rw [hs]
  have : pageSize < 4294967296 := by decide
  omega

end NearCompression
