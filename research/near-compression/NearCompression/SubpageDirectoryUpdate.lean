import NearCompression.SubpageIndex

/-! Whole-directory byte update refinement, including non-target blocks. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem global_subpage_write_other (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (other : index ≠ address / block) (value : UInt8) :
    globalSubpageAt (writeByte s address value).pages block count index =
      globalSubpageAt s.pages block count index := by
  have countPos : 0 < count := by
    by_cases hz : count = 0
    · simp [hz, pageSize] at layout
    · omega
  simp only [globalSubpageAt, writeByte, Array.getElem?_modify]
  by_cases samePage : address / pageSize = index / count
  · rw [if_pos samePage, ← samePage, present]
    simp only [Option.map_some]
    have different : (address % pageSize) / block ≠ index % count := by
      intro he
      apply other
      apply Nat.ext_div_mod (n := count)
      · rw [global_block_page_index _ _ _ layout]; exact samePage.symm
      · rw [global_block_local_index _ _ _ layout]; exact he.symm
    have region : block * (index % count) + block ≤ page.size := by
      have h := Nat.mul_le_mul_left block (Nat.mod_lt index countPos)
      simpa only [Nat.mul_succ, layout, full] using h
    have outside : address % pageSize < block * (index % count) ∨
        block * (index % count) + block ≤ address % pageSize := by
      by_cases lo : address % pageSize < block * (index % count)
      · exact Or.inl lo
      · by_cases hi : address % pageSize < block * (index % count) + block
        · have eq : (address % pageSize) / block = index % count :=
            Nat.div_eq_of_lt_le (by simpa only [Nat.mul_comm] using Nat.le_of_not_gt lo)
              (by simpa only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm] using hi)
          exact False.elim (different eq)
        · exact Or.inr (by omega)
    congr 1
    exact extract_write_outside page _ block (address % pageSize) region
      (by rw [full]; exact Nat.mod_lt _ (by decide)) outside value
  · rw [if_neg samePage]

theorem subpage_directory_write_other (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (other : index ≠ address / block) (value : UInt8) :
    (subpageDirectory (writeByte s address value).pages block count)[index]? =
      (subpageDirectory s.pages block count)[index]? := by
  by_cases hi : index < s.pages.size * count
  · have hi' : index < (writeByte s address value).pages.size * count := by
      simpa only [writeByte, Array.size_modify] using hi
    rw [subpage_directory_lookup _ _ _ _ hi', subpage_directory_lookup _ _ _ _ hi,
      global_subpage_write_other s address page present full block count index positive layout other value]
  · simp [subpageDirectory, writeByte, hi]

theorem subpage_directory_write_exact (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) (value : UInt8) :
    subpageDirectory (writeByte s address value).pages block count =
      (subpageDirectory s.pages block count).modify (address / block)
        (fun p => p.set! (address % block) value) := by
  apply Array.ext_getElem?
  intro index
  rw [Array.getElem?_modify]
  by_cases same : address / block = index
  · subst index
    rw [if_pos rfl, subpage_directory_write_target s address page present full block count positive layout value]
    have hi := global_block_allocated s.pages address block count layout (Array.getElem?_eq_some_iff.mp present).1
    rw [subpage_directory_lookup _ _ _ _ hi, global_subpage_lookup _ _ _ _ layout page present]
    rfl
  · rw [if_neg same]
    exact subpage_directory_write_other s address page present full block count index positive layout
      (Ne.symm same) value

end NearCompression
