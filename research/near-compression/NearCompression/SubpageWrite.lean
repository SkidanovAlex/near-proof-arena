import NearCompression.SubpageRead

/-! Byte writes commute with an in-bounds slice and preserve disjoint slices.
No block commitment or allocation behavior is changed here. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem extract_write_inside (page : ByteArray) (start length offset : Nat)
    (region : start + length ≤ page.size) (inside : offset < length) (value : UInt8) :
    (page.set! (start + offset) value).extract start (start + length) =
      (page.extract start (start + length)).set! offset value := by
  have hs : (page.extract start (start + length)).size = length := by
    simp only [ByteArray.size_extract, Nat.min_eq_left region]; omega
  apply ByteArray.ext
  apply Array.ext
  · simp [ByteArray.size_data, ByteArray.size_extract, ByteArray.size_set!]
  · intro i hi hj
    simp only [ByteArray.size_data] at hi hj
    simp only [← ByteArray.getElem_eq_getElem_data]
    have hi' : i < length := by simpa [ByteArray.size_extract, Nat.min_eq_left region] using hi
    rw [ByteArray.getElem_extract, ByteArray.getElem_set! page (start + offset) (start + i) value (by omega) (by omega),
      ByteArray.getElem_set! (page.extract start (start + length)) offset i value (by omega) (by omega)]
    simp only [ByteArray.getElem_extract]
    by_cases he : offset = i
    · subst i; simp
    · simp [he]

theorem extract_write_outside (page : ByteArray) (start length target : Nat)
    (region : start + length ≤ page.size) (allocated : target < page.size)
    (outside : target < start ∨ start + length ≤ target) (value : UInt8) :
    (page.set! target value).extract start (start + length) = page.extract start (start + length) := by
  apply ByteArray.ext
  apply Array.ext
  · simp [ByteArray.size_data, ByteArray.size_extract, ByteArray.size_set!]
  · intro i hi hj
    simp only [ByteArray.size_data] at hi hj
    simp only [← ByteArray.getElem_eq_getElem_data]
    have hi' : i < length := by simpa [ByteArray.size_extract, Nat.min_eq_left region] using hi
    rw [ByteArray.getElem_extract, ByteArray.getElem_set! page target (start + i) value allocated (by omega),
      ByteArray.getElem_extract]
    have hne : target ≠ start + i := by omega
    simp [hne]

theorem subpage_write (page : ByteArray) (full : page.size = pageSize)
    (block count offset : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (inside : offset < pageSize) (value : UInt8) :
    extractSubpage (page.set! offset value) block offset =
      (extractSubpage page block offset).set! (offset % block) value := by
  have h := subpage_region_bound block count offset positive layout inside
  have he := extract_write_inside page (block * (offset / block)) block (offset % block)
    (by omega) (Nat.mod_lt offset positive) value
  simpa only [extractSubpage, Nat.div_add_mod] using he

theorem wasm_write_subpage (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) (value : UInt8) :
    ((writeByte s address value).pages[address / pageSize]?).map
      (fun p => extractSubpage p block (address % pageSize)) =
    some ((extractSubpage page block (address % pageSize)).set! ((address % pageSize) % block) value) := by
  simp only [writeByte, Array.getElem?_modify, if_true, present, Option.map_some]
  rw [subpage_write page full block count (address % pageSize) positive layout
    (Nat.mod_lt address (by decide)) value]

end NearCompression
