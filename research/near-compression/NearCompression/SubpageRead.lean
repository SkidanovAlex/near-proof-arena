import NearCompression.PageBatchChain

/-! Parameterized subpage read refinement. This does not reuse the page-tree
commitment domain for subpages or change the Wasm allocation granularity. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def extractSubpage (page : ByteArray) (block offset : Nat) : ByteArray :=
  page.extract (block * (offset / block)) (block * (offset / block) + block)

theorem bounded_extract_read (page : ByteArray) (start length offset : Nat)
    (region : start + length ≤ page.size) (inside : offset < length) :
    (page.extract start (start + length))[offset]! = page[start + offset]! := by
  have hs : (page.extract start (start + length)).size = length := by
    rw [ByteArray.size_extract, Nat.min_eq_left region]
    omega
  rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
  exact ByteArray.getElem_extract _

theorem subpage_region_bound (block count offset : Nat) (positive : 0 < block)
    (layout : block * count = pageSize) (inside : offset < pageSize) :
    block * (offset / block) + block ≤ pageSize := by
  have hq : offset / block < count := (Nat.div_lt_iff_lt_mul positive).mpr (by
    simpa only [Nat.mul_comm, layout] using inside)
  have h := Nat.mul_le_mul_left block hq
  simpa only [Nat.mul_succ, layout] using h

theorem subpage_size (page : ByteArray) (full : page.size = pageSize)
    (block count offset : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (inside : offset < pageSize) : (extractSubpage page block offset).size = block := by
  have h := subpage_region_bound block count offset positive layout inside
  simp only [extractSubpage, ByteArray.size_extract, full, Nat.min_eq_left h]
  omega

theorem subpage_read (page : ByteArray) (full : page.size = pageSize)
    (block count offset : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (inside : offset < pageSize) :
    (extractSubpage page block offset)[offset % block]! = page[offset]! := by
  have h := subpage_region_bound block count offset positive layout inside
  have hm := Nat.mod_lt offset positive
  have he := bounded_extract_read page (block * (offset / block)) block (offset % block) (by omega) hm
  simpa only [extractSubpage, Nat.div_add_mod] using he

theorem wasm_read_subpage (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) :
    readByte s address = (extractSubpage page block (address % pageSize))[(address % pageSize) % block]! := by
  have he := subpage_read page full block count (address % pageSize) positive layout
    (Nat.mod_lt address (by decide))
  simp only [readByte, present]
  rw [he]
  have hi : address % pageSize < page.size := by rw [full]; exact Nat.mod_lt _ (by decide)
  simp [ByteArray.get!, getElem!_pos, hi, ByteArray.getElem_eq_getElem_data]

-- Candidate layouts from the measured sweep preserve the allocation granularity.
example : 1024 * 64 = pageSize := by decide +kernel
example : 4096 * 16 = pageSize := by decide +kernel

end NearCompression
