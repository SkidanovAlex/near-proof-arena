import NearCompression.SubpageWrite

/-! Global subpage indices agree with actual Wasm page/offset addressing.
The directory is finite data, not yet an authenticated block-tree commitment. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def globalSubpageAt (pages : Array ByteArray) (block count index : Nat) : Option ByteArray :=
  (pages[index / count]?).map (fun page =>
    page.extract (block * (index % count)) (block * (index % count) + block))

def subpageDirectory (pages : Array ByteArray) (block count : Nat) : Array ByteArray :=
  Array.ofFn (fun i : Fin (pages.size * count) => (globalSubpageAt pages block count i).getD ByteArray.empty)

theorem global_block_page_index (address block count : Nat) (layout : block * count = pageSize) :
    address / block / count = address / pageSize := by
  rw [Nat.div_div_eq_div_mul, layout]

theorem global_block_local_index (address block count : Nat) (layout : block * count = pageSize) :
    address / block % count = (address % pageSize) / block := by
  rw [← layout, Nat.mod_mul_right_div_self]

theorem global_block_byte_offset (address block count : Nat) (layout : block * count = pageSize) :
    (address % pageSize) % block = address % block := by
  exact Nat.mod_mod_of_dvd address ⟨count, layout.symm⟩

theorem global_subpage_lookup (pages : Array ByteArray) (address block count : Nat)
    (layout : block * count = pageSize) (page : ByteArray)
    (present : pages[address / pageSize]? = some page) :
    globalSubpageAt pages block count (address / block) =
      some (extractSubpage page block (address % pageSize)) := by
  simp only [globalSubpageAt, global_block_page_index _ _ _ layout, present, Option.map_some,
    global_block_local_index _ _ _ layout, extractSubpage]

theorem global_block_allocated (pages : Array ByteArray) (address block count : Nat)
    (layout : block * count = pageSize) (allocated : address / pageSize < pages.size) :
    address / block < pages.size * count := by
  have positive : 0 < count := by
    by_cases hz : count = 0
    · simp [hz, pageSize] at layout
    · omega
  apply (Nat.div_lt_iff_lt_mul positive).mp
  simpa only [global_block_page_index _ _ _ layout] using allocated

theorem subpage_directory_lookup (pages : Array ByteArray) (block count index : Nat)
    (allocated : index < pages.size * count) :
    (subpageDirectory pages block count)[index]? =
      some ((globalSubpageAt pages block count index).getD ByteArray.empty) := by
  simp [subpageDirectory, allocated]

theorem wasm_read_global_subpage (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) :
    (globalSubpageAt s.pages block count (address / block)).map (fun p => p[address % block]!) =
      some (readByte s address) := by
  rw [global_subpage_lookup _ _ _ _ layout page present]
  simp only [Option.map_some]
  rw [wasm_read_subpage s address page present full block count positive layout,
    global_block_byte_offset _ _ _ layout]

theorem wasm_read_subpage_directory (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) :
    ((subpageDirectory s.pages block count)[address / block]?).map (fun p => p[address % block]!) =
      some (readByte s address) := by
  have hi := (Array.getElem?_eq_some_iff.mp present).1
  rw [subpage_directory_lookup _ _ _ _ (global_block_allocated _ _ _ _ layout hi),
    global_subpage_lookup _ _ _ _ layout page present]
  simp only [Option.getD_some, Option.map_some]
  rw [wasm_read_subpage s address page present full block count positive layout,
    global_block_byte_offset _ _ _ layout]

theorem global_subpage_write_target (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) (value : UInt8) :
    globalSubpageAt (writeByte s address value).pages block count (address / block) =
      some ((extractSubpage page block (address % pageSize)).set! (address % block) value) := by
  simp only [globalSubpageAt, global_block_page_index _ _ _ layout,
    global_block_local_index _ _ _ layout]
  change ((writeByte s address value).pages[address / pageSize]?).map
    (fun p => extractSubpage p block (address % pageSize)) = _
  rw [wasm_write_subpage s address page present full block count positive layout value,
    global_block_byte_offset _ _ _ layout]

theorem subpage_directory_write_target (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count : Nat) (positive : 0 < block) (layout : block * count = pageSize) (value : UInt8) :
    (subpageDirectory (writeByte s address value).pages block count)[address / block]? =
      some ((extractSubpage page block (address % pageSize)).set! (address % block) value) := by
  have hi := global_block_allocated s.pages address block count layout
    (Array.getElem?_eq_some_iff.mp present).1
  have hi' : address / block < (writeByte s address value).pages.size * count := by
    simpa only [writeByte, Array.size_modify] using hi
  rw [subpage_directory_lookup _ _ _ _ hi',
    global_subpage_write_target s address page present full block count positive layout value]
  rfl

end NearCompression
