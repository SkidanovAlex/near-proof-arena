import NearCompression.SubpageDirectoryUpdate

/-! Full Wasm page-size invariants for memory construction and byte writers.
This is not yet a whole-interpreter reachability theorem. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def fullPages (pages : Array ByteArray) : Prop := ∀ p ∈ pages.toList, p.size = pageSize

theorem zero_page_full : zeroPage.size = pageSize := by
  change (Array.replicate pageSize (0 : UInt8)).size = pageSize
  simp

theorem allocated_pages_full (count : Nat) : fullPages (Array.replicate count zeroPage) := by
  intro p hp
  have he : p = zeroPage := by simpa using (List.mem_replicate.mp (by simpa using hp)).2
  rw [he, zero_page_full]

theorem grown_pages_full (pages : Array ByteArray) (full : fullPages pages) (count : Nat) :
    fullPages (pages ++ Array.replicate count zeroPage) := by
  intro p hp
  simp only [Array.toList_append, List.mem_append] at hp
  rcases hp with old | new
  · exact full p old
  · exact allocated_pages_full count p new

theorem write_byte_full_pages (s : St) (full : fullPages s.pages) (address : Nat) (value : UInt8) :
    fullPages (writeByte s address value).pages := by
  intro p hp
  have hm : p ∈ s.pages.modify (address / pageSize) (fun p => p.set! (address % pageSize) value) :=
    Array.mem_toList_iff.mp hp
  obtain ⟨i, hi, he⟩ := Array.getElem_of_mem hm
  rw [Array.getElem_modify] at he
  have originalFull : (s.pages[i]'(by simpa using hi)).size = pageSize := full _ (by simp)
  split at he
  · rw [← he, ByteArray.size_set!]; exact originalFull
  · rw [← he]; exact originalFull

theorem execute_requests_full_pages (s : St) (full : fullPages s.pages) (requests : List (Nat × UInt8)) :
    fullPages (executeByteRequests s requests).pages := by
  induction requests generalizing s with
  | nil => exact full
  | cons r rs ih => exact ih _ (write_byte_full_pages s full r.1 r.2)

theorem write_bytes_full_pages (s : St) (full : fullPages s.pages) (address : Nat) (data : ByteArray) :
    fullPages (writeBytes s address data).pages := by
  rw [write_bytes_requests_exact]
  exact execute_requests_full_pages s full _

theorem full_pages_wire_wf (s : St) (full : fullPages s.pages) : memoryPagesWf s := by
  intro p hp
  have he := full p hp
  simp only [bytesWireWf, Array.length_toList, ByteArray.size_data]
  rw [he]
  decide +kernel

/-- The actual store loop also preserves page shape, independently of the value
being stored. Instruction gas/bounds checking is not changed or proved here. -/
theorem for_in_full_pages : ∀ (xs : List Nat) (f : Nat → St → St) (s : St),
    fullPages s.pages → (∀ i u, fullPages u.pages → fullPages (f i u).pages) →
    fullPages (forIn (m := Id) xs s (fun i u => ForInStep.yield (f i u))).pages
  | [], _, _, h, _ => h
  | i :: xs, f, s, h, hf => by
    simp only [List.forIn_cons]
    exact for_in_full_pages xs f (f i s) (hf i s h) hf

theorem write_le_full_pages (s : St) (full : fullPages s.pages) (address width value : Nat) :
    fullPages (writeLE s address width value).pages := by
  unfold writeLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  apply for_in_full_pages _ _ s full
  intro i u hu
  exact write_byte_full_pages u hu _ _

def resultFullPages : Res → Prop
  | .cont s | .fin s | .abort s _ => fullPages s.pages
  | .unmodeled _ => True

theorem mem_copy_full_pages (s : St) (full : fullPages s.pages) (dest source length : Nat) :
    resultFullPages (memCopy s dest source length) := by
  unfold memCopy
  split
  · exact full
  · exact write_bytes_full_pages s full _ _

theorem mem_init_full_pages (s : St) (full : fullPages s.pages) (segment dest source length : Nat) :
    resultFullPages (memInit s segment dest source length) := by
  unfold memInit
  dsimp only
  split
  · exact full
  · exact write_bytes_full_pages s full _ _

theorem mem_fill_full_pages (s : St) (full : fullPages s.pages) (dest value length : Nat) :
    resultFullPages (memFill s dest value length) := by
  unfold memFill
  split
  · exact full
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    apply for_in_full_pages _ _ s full
    intro i u hu
    exact write_byte_full_pages u hu _ _

end NearCompression
