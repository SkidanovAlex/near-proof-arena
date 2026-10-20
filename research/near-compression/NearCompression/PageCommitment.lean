import NearCompression.BackedWire

/-! Page commitments tied to actual Wasm memory. The directory is the honest
reference here; authenticating its entries/root is a separate obligation. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def pageCommitmentDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 112, 97, 103, 101, 45, 118, 49]
def encodeMemoryPage (p : ByteArray) : Bytes := pageCommitmentDomain ++ encodeBytesWire p

theorem memory_page_encoding_injective (p q : ByteArray) (hp : bytesWireWf p)
    (hq : bytesWireWf q) (same : encodeMemoryPage p = encodeMemoryPage q) : p = q := by
  have h : encodeBytesWire p = encodeBytesWire q := List.append_cancel_left same
  have he := congrArg (fun bs => parseBytesWire (bs ++ [])) h
  rw [bytes_wire_roundtrip p hp [], bytes_wire_roundtrip q hq []] at he
  exact congrArg Prod.fst (Except.ok.inj he)

def pageDigestDirectory {Digest : Type} (hash : Bytes → Digest) (s : St) : Array Digest :=
  s.pages.map (fun p => hash (encodeMemoryPage p))

def acceptsPageOpening {Digest : Type} (hash : Bytes → Digest) (directory : Array Digest)
    (index : Nat) (page : ByteArray) : Prop :=
  directory[index]? = some (hash (encodeMemoryPage page))

theorem page_opening_or_collision {Digest : Type} (hash : Bytes → Digest)
    (s : St) (index : Nat) (page : ByteArray)
    (wf : ∀ p ∈ s.pages.toList, bytesWireWf p) (hp : bytesWireWf page)
    (accepted : acceptsPageOpening hash (pageDigestDirectory hash s) index page) :
    s.pages[index]? = some page ∨
      ∃ original, s.pages[index]? = some original ∧
        encodeMemoryPage original ≠ encodeMemoryPage page ∧
        hash (encodeMemoryPage original) = hash (encodeMemoryPage page) := by
  classical
  unfold acceptsPageOpening pageDigestDirectory at accepted
  rw [Array.getElem?_map] at accepted
  cases he : s.pages[index]? with
  | none => simp [he] at accepted
  | some original =>
    have hhash : hash (encodeMemoryPage original) = hash (encodeMemoryPage page) := by
      simpa only [he, Option.map_some, Option.some.injEq] using accepted
    by_cases same : original = page
    · exact Or.inl (congrArg some same)
    · apply Or.inr
      refine ⟨original, rfl, ?_, hhash⟩
      intro enc
      apply same
      exact memory_page_encoding_injective original page (wf original (by
        simpa using (Array.mem_of_getElem? he))) hp enc

theorem page_opening_read_or_collision {Digest : Type} (hash : Bytes → Digest)
    (s : St) (address : Nat) (page : ByteArray)
    (wf : ∀ p ∈ s.pages.toList, bytesWireWf p) (hp : bytesWireWf page)
    (accepted : acceptsPageOpening hash (pageDigestDirectory hash s) (address / pageSize) page) :
    readByte s address = page.get! (address % pageSize) ∨
      ∃ original, s.pages[address / pageSize]? = some original ∧
        encodeMemoryPage original ≠ encodeMemoryPage page ∧
        hash (encodeMemoryPage original) = hash (encodeMemoryPage page) := by
  rcases page_opening_or_collision hash s _ page wf hp accepted with he | hc
  · exact Or.inl (by simp only [readByte, he])
  · exact Or.inr hc

/-- The actual writeByte operation changes only its addressed page digest. -/
theorem page_directory_write_other {Digest : Type} (hash : Bytes → Digest)
    (s : St) (address index : Nat) (value : UInt8) (other : address / pageSize ≠ index) :
    (pageDigestDirectory hash (writeByte s address value))[index]? =
      (pageDigestDirectory hash s)[index]? := by
  simp only [pageDigestDirectory, writeByte, Array.getElem?_map, Array.getElem?_modify, if_neg other]

theorem page_directory_write_target {Digest : Type} (hash : Bytes → Digest)
    (s : St) (address : Nat) (value : UInt8) :
    (pageDigestDirectory hash (writeByte s address value))[address / pageSize]? =
      (s.pages[address / pageSize]?).map
        (fun p => hash (encodeMemoryPage (p.set! (address % pageSize) value))) := by
  simp only [pageDigestDirectory, writeByte, Array.getElem?_map, Array.getElem?_modify,
    if_true, Option.map_map, Function.comp_def]

end NearCompression
