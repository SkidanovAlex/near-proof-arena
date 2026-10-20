import NearCompression.SubpageCommitmentWrite

/-! Bind block layout, Wasm allocation count, depth and root in one encoding.
This metadata commitment still needs linkage to the full state statement. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

structure BlockDescriptor where
  block : Nat
  perPage : Nat
  pages : Nat
  depth : Nat
  root : ByteArray
  deriving DecidableEq

def blockDescriptorDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 98, 108, 111, 99, 107, 109, 101, 109, 45, 118, 49]
def blockDescriptorWf (d : BlockDescriptor) : Prop :=
  nat128WireWf d.block ∧ nat128WireWf d.perPage ∧ nat128WireWf d.pages ∧ nat128WireWf d.depth ∧ bytesWireWf d.root

def blockDescriptorPayload (d : BlockDescriptor) : Bytes :=
  u128 d.block ++ u128 d.perPage ++ u128 d.pages ++ u128 d.depth ++ encodeBytesWire d.root

def encodeBlockDescriptor (d : BlockDescriptor) : Bytes := blockDescriptorDomain ++ blockDescriptorPayload d

def parseBlockDescriptorPayload : NearSpecV3.P BlockDescriptor := fun bs => do
  let (block, bs) ← pU128 "counter" bs
  let (perPage, bs) ← pU128 "counter" bs
  let (pages, bs) ← pU128 "counter" bs
  let (depth, bs) ← pU128 "counter" bs
  let (root, bs) ← parseBytesWire bs
  pure ({ block, perPage, pages, depth, root }, bs)

theorem block_descriptor_payload_roundtrip (d : BlockDescriptor) (wf : blockDescriptorWf d) (rest : Bytes) :
    parseBlockDescriptorPayload (blockDescriptorPayload d ++ rest) = .ok (d, rest) := by
  obtain ⟨hb, hc, hp, hd, hr⟩ := wf
  simp only [parseBlockDescriptorPayload, blockDescriptorPayload, List.append_assoc,
    nat128_wire_roundtrip d.block hb, nat128_wire_roundtrip d.perPage hc,
    nat128_wire_roundtrip d.pages hp, nat128_wire_roundtrip d.depth hd,
    bytes_wire_roundtrip d.root hr, bind, Except.bind]
  rfl

theorem block_descriptor_encoding_injective (a b : BlockDescriptor)
    (ha : blockDescriptorWf a) (hb : blockDescriptorWf b)
    (same : encodeBlockDescriptor a = encodeBlockDescriptor b) : a = b := by
  have h : blockDescriptorPayload a = blockDescriptorPayload b := List.append_cancel_left same
  have he := congrArg (fun bs => parseBlockDescriptorPayload (bs ++ [])) h
  rw [block_descriptor_payload_roundtrip a ha [], block_descriptor_payload_roundtrip b hb []] at he
  exact congrArg Prod.fst (Except.ok.inj he)

def describeSubpageMemory (hash : Bytes → ByteArray) (s : St) (block count depth : Nat) : BlockDescriptor :=
  ⟨block, count, s.pages.size, depth, pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth)⟩

theorem block_descriptor_binding_or_collision (hash : Bytes → ByteArray)
    (a b : BlockDescriptor) (ha : blockDescriptorWf a) (hb : blockDescriptorWf b)
    (same : hash (encodeBlockDescriptor a) = hash (encodeBlockDescriptor b)) :
    a = b ∨ (encodeBlockDescriptor a ≠ encodeBlockDescriptor b ∧
      hash (encodeBlockDescriptor a) = hash (encodeBlockDescriptor b)) := by
  classical
  by_cases he : encodeBlockDescriptor a = encodeBlockDescriptor b
  · exact Or.inl (block_descriptor_encoding_injective a b ha hb he)
  · exact Or.inr ⟨he, same⟩

/-- Operational validity is distinct from encoding bounds. -/
def acceptsBlockOpening (hash : Bytes → ByteArray) (d : BlockDescriptor) (address : Nat)
    (data : ByteArray) (path : List (Bool × ByteArray)) : Prop :=
  0 < d.block ∧ d.block * d.perPage = pageSize ∧ d.pages * d.perPage ≤ 2 ^ d.depth ∧
    address / pageSize < d.pages ∧ data.size = d.block ∧
    path.map Prod.fst = pageIndexPath d.depth (address / d.block) ∧
    d.root = pageOpeningRoot (blockTreeHash hash d.block) data path

def checkBlockOpening (hash : Bytes → ByteArray) (d : BlockDescriptor) (address : Nat)
    (data : ByteArray) (path : List (Bool × ByteArray)) : Bool :=
  decide (0 < d.block) && decide (d.block * d.perPage = pageSize) &&
    decide (d.pages * d.perPage ≤ 2 ^ d.depth) && decide (address / pageSize < d.pages) &&
    decide (data.size = d.block) && decide (path.map Prod.fst = pageIndexPath d.depth (address / d.block)) &&
    decide (d.root = pageOpeningRoot (blockTreeHash hash d.block) data path)

theorem check_block_opening_correct (hash : Bytes → ByteArray) (d : BlockDescriptor) (address : Nat)
    (data : ByteArray) (path : List (Bool × ByteArray)) :
    checkBlockOpening hash d address data path = true ↔ acceptsBlockOpening hash d address data path := by
  simp [checkBlockOpening, acceptsBlockOpening, and_assoc]

end NearCompression
