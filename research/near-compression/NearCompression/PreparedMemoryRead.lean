import NearCompression.PreparedMemoryScalar
import NearCompression.AuthenticatedBlockRead
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

structure PreparedMemoryReadOpening where
  block : ByteArray
  path : List (Bool × ByteArray)
  deriving Inhabited

def preparedMemoryReadOpeningCheck (hash : Bytes→ByteArray) (d : BlockDescriptor)
    (address : Nat) (opening : PreparedMemoryReadOpening) : Bool :=
  decide (opening.block.size<4294967296) &&
    opening.path.all (fun x=>decide (x.2.size<4294967296)) &&
    checkBlockOpening hash d address opening.block opening.path

/-- Per-byte subpage openings permit scalar accesses to cross both subpage
and Wasm-page boundaries. Deduplicated openings/event buses are a later
optimization; this baseline supplies at most8 subpage witnesses per access. -/
def preparedMemoryReadCheck (hash : Bytes→ByteArray) (d : BlockDescriptor)
    (address width : Nat) (openings : List PreparedMemoryReadOpening) : Bool :=
  decide ((width=1 ∨ width=2 ∨ width=4 ∨ width=8) ∧ openings.length=width ∧
    address+width≤d.pages*pageSize) &&
  (List.range' 0 width).all (fun i=>preparedMemoryReadOpeningCheck hash d (address+i) (openings.getD i default))

def preparedMemoryReadValue (d : BlockDescriptor) (address width : Nat)
    (openings : List PreparedMemoryReadOpening) : Nat :=
  preparedScalarReadValue (fun i=>(openings.getD i default).block[(address+i)%d.block]!) width

/-- Collision support is the actual committed tree and one queried opening,
including the exact byte index. This finite event is suitable for composition
with the enclosing hash-query accounting; no global existential collision. -/
def PreparedMemoryReadCollision (hash : Bytes→ByteArray) (s : St)
    (block count depth width : Nat) (openings : List PreparedMemoryReadOpening) : Prop :=
  ∃i,i∈List.range' 0 width ∧ PageCollisionIn hash
    (encodeBlockDescriptor (describeSubpageMemory hash s block count depth) ::
      (pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
    (encodeBlockDescriptor (describeSubpageMemory hash s block count depth) ::
      (pageOpeningMessages (blockTreeHash hash block) (openings.getD i default).block (openings.getD i default).path).map (blockHashMessage block))

private theorem read_fold_congr (xs : List Nat) (f g : Nat→UInt8)
    (same : ∀i∈xs,f i=g i) (acc : Nat) :
    xs.foldl (fun value i=>value+(f i).toNat*256^i) acc=
      xs.foldl (fun value i=>value+(g i).toNat*256^i) acc := by
  induction xs generalizing acc with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.foldl_cons]
    rw [same x (by simp)]
    exact ih (fun i hi=>same i (by simp [hi])) _

theorem prepared_memory_read_checked (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address width : Nat)
    (referenceWf : blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (openings : List PreparedMemoryReadOpening)
    (accepted : preparedMemoryReadCheck hash (describeSubpageMemory hash s block count depth) address width openings=true) :
    (width=1 ∨ width=2 ∨ width=4 ∨ width=8) ∧ openings.length=width ∧ address+width≤memBytes s ∧
    (NearSpecV3.Wasm.readLE s address width=
      preparedMemoryReadValue (describeSubpageMemory hash s block count depth) address width openings ∨
      PreparedMemoryReadCollision hash s block count depth width openings) := by
  simp only [preparedMemoryReadCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at accepted
  refine ⟨accepted.1.1,accepted.1.2.1,accepted.1.2.2,?_⟩
  classical
  by_cases collision:PreparedMemoryReadCollision hash s block count depth width openings
  · exact Or.inr collision
  · apply Or.inl
    have byteEq (i : Nat) (hi : i∈List.range' 0 width) :
        readByte s (address+i)=(openings.getD i default).block[(address+i)%block]! := by
      have check:=accepted.2 i hi
      simp only [preparedMemoryReadOpeningCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at check
      have wf:bytesWireWf (openings.getD i default).block:=by
        simpa only [bytesWireWf,Array.length_toList,ByteArray.size_data] using check.1.1
      have pwf:pageOpeningWf (openings.getD i default).path:=by
        intro x hx
        simpa only [bytesWireWf,Array.length_toList,ByteArray.size_data] using check.1.2 x hx
      have result:=authenticated_block_read_or_collision hash digestBound s full block count depth (address+i)
        referenceWf _ referenceWf rfl _ wf _ pwf check.2
      rcases result with correct|bad
      · exact correct
      · exact False.elim (collision ⟨i,hi,bad⟩)
    rw [prepared_scalar_read_exact]
    unfold preparedMemoryReadValue preparedScalarReadValue
    exact read_fold_congr _ _ _ (fun i hi=>byteEq i hi) 0
end NearCompression
