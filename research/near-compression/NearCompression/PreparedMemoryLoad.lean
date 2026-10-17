import NearCompression.PreparedMemoryRead
import NearCompression.PreparedMemoryExec
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- Accepted hash-based byte openings determine the actual typed load
successor, including signed extension. The input descriptor here is the
honest state descriptor; authentication by the enclosing statement remains
an explicit integration obligation. -/
theorem prepared_memory_load_checked (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth : Nat)
    (referenceWf : blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (cfg : NearCfg) (p : Prepared) (f : Frame) (pf : PFunc)
    (op align offset : Nat) (address : UInt32) (openings : List PreparedMemoryReadOpening)
    (accepted : preparedMemoryReadCheck hash (describeSubpageMemory hash s block count depth)
      (address.toNat+offset) (loadSpec op).1 openings=true) :
    exec cfg p (pushV s (.i32 address)) f pf (.load op align offset)=
      .cont (setFrame (pushV s (preparedMemoryLoadedValue op
        (preparedMemoryReadValue (describeSubpageMemory hash s block count depth)
          (address.toNat+offset) (loadSpec op).1 openings))) {f with pc:=f.pc+1}) ∨
      PreparedMemoryReadCollision hash s block count depth (loadSpec op).1 openings := by
  obtain ⟨_,_,bounds,result⟩:=prepared_memory_read_checked hash digestBound s full block count depth
    (address.toNat+offset) (loadSpec op).1 referenceWf openings accepted
  rcases result with correct|collision
  · apply Or.inl
    rw [prepared_memory_load_exec,ite_eq_right (by omega),←prepared_scalar_read_exact,correct]
  · exact Or.inr collision
end NearCompression
