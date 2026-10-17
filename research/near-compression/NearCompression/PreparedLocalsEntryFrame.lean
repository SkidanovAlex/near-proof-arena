import NearCompression.PreparedLocalsInitialization
import NearCompression.PreparedLocalsCode
import NearCompression.PreparedWasmEntry
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

/-- The real prepared entry frame initializes precisely the local array
constrained by row zero; local types and count come from the code checker. -/
theorem prepared_locals_entry_frame (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (checked : preparedLocalsCodeCheck count pf fn pub=true)
    (tr : Trace Fp) (t : Nat)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (p : Prepared) (fi : Nat) :
    (preparedWasmEntryFrame p fi pf).locals=preparedLocalsArray (tr.cell t 0) count := by
  obtain ⟨_,bound,size,_,_,types,_⟩:=prepared_locals_code_shape count pf fn pub checked
  rw [prepared_locals_initial_array count bound tr t pub localH (Nat.two_pow_pos _)]
  change pf.locals.map Val.default=(List.replicate count (Val.i32 0)).toArray
  apply Array.ext
  · simp [size]
  · intro i hi hj
    have hidx : i<pf.locals.size := by simpa using hi
    have ty : pf.locals[i]=VT.i32 := types _ (by simpa using Array.getElem_mem hidx)
    simp [ty,Val.default]
end NearCompression
