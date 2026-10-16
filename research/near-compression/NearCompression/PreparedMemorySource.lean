import NearCompression.PreparedMemoryLiteral
import NearCompression.PreparedMemoryBounds
import NearCompression.InstructionAddTrace
import ZkFormal.Near.Extract.Common
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem bit_prefix : preparedMemoryLiteralConstraints.take 460=
    (List.range 460).map preparedGasBoolean := by rfl
private theorem addresses : (preparedMemoryLiteralConstraints.drop 477).take 3=preparedMemoryAddressEquations := by rfl
private theorem bounds_at : ∀i:Fin 4,preparedMemoryLiteralConstraints[if i.val=0 then 460 else 481+i.val]?=
    some (preparedMemoryBoundsEquations[i]) := by decide
private instance localDecidable (e : Expr) : Decidable (instructionLocalExpr e) := by
  cases e with
  | const _=>exact isTrue True.intro
  | col _ n=>exact inferInstanceAs (Decidable (n=false))
  | add a b | mul a b=>exact @instDecidableAnd _ _ (localDecidable a) (localDecidable b)
  | neg a=>exact localDecidable a
  | pub _ | isFirst | isLast | isTransition=>exact isFalse id
private theorem local_at : ∀i:Fin 741,instructionLocalExpr (preparedMemoryLiteralConstraints[i]) := by decide

/-- Actual table-local satisfaction supplies every address/bounds source
residual. No separate caller-provided arithmetic relation is required. -/
theorem prepared_memory_literal_bounds (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t) :
    PreparedMemoryBoundsHolds (tr.cell t r) := by
  have eval (e : Expr) (member : e∈preparedMemoryLiteralConstraints) :
      e.evalWith (preparedGasEnv (tr.cell t r) [])=0 := by
    have actual:=localH.constr r hr e member
    obtain ⟨i,hi,eq⟩:=List.getElem_of_mem member
    have small : i<741 := by simpa only [preparedMemoryLiteralConstraints,List.length_cons,List.length_nil] using hi
    have loc : instructionLocalExpr e := by rw [←eq];exact local_at ⟨i,small⟩
    rw [instruction_local_eval e tr t r pub loc] at actual
    exact actual
  constructor
  · intro e he
    rcases List.mem_append.mp he with boolean|address
    · rw [←bit_prefix] at boolean
      exact eval e (List.mem_of_mem_take boolean)
    · rw [←addresses] at address
      exact eval e (List.mem_of_mem_drop (List.mem_of_mem_take address))
  · intro e he
    obtain ⟨i,hi,eq⟩:=List.getElem_of_mem he
    have small : i<4 := by simpa only [preparedMemoryBoundsEquations,List.length_cons,List.length_nil] using hi
    apply eval
    rw [←eq]
    exact List.mem_of_getElem? (bounds_at ⟨i,small⟩)
end NearCompression
