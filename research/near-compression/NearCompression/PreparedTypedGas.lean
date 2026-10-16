import NearCompression.PreparedTypedSource
import NearCompression.PreparedControlGas
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem boolean_prefix : ∀count:Fin 5,
    (preparedTypedLiteralExec count).take 682=(List.range 682).map preparedGasBoolean := by
  intro ⟨n,hn⟩
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem subtract_at : ∀count:Fin 5,∀i:Fin 4,
    (preparedTypedLiteralExec count)[1619+66*(4-count.val)+i.val]?=some (preparedExecGasSubtract i) := by decide
private theorem update_at : ∀count:Fin 5,∀i:Fin 4,
    (preparedTypedLiteralExec count)[1727+66*(4-count.val)+i.val]?=some (preparedExecGasUpdate i) := by decide
/-- Exact typed literal sources instantiate the already checked natural gas
borrow and update semantics. No independent fee-range premise is required. -/
theorem prepared_typed_gas_source (count : Nat) (hc : count≤4) :
    PreparedControlGasSource (preparedTypedLiteralExecTable count) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    apply List.mem_of_mem_take (i:=682)
    change preparedGasBoolean i∈(preparedTypedLiteralExec count).take 682
    rw [boolean_prefix ⟨count,by omega⟩]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  · intro i hi
    exact List.mem_of_getElem? (subtract_at ⟨count,by omega⟩ ⟨i,hi⟩)
  · intro i hi
    exact List.mem_of_getElem? (update_at ⟨count,by omega⟩ ⟨i,hi⟩)
end NearCompression
