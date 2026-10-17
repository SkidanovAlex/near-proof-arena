import NearCompression.PreparedWasmExecution

namespace NearCompression
open NearSpecV3.Wasm

/-- Actual CallingWasm reset performed by callEntry. -/
def preparedWasmHostReset (host : St) : St :=
  {host with gas:={host.gas with g:=host.gas.remaining},stack:=#[],frames:=[]}

def preparedWasmEntryFrame (p : Prepared) (fi : Nat) (pf : PFunc) : Frame :=
  {fn:=fi-p.m.imports.size,pc:=0,locals:=pf.locals.map Val.default,
    labels:=[{target:=pf.code.size,arity:=pf.type.results.size,height:=0,isLoop:=false}],base:=0}

def preparedWasmEntryState (p : Prepared) (fi : Nat) (pf : PFunc) (host : St) : St :=
  {host with
    gas := {host.gas with g:=host.gas.remaining-pf.prologueGas}
    stack := #[]
    frames := [preparedWasmEntryFrame p fi pf]
    stackRem := host.stackRem-pf.stackCharge}

/-- Evaluate the genuine prepared prologue, including frame construction and
stack-budget deduction. No per-instruction replacement for range gas is used. -/
theorem prepared_wasm_enter (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (stackBudget : pf.stackCharge≤host.stackRem)
    (feeBound : pf.prologueGas<u64Bound) (enough : pf.prologueGas≤host.gas.remaining) :
    enter p (preparedWasmHostReset host) fi=.cont (preparedWasmEntryState p fi pf host) := by
  let base := {preparedWasmHostReset host with stackRem:=host.stackRem-pf.stackCharge}
  have charged:=instruction_add32_charge_success base (Fee.const pf.prologueGas) 0
    (by simpa only [Fee.const,Nat.zero_mul,Nat.zero_add] using feeBound)
    (by simpa only [Fee.const,Nat.zero_mul,Nat.zero_add,base,preparedWasmHostReset] using enough)
  change enter p (preparedWasmHostReset host) fi=_
  simp only [enter,preparedWasmHostReset,fetch,Nat.not_lt.mpr stackBudget,ite_false]
  change (match charge base (Fee.const pf.prologueGas) 0 with
    | .cont s => _ | r => r)=_
  rw [charged]
  simp only [base,preparedWasmHostReset,preparedWasmEntryState,preparedWasmEntryFrame,
    Fee.const,Nat.zero_mul,Nat.zero_add,Array.size_empty,Nat.zero_sub,
    Array.extract_empty,Array.empty_append]

theorem prepared_wasm_entry_gas (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (promises : host.gas.promises=0) (limit : host.gas.limit=host.gas.prepaid)
    (spent : host.gas.burnt≤host.gas.prepaid) (prepaid : host.gas.prepaid≤maxGasBurnt) :
    PreparedWasmGasContext (preparedWasmEntryState p fi pf host) := by
  unfold PreparedWasmGasContext preparedWasmEntryState
  dsimp only
  refine ⟨promises,limit,spent,?_,prepaid⟩
  simp only [Gas.remaining,Gas.used,promises,Nat.add_zero]
  exact Nat.sub_le _ _

/-- The earlier callEntry composition no longer needs an assumed enter result:
actual function lookup, stack budget, and prepared prologue bounds suffice. -/
theorem prepared_wasm_checked_call_entry (table : ZkFormal.Air.Table) (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp)
    (t : Nat) (pub : List ZkFormal.Algebra.Fp) (air : PreparedWasmAir table tr t pub)
    (cfg : NearCfg) (p : Prepared) (host : St) (fi : Nat) (pf : PFunc)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (stackBudget : pf.stackCharge≤host.stackRem)
    (feeBound : pf.prologueGas<u64Bound) (enough : pf.prologueGas≤host.gas.remaining)
    (promises : host.gas.promises=0) (limit : host.gas.limit=host.gas.prepaid)
    (spent : host.gas.burnt≤host.gas.prepaid) (prepaid : host.gas.prepaid≤maxGasBurnt)
    (r n : Nat) (final : St) (error : Option String)
    (execution : PreparedWasmExecution p tr t pub r (preparedWasmEntryState p fi pf host) n final error)
    (extra : Nat) : callEntry cfg p (n+extra) host fi=.ok (final,error) := by
  exact prepared_wasm_execution_call_entry table tr t pub air cfg p host _ fi r n final error
    (prepared_wasm_enter p fi pf host fetch stackBudget feeBound enough) execution
    (prepared_wasm_entry_gas p fi pf host promises limit spent prepaid) extra

end NearCompression
