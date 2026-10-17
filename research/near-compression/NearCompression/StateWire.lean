import NearCompression.ActionWire

/-! Complete finite state-boundary codec, normalizing only logical map layouts.
Field bounds and the fixed immutable store remain explicit obligations. -/
set_option maxHeartbeats 8000000

namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def normalizeStateBoundaryWire (s : StateBoundary) : StateBoundary :=
  { s with real := s.real.map normalizeRealBoundary }

def stateBoundaryWireWf (s : StateBoundary) : Prop :=
  stackWireWf s.stack ∧
  framesWireWf s.frames ∧
  byteArraysWireWf s.pages ∧
  stackWireWf s.globals ∧
  tableWireWf s.table ∧
  nat128WireWf s.tableMax ∧
  elementsWireWf s.elems ∧
  byteArraysWireWf s.datas ∧
  nat128WireWf s.stackRem ∧
  gasWireWf s.gas ∧
  contextWireWf s.ctx ∧
  returnWireWf s.ret ∧
  nat128WireWf s.balance ∧
  nat128WireWf s.storageUsage ∧
  registersWireWf s.registers ∧
  nat128WireWf s.regUsage ∧
  byteArraysWireWf s.logs ∧
  nat128WireWf s.totalLogLen ∧
  (arrayWireWf promiseWireWf) s.promises ∧
  trieWireWf s.trie ∧
  actionsWireWf s.actions ∧
  nat128WireWf s.dataCount ∧
  optionalRealBoundaryWireWf s.real ∧
  nat128WireWf s.subsidized

def encodeStateBoundaryWire (s : StateBoundary) : Bytes :=
  encodeStackWire s.stack ++
  encodeFramesWire s.frames ++
  encodeByteArraysWire s.pages ++
  encodeStackWire s.globals ++
  encodeTableWire s.table ++
  u128 s.tableMax ++
  encodeElementsWire s.elems ++
  encodeByteArraysWire s.datas ++
  u128 s.stackRem ++
  encodeGasWire s.gas ++
  encodeContextWire s.ctx ++
  encodeReturnWire s.ret ++
  u128 s.balance ++
  u128 s.storageUsage ++
  encodeRegistersWire s.registers ++
  u128 s.regUsage ++
  encodeByteArraysWire s.logs ++
  u128 s.totalLogLen ++
  (encodeArrayWire encodePromiseWire) s.promises ++
  encodeTrieWire s.trie ++
  encodeActionsWire s.actions ++
  u128 s.dataCount ++
  encodeOptionalRealBoundaryWire s.real ++
  u128 s.subsidized

def parseStateBoundaryWire : NearSpecV3.P StateBoundary := fun bs => do
  let (stack, bs) ← parseStackWire bs
  let (frames, bs) ← parseFramesWire bs
  let (pages, bs) ← parseByteArraysWire bs
  let (globals, bs) ← parseStackWire bs
  let (table, bs) ← parseTableWire bs
  let (tableMax, bs) ← (pU128 "counter") bs
  let (elems, bs) ← parseElementsWire bs
  let (datas, bs) ← parseByteArraysWire bs
  let (stackRem, bs) ← (pU128 "counter") bs
  let (gas, bs) ← parseGasWire bs
  let (ctx, bs) ← parseContextWire bs
  let (ret, bs) ← parseReturnWire bs
  let (balance, bs) ← (pU128 "counter") bs
  let (storageUsage, bs) ← (pU128 "counter") bs
  let (registers, bs) ← parseRegistersWire bs
  let (regUsage, bs) ← (pU128 "counter") bs
  let (logs, bs) ← parseByteArraysWire bs
  let (totalLogLen, bs) ← (pU128 "counter") bs
  let (promises, bs) ← (parseArrayWire parsePromiseWire) bs
  let (trie, bs) ← parseTrieWire bs
  let (actions, bs) ← parseActionsWire bs
  let (dataCount, bs) ← (pU128 "counter") bs
  let (real, bs) ← parseOptionalRealBoundaryWire bs
  let (subsidized, bs) ← (pU128 "counter") bs
  pure ({ stack, frames, pages, globals, table, tableMax, elems, datas, stackRem, gas, ctx, ret, balance, storageUsage, registers, regUsage, logs, totalLogLen, promises, trie, actions, dataCount, real, subsidized }, bs)

theorem state_boundary_wire_roundtrip (s : StateBoundary) (wf : stateBoundaryWireWf s) (rest : Bytes) :
    parseStateBoundaryWire (encodeStateBoundaryWire s ++ rest) = .ok (normalizeStateBoundaryWire s, rest) := by
  obtain ⟨hstack, hframes, hpages, hglobals, htable, htableMax, helems, hdatas, hstackRem, hgas, hctx, hret, hbalance, hstorageUsage, hregisters, hregUsage, hlogs, htotalLogLen, hpromises, htrie, hactions, hdataCount, hreal, hsubsidized⟩ := wf
  simp only [parseStateBoundaryWire, encodeStateBoundaryWire, List.append_assoc,
    stack_wire_roundtrip s.stack hstack,
    frames_wire_roundtrip s.frames hframes,
    byte_arrays_wire_roundtrip s.pages hpages,
    stack_wire_roundtrip s.globals hglobals,
    table_wire_roundtrip s.table htable,
    nat128_wire_roundtrip s.tableMax htableMax,
    elements_wire_roundtrip s.elems helems,
    byte_arrays_wire_roundtrip s.datas hdatas,
    nat128_wire_roundtrip s.stackRem hstackRem,
    gas_wire_roundtrip s.gas hgas,
    context_wire_roundtrip s.ctx hctx,
    return_wire_roundtrip s.ret hret,
    nat128_wire_roundtrip s.balance hbalance,
    nat128_wire_roundtrip s.storageUsage hstorageUsage,
    registers_wire_roundtrip s.registers hregisters,
    nat128_wire_roundtrip s.regUsage hregUsage,
    byte_arrays_wire_roundtrip s.logs hlogs,
    nat128_wire_roundtrip s.totalLogLen htotalLogLen,
    (array_wire_roundtrip _ _ _ promise_wire_roundtrip) s.promises hpromises,
    trie_wire_roundtrip s.trie htrie,
    actions_wire_roundtrip s.actions hactions,
    nat128_wire_roundtrip s.dataCount hdataCount,
    optional_real_boundary_wire_roundtrip s.real hreal,
    nat128_wire_roundtrip s.subsidized hsubsidized, bind, Except.bind]
  rfl

theorem restore_normalized_state_boundary (store : TTN.Store) (s : StateBoundary) :
    restoreState store (normalizeStateBoundaryWire s) = normalizeStateMaps (restoreState store s) := by
  cases he : s.real <;>
    simp [normalizeStateBoundaryWire, restoreState, normalizeStateMaps, he,
      restore_normalized_real_boundary]

theorem state_boundary_wire_observed_roundtrip (store : TTN.Store)
    (s : StateBoundary) (wf : stateBoundaryWireWf s) (rest : Bytes) :
    ∃ decoded, parseStateBoundaryWire (encodeStateBoundaryWire s ++ rest) = .ok (decoded, rest) ∧
      StateEquivalent (restoreState store decoded) (restoreState store s) := by
  refine ⟨normalizeStateBoundaryWire s, state_boundary_wire_roundtrip s wf rest, ?_⟩
  rw [restore_normalized_state_boundary]
  exact normalized_state_equiv _

end NearCompression
