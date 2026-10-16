import NearCompression.ContextValueWire

/-! Full CallCtx serialization; bounds remain explicit codec premises. -/
set_option maxHeartbeats 4000000

namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def nat128WireWf (n : Nat) : Prop := n < 340282366920938463463374607431768211456

theorem nat128_wire_roundtrip (n : Nat) (wf : nat128WireWf n) (rest : Bytes) :
    pU128 "counter" (u128 n ++ rest) = .ok (n, rest) := pU128_ok _ _ _ wf

def validatorWireWf := pairWireWf stringWireWf nat128WireWf
def encodeValidatorWire := encodePairWire encodeStringWire u128
def parseValidatorWire := parsePairWire parseStringWire (pU128 "counter")

theorem validator_wire_roundtrip (v : String × Nat) (wf : validatorWireWf v) (rest : Bytes) :
    parseValidatorWire (encodeValidatorWire v ++ rest) = .ok (v, rest) :=
  pair_wire_roundtrip _ _ _ _ _ _ string_wire_roundtrip nat128_wire_roundtrip v wf rest

def contextWireWf (c : CallCtx) : Prop :=
  stringWireWf c.currentAccount ∧
  stringWireWf c.signer ∧
  bytesWireWf c.signerPk ∧
  stringWireWf c.predecessor ∧
  stringWireWf c.refundTo ∧
  bytesWireWf c.input ∧
  (arrayWireWf promiseResultWireWf) c.promiseResults ∧
  nat128WireWf c.blockHeight ∧
  nat128WireWf c.blockTimestamp ∧
  nat128WireWf c.epochHeight ∧
  nat128WireWf c.accountBalance ∧
  nat128WireWf c.accountLocked ∧
  nat128WireWf c.storageUsage ∧
  nat128WireWf c.attachedDeposit ∧
  nat128WireWf c.prepaidGas ∧
  bytesWireWf c.randomSeed ∧
  (arrayWireWf stringWireWf) c.receivers ∧
  stringWireWf c.chainId ∧
  (arrayWireWf validatorWireWf) c.validators ∧
  optionalBytesWireWf c.accountContract ∧
  optionalBytesWireWf c.actionHash

def encodeContextWire (c : CallCtx) : Bytes :=
  encodeStringWire c.currentAccount ++
  encodeStringWire c.signer ++
  encodeBytesWire c.signerPk ++
  encodeStringWire c.predecessor ++
  encodeStringWire c.refundTo ++
  encodeBytesWire c.input ++
  (encodeArrayWire encodePromiseResultWire) c.promiseResults ++
  u128 c.blockHeight ++
  u128 c.blockTimestamp ++
  u128 c.epochHeight ++
  u128 c.accountBalance ++
  u128 c.accountLocked ++
  u128 c.storageUsage ++
  u128 c.attachedDeposit ++
  u128 c.prepaidGas ++
  encodeBytesWire c.randomSeed ++
  (encodeArrayWire encodeStringWire) c.receivers ++
  encodeStringWire c.chainId ++
  (encodeArrayWire encodeValidatorWire) c.validators ++
  encodeOptionalBytesWire c.accountContract ++
  encodeOptionalBytesWire c.actionHash

def parseContextWire : NearSpecV3.P CallCtx := fun bs => do
  let (currentAccount, bs) ← parseStringWire bs
  let (signer, bs) ← parseStringWire bs
  let (signerPk, bs) ← parseBytesWire bs
  let (predecessor, bs) ← parseStringWire bs
  let (refundTo, bs) ← parseStringWire bs
  let (input, bs) ← parseBytesWire bs
  let (promiseResults, bs) ← (parseArrayWire parsePromiseResultWire) bs
  let (blockHeight, bs) ← (pU128 "counter") bs
  let (blockTimestamp, bs) ← (pU128 "counter") bs
  let (epochHeight, bs) ← (pU128 "counter") bs
  let (accountBalance, bs) ← (pU128 "counter") bs
  let (accountLocked, bs) ← (pU128 "counter") bs
  let (storageUsage, bs) ← (pU128 "counter") bs
  let (attachedDeposit, bs) ← (pU128 "counter") bs
  let (prepaidGas, bs) ← (pU128 "counter") bs
  let (randomSeed, bs) ← parseBytesWire bs
  let (receivers, bs) ← (parseArrayWire parseStringWire) bs
  let (chainId, bs) ← parseStringWire bs
  let (validators, bs) ← (parseArrayWire parseValidatorWire) bs
  let (accountContract, bs) ← parseOptionalBytesWire bs
  let (actionHash, bs) ← parseOptionalBytesWire bs
  pure ({ currentAccount, signer, signerPk, predecessor, refundTo, input, promiseResults, blockHeight, blockTimestamp, epochHeight, accountBalance, accountLocked, storageUsage, attachedDeposit, prepaidGas, randomSeed, receivers, chainId, validators, accountContract, actionHash }, bs)

theorem context_wire_roundtrip (c : CallCtx) (wf : contextWireWf c) (rest : Bytes) :
    parseContextWire (encodeContextWire c ++ rest) = .ok (c, rest) := by
  obtain ⟨hcurrentAccount, hsigner, hsignerPk, hpredecessor, hrefundTo, hinput, hpromiseResults, hblockHeight, hblockTimestamp, hepochHeight, haccountBalance, haccountLocked, hstorageUsage, hattachedDeposit, hprepaidGas, hrandomSeed, hreceivers, hchainId, hvalidators, haccountContract, hactionHash⟩ := wf
  simp only [parseContextWire, encodeContextWire, List.append_assoc,
    string_wire_roundtrip c.currentAccount hcurrentAccount,
    string_wire_roundtrip c.signer hsigner,
    bytes_wire_roundtrip c.signerPk hsignerPk,
    string_wire_roundtrip c.predecessor hpredecessor,
    string_wire_roundtrip c.refundTo hrefundTo,
    bytes_wire_roundtrip c.input hinput,
    (array_wire_roundtrip _ _ _ promise_result_wire_roundtrip) c.promiseResults hpromiseResults,
    nat128_wire_roundtrip c.blockHeight hblockHeight,
    nat128_wire_roundtrip c.blockTimestamp hblockTimestamp,
    nat128_wire_roundtrip c.epochHeight hepochHeight,
    nat128_wire_roundtrip c.accountBalance haccountBalance,
    nat128_wire_roundtrip c.accountLocked haccountLocked,
    nat128_wire_roundtrip c.storageUsage hstorageUsage,
    nat128_wire_roundtrip c.attachedDeposit hattachedDeposit,
    nat128_wire_roundtrip c.prepaidGas hprepaidGas,
    bytes_wire_roundtrip c.randomSeed hrandomSeed,
    (array_wire_roundtrip _ _ _ string_wire_roundtrip) c.receivers hreceivers,
    string_wire_roundtrip c.chainId hchainId,
    (array_wire_roundtrip _ _ _ validator_wire_roundtrip) c.validators hvalidators,
    optional_bytes_wire_roundtrip c.accountContract haccountContract,
    optional_bytes_wire_roundtrip c.actionHash hactionHash, bind, Except.bind]
  rfl

theorem context_wire_injective (a b : CallCtx) (ha : contextWireWf a) (hb : contextWireWf b)
    (same : encodeContextWire a = encodeContextWire b) : a = b := by
  have h := congrArg (fun bs => parseContextWire (bs ++ [])) same
  with_reducible rw [context_wire_roundtrip a ha [], context_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
