import ZkFormal.NearV3.D3.ContractData
import ZkFormal.V2.Air
import NearSpecV3.D3.FunctionCall

/-!
# `ZkFormal.PQ.Join.Statement` — the joint statement of a Wasm FunctionCall proof and a state proof

Lane `pq-d3-join`.  **This file states the joint relation; it proves nothing about a full AIR.**
Every `Prop` here is a *definition of the obligation*, labelled unproved, and is meant to be
discharged by the two side theorems plus the cross-proof bus balance.

## The two proofs

* **Wasm FunctionCall proof** (`lane/pq-wasm-base`, §14.2 of its README): the base AIR
  `wasmBaseAir` over the contract code, with the HOST chip, the register space and the
  `g_after` budget register.  Its public values are the base statement (`N, S_final, nres, rtag,
  result, status, mem, dataEnd, local tags, globals, stackRem`) plus the cached-commitment
  statement components (`code_root`, and `code_hash` from the state side), plus the HOST
  traffic's cached commitments.
* **State proof** (this lane's D0a/D1 port, plus the D3 `ContractData` work): `nearAirV3D1`
  (or `nearAirV3` for D0a) with the walk/`upsV3`/SHA tables, producing `HoldsP` and then the
  D3 relation through `runCall` (`NearSpecV3.D3.functionCall`, `d3Hooks`).

The proofs are **not** merged into one AIR: each is independently proved and verified, and the
join is a statement over their public values plus a shared host wire.  This mirrors
`docs/logs/pq-gap-analysis-2026-10-19.md` §2.1–2.3 and `pq-wasm-base` §14.2.

## The host wire

A `storage_write` on the Wasm side is one `HOSTQ` request, a `HOSTB` byte stream for the key and
value, and one `HOSTR` response.  The state side consumes `HOSTQ` as the driver of a ContractData
walk and an `upsV3` upsert, and produces `HOSTR` from the gas and value it computed.  The messages
are field-element lists over BabyBear; bytes are one field element each, exactly as the existing
`VBYTES (vid, pos, byte)` and `BYTES (Id, pos, byte)` buses.

| bus | id (low range, reserved for the join) | shape |
|---|---:|---|
| `HOSTQ` | 0 | `[ts, host_id, S, a0, a1, a2, a3, a4]` |
| `HOSTR` | 1 | `[ts, status, r_lo, r_hi, g_after_lo, g_after_hi, 0, 0]` |
| `HOSTB` | 2 | `[ts, dir, pos, byte]` |

`dir = 0` is Wasm → state (key/value bytes of a write), `dir = 1` is state → Wasm (a register
filled by `storage_read`, the `input`, a context string).  `ts` is the Wasm row clock and is
strictly increasing across the calls of one execution; `S` is the instruction-gas count so far.
`host_id` indexes the fixed host-function table (bound to the statement like `FUNC`).

The ids are below the Wasm base family's used ids (`0 … 6` in `pq-wasm-base`,
`WasmBase/Chips.lean`); the `BOUNDARY`/`STATE`/`FETCH`/`CH`/`R16`/`BYTE`/`DATA`/`FUNC` buses are
**not** shared.  To make the two families coexist on one bus space without renumbering the Wasm
tables, the join reserves the **top** of the state range: the HOST buses are `HOSTQ = 200`,
`HOSTR = 201`, `HOSTB = 202`, above `nearBuses = 77` and above the `pq-state-port` export's
`BUS_OFFSET = 128` shift (so a classical bus `b` exports as `128 + b ≤ 128 + 76 = 204`, and
`HOSTQ/HOSTR/HOSTB` must therefore be `> 204`; the ids are `208, 209, 210`, checked by
`host_bus_safe` below). -/

namespace ZkFormal.PQ.Join

open ZkFormal.Air ZkFormal.V2

/-- The HOST request bus id.  Must lie outside every classical bus after the `pq-state-port`
`BUS_OFFSET = 128` shift (`128 + 76 = 204`) and outside the Wasm base ids (`0 … 6`). -/
def B_HOSTQ : Nat := 208
/-- The HOST response bus id. -/
def B_HOSTR : Nat := 209
/-- The HOST byte bus id. -/
def B_HOSTB : Nat := 210

/-- `BUS_OFFSET` used by `research/near-compression/native/pq-state-port/src/main.rs`. -/
def stateBusOffset : Nat := 128
/-- The largest classical bus id (`nearBuses - 1`). -/
def stateBusMax : Nat := 76
/-- The largest Wasm base bus id (`FUNC` in `WasmBase/Chips.lean`). -/
def wasmBusMax : Nat := 6

/-- The join's bus ids do not collide with either side's shifted ids.  Kernel fact. -/
theorem host_bus_safe :
    wasmBusMax < B_HOSTQ ∧ stateBusOffset + stateBusMax < B_HOSTQ ∧
      B_HOSTQ + 1 = B_HOSTR ∧ B_HOSTR + 1 = B_HOSTB := by
  decide +kernel

/-! ## Host messages -/

/-- Split a `Nat` into two 16-bit limbs. -/
def lo16 (n : Nat) : Nat := n % 65536
def hi16 (n : Nat) : Nat := n / 65536

/-- `HOSTQ`: the request of one host call.  `args` are the popped Wasm arguments, each already a
field element (the Wasm stack values are four 16-bit limbs; a call with more than five words
sends a second row, `HOSTQ_CONT`, which this design leaves out of the `storage_write` prototype). -/
def hostQ (ts hostId gas : Nat) (args : List Nat) : List Nat :=
  [ts, hostId, gas] ++ args ++ List.replicate (5 - min args.length 5) 0

/-- `HOSTR`: the response.  `status = 0` is ok, `1` a host error, `2` gas exhausted;
`r` is the low two 16-bit limbs of the result word; `gAfter` is the state side's resynchronised
budget (`g := remaining`). -/
def hostR (ts status r gAfter : Nat) : List Nat :=
  [ts, status, lo16 r, hi16 r, lo16 gAfter, hi16 gAfter, 0, 0]

/-- `HOSTB`: one byte of a byte string moved between the sides.  `dir = 0` is Wasm → state. -/
def hostB (ts dir pos byte : Nat) : List Nat := [ts, dir, pos, byte]

/-- The host-function table.  Only the entries the `storage_write` prototype needs are named; the
full table is part of the Wasm statement (bound like `FUNC`). -/
def hostIdStorageWrite : Nat := 0

/-- The request arguments of `storage_write(key_len, key_ptr, val_len, val_ptr, register_id)`
(`Host.lean:693-725`).  The bytes themselves travel on `HOSTB`, keyed by `ts`; the request gives
the lengths and the register. -/
def storageWriteQ (ts gas keyLen valLen regId : Nat) : List Nat :=
  hostQ ts hostIdStorageWrite gas [keyLen, valLen, regId]

/-! ## The wire

One `wire` is the shared, time-ordered stream of host messages.  It is the *only* cross-proof
object: the two proofs each project it onto their own bus traffic, and the aggregation checks that
both projections are the same multiset. -/

structure Wire where
  /-- every request, in `ts` order -/
  q : List (List Nat)
  /-- every response, in `ts` order -/
  r : List (List Nat)
  /-- every byte, in `(ts, dir, pos)` order -/
  b : List (List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `ts` strictly increases along the request stream.  This is what lets the state side process
requests as a sequence and reuse the trie overlay in order. -/
def Wire.tsIncreasing (w : Wire) : Prop :=
  (w.q.map (·.getD 0 0)).Pairwise (· < ·)

/-- Every response answers the request at the same `ts`. -/
def Wire.responsesMatch (w : Wire) : Prop :=
  w.q.map (·.getD 0 0) = w.r.map (·.getD 0 0)

/-- Bytes of a call are contiguous in `pos` and carry its `ts`. -/
def Wire.bytesWellFormed (w : Wire) : Prop :=
  ∀ m ∈ w.b, m.length = 4

/-! ## The side statements -/

/-- The Wasm base statement's public values (`WasmBase/Chips.lean`, `Boundary.pubN …`).  The
`code_root` is the cached CODE commitment; `code_hash` is the receipt's contract code hash,
bound on the state side. -/
structure WasmStmt where
  codeRoot : Nat
  codeHash : List Nat
  steps : Nat
  finalGas : Nat
  nres : Nat
  resultTag : Nat
  result : List Nat
  status : Nat
  memSize : Nat
  dataEnd : Nat
  /-- HOST traffic, projected from the wire -/
  hostQ : List (List Nat)
  hostR : List (List Nat)
  hostB : List (List Nat)

/-- The state statement: the D2/D3 claim plus the parts the join reads.  `walks` and `finals` are
the `walkV3`/`cdWalkV3` and `FINAL` views; `values` are the `valV3` value records; `overlay` is
the `RealStore.writes` log committed by the state proof (`TrieStore.lean:168`). -/
structure StateStmt where
  prevRoot : List Nat
  postRoot : List Nat
  /-- `account -> contract code hash` as read by the account table (the `w.shape` binding) -/
  contractOf : List Nat → Option (List Nat)
  /-- `(walk id, instance) -> key path` accepted by the walk table -/
  walkPath : Nat → Nat → Option (List Nat)
  /-- `walk id -> (fk, k)` from the terminal row (`walkV3`'s `FINAL`) -/
  walkFinal : Nat → Option (Nat × Nat)
  /-- value record id -> bytes (`valV3`) -/
  valueRecord : Nat → Option (List Nat)
  /-- the ordered write log of a successful call (`RealStore.writes`) -/
  writes : List (List Nat × Option (List Nat))
  hostQ : List (List Nat)
  hostR : List (List Nat)
  hostB : List (List Nat)

/-- The state proof's code binding: the executing account's contract hash equals the Wasm
statement's `code_hash`.  This is the `receipt → code_hash` link `pq-wasm-base` §5 leaves open. -/
def CodeBound (w : WasmStmt) (s : StateStmt) (account : List Nat) : Prop :=
  s.contractOf account = some w.codeHash

/-- The cached `code_root` is a deterministic function of the code hash (the state side's deploy
or account value determines the code; V_d recomputes the root, `pq-wasm-base/STATEMENT.md` §2).
Stated as an abstract predicate: the join consumes it, it is not proved here. -/
def CodeRootBound (w : WasmStmt) (s : StateStmt) : Prop :=
  ∃ code, s.contractOf code = some w.codeHash

/-! ## The state half of one `storage_write` -/

/-- One `storage_write` as the join sees it. -/
structure StorageWrite where
  ts : Nat
  /-- account id bytes (one field element per byte) -/
  account : List Nat
  /-- data key bytes -/
  key : List Nat
  /-- value bytes being written -/
  value : List Nat
  /-- the value in the pre-state trie at `contractDataKey account key`; `none` = the write is an
  insertion (`ContractData` path absent / branch without a value).  This is what the walk sees. -/
  preValue : Option (List Nat) := none
  /-- `true` iff the call succeeded and the write is committed; a failed call rolls back
  (`FunctionCall.lean:322-329`) and the write appears in `writes` but not in the overlay. -/
  committed : Bool

/-- **The state half of a `storage_write`, stated.**  For the write's `ts` there is a walk id and
a value record such that

1. the walk table's path is the ContractData path `[9] ‖ account ‖ [44] ‖ key`
   (`D3.ContractData.contractDataPath`) — this is the piece the D1 port does not have;
2. the terminal describes the **pre-state**: `FINAL` kind `1` (`FK_ABS`) when the key is absent
   (an insertion), or kind `0` (`FK_VAL`) into a value record equal to `preValue` when the key is
   present (an overwrite).  The walk is over the pre-state trie; the new value enters only through
   `upsV3`, never through the walk;
3. the state's write log contains `(contractDataKey account key, some value)` at a position
   matching `ts`'s order;
4. if `committed`, the `upsV3` post-state applies that write: `postRoot` is the root of the
   pre-state with the log applied.

Parts (1)–(3) are the walk/value/write facts; (4) is the `upsV3` obligation.  This `Prop` is
**stated, not proved**. -/
def StateHalfStorageWrite (s : StateStmt) (w : StorageWrite) (preUpsertPost : List Nat) : Prop :=
  -- (1) the path the walk table accepts is the ContractData path, not the account key
  (∃ wid tau,
      s.walkPath wid tau = some (ZkFormal.NearV3.D3.contractDataPath (w.account.map UInt8.ofNat)
        (w.key.map UInt8.ofNat))) ∧
  -- (2) the terminal describes the *pre*-state: absent (ABS) for an insertion, VAL into a value
  -- record equal to the old bytes for an overwrite.  The new value never enters the walk.
  (match w.preValue with
    | none => ∃ wid, s.walkFinal wid = some (1, 0)
    | some old => ∃ wid vid, s.walkFinal wid = some (0, vid) ∧ s.valueRecord vid = some old) ∧
  -- (3) the ordered write log carries `(full trie key, some new value)`
  ((ZkFormal.NearV3.D3.contractDataKey (w.account.map UInt8.ofNat) (w.key.map UInt8.ofNat)).map
      UInt8.toNat, some w.value) ∈ s.writes ∧
  -- (4) a committed write is applied by `upsV3`
  (w.committed = true → s.postRoot = preUpsertPost)

/-- The write-log order matches the wire's `ts` order: the state applies the calls in the order
the Wasm proof made them.  `storage_write`s only (the prototype's scope). -/
def WritesAlignedWithWire (s : StateStmt) (ws : List StorageWrite) : Prop :=
  ws.map (fun w => (ZkFormal.NearV3.D3.contractDataKey (w.account.map UInt8.ofNat)
    (w.key.map UInt8.ofNat)).map UInt8.toNat) = s.writes.map (·.1)

/-! ## The cross-proof bus balance -/

/-- A side's projection of the wire is the wire.  This is the *whole* cross-proof obligation for
the HOST buses: the Wasm proof's `HOSTQ`/`HOSTR`/`HOSTB` traffic and the state proof's must be
the same multiset, which — because both sides project the same ordered wire — is equality of the
projections each side's public values expose. -/
def HostTrafficAgrees (w : WasmStmt) (s : StateStmt) : Prop :=
  w.hostQ = s.hostQ ∧ w.hostR = s.hostR ∧ w.hostB = s.hostB

/-- The joint bus balance: on every bus and message, sends from both sides equal receives from
both sides.  Over the HOST buses this is `HostTrafficAgrees` plus the direction convention (the
Wasm side sends `HOSTQ` and receives `HOSTR`/`HOSTB`; the state side receives `HOSTQ` and sends
`HOSTR`/`HOSTB`).  On the state side's own buses it is the `HoldsP.balance` of the state AIR; on
the Wasm side it is the `Holds` balance of the base AIR.  Stated structurally, not proved. -/
def JointBusBalance (w : WasmStmt) (s : StateStmt) : Prop :=
  HostTrafficAgrees w s ∧
    (∀ m ∈ w.hostQ, m ∈ s.hostQ) ∧ (∀ m ∈ s.hostQ, m ∈ w.hostQ) ∧
    (∀ m ∈ w.hostR, m ∈ s.hostR) ∧ (∀ m ∈ s.hostR, m ∈ w.hostR) ∧
    (∀ m ∈ w.hostB, m ∈ s.hostB) ∧ (∀ m ∈ s.hostB, m ∈ w.hostB)

/-! ## The joint statement -/

/-- The two side relations, as opaque `Prop`s: `WasmHolds` is the HOST-extended base relation
(`Holds (wasmBaseAir …)` plus the HOST chip's traffic), `StateHolds` is the state relation
(`HoldsP nearAirV3D1 …` plus the D3 `runCall` fold).  They are parameters because each side's
theorem lives in its own lane; this file states how they compose. -/
structure JointStmt where
  /-- the claim's pre-state root (`prev_state_root`), as field elements -/
  prevRoot : List Nat
  /-- the claim's post-state root -/
  postRoot : List Nat
  /-- the executing account id -/
  account : List Nat
  /-- the Wasm contract code hash (sha256 of the code) -/
  codeHash : List Nat
  wasm : WasmStmt
  state : StateStmt
  wire : Wire
  /-- the storage writes of this FunctionCall, in `ts` order -/
  writes : List StorageWrite
  /-- each write's `upsV3` post-state root -/
  postAfter : StorageWrite → List Nat
  /-- **Wasm side**: the base relation holds with the HOST traffic -/
  wasmHolds : WasmStmt → Wire → Prop
  /-- **State side**: the state relation holds with the HOST traffic -/
  stateHolds : StateStmt → Wire → Prop

/-- **The joint statement** (stated, not proved).

A Wasm FunctionCall proof and a state proof compose when

* each side's relation holds with the same host wire (`wasmHolds`, `stateHolds`);
* the roots agree: `state.prevRoot = prevRoot`, `state.postRoot` is the post root after the
  writes, and the Wasm side's `code_hash` equals the state side's contract hash for `account`
  (`CodeBound`);
* the wire is well formed (`ts` increasing, responses match, bytes have the right shape);
* every `storage_write` has its state half (`StateHalfStorageWrite`), and the write log is in
  the wire's order (`WritesAlignedWithWire`);
* the cross-proof bus balance holds (`JointBusBalance`).

The joint public values are exactly the union of the two sides' public values plus the wire's
three commitments; `prevRoot`, `postRoot`, `account` and `codeHash` are duplicated on both sides
and must agree.  This `def` is the specification; the soundness theorem (the two side theorems
plus the balance imply `RelD3`) is **not** proved here and is the remaining join obligation. -/
def Joint (j : JointStmt) : Prop :=
  j.wasmHolds j.wasm j.wire ∧
  j.stateHolds j.state j.wire ∧
  j.wire.tsIncreasing ∧ j.wire.responsesMatch ∧ j.wire.bytesWellFormed ∧
  j.state.prevRoot = j.prevRoot ∧
  j.state.postRoot = j.postRoot ∧
  CodeBound j.wasm j.state j.account ∧
  (j.wasm.codeHash = j.codeHash) ∧
  (∀ w ∈ j.writes, StateHalfStorageWrite j.state w (j.postAfter w)) ∧
  WritesAlignedWithWire j.state j.writes ∧
  JointBusBalance j.wasm j.state

/-! ## What the two side theorems must supply

Stated as separate `Prop`s so the checklist can name them:

* `WasmHalf` — `wasm_base_sound` (`pq-wasm-base` `Main/Final.lean`) extended with the HOST chip:
  under `check`, `CodeOK`, `PubOK` and the statement conditions, the run ends with the public
  result/status and the HOST traffic is exactly the wire (`pq-wasm-base` §8 lists the missing
  OOG/import pieces).
* `StateHalf` — the D0a/D1 extraction (`pq-state-port` `D0a.pq_d0a_rel`) plus the D3 `runCall`
  fold: a `HoldsP` proof of the state tables yields `RelD3` for the receipt, with the storage
  writes replayed in order.
* `Compose` — `Joint → RelD3` for the chunk's FunctionCall receipt. -/

/-- Wasm half (stated). -/
def WasmHalf (j : JointStmt) : Prop :=
  j.wasmHolds j.wasm j.wire →
    j.wasm.status = 1 ∨ j.wasm.status = 2

/-- State half (stated). -/
def StateHalf (j : JointStmt) : Prop :=
  (∀ w ∈ j.writes, StateHalfStorageWrite j.state w (j.postAfter w))

/-- Composition (stated): the joint statement implies the chunk relation for this receipt.
`RelD3` is `NearSpecV3.D3.RelD3`; the composition is the join's main remaining proof. -/
def Compose (chunkClaim chunkWitness : NearSpec.Bytes) (j : JointStmt) : Prop :=
  Joint j → NearSpecV3.D3.RelD3 chunkClaim chunkWitness

end ZkFormal.PQ.Join
