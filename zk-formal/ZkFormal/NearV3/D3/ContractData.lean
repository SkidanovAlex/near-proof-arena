import ZkFormal.NearV3.Tables.Walk
import ZkFormal.NearV3.D1.Tables.RelayDefs
import NearSpec.Trie

/-!
# `ZkFormal.NearV3.D3.ContractData` — the `TrieKey::ContractData` key prefix and its walk tables

Lane `pq-d3-join`.  **Definitions and stated specs only; nothing here is proved as a theorem
about a full AIR except the cheap `decide +kernel` facts explicitly labelled `example`.**

## Why this is new work

The D1 tables are **transfer-only**: `spec/lean/v3/NearSpecV3/TxD1.lean:97` rejects every action
that is not `Transfer(3)`, `NearSpecV3.RuntimeD1.txKeys` walks only `accountKeyPath` and
`keyAccessKey`, and no table in `nearAirV3` / `nearAirV3D1` mentions `TrieKey::ContractData`.
Contract storage is therefore **not** inherited from the D1 port; the walk, key routing and key
nibbles below are the missing piece.

## The key

`nearcore` (`core/primitives/src/trie_key.rs:452-560`, `col::CONTRACT_DATA = 9`) encodes a
contract-data key as

```
0x09 ‖ account_id ‖ 0x2c (',') ‖ data_key
```

`NearSpecV3.Wasm.TTN.contractDataPrefix` (`spec/lean/v3/NearSpecV3/Wasm/TrieStore.lean:172`)
is exactly `#[9] ++ account.toUTF8 ++ #[44]`; `RealStore.pfx` holds it for the current account and
`realOpH` / `realSetH` concatenate `pfx ++ data_key` (`Host.lean:40,56`).  A `storage_write`
therefore walks the full path of `[9] ++ account ++ [44] ++ key`, not of the account key.

## What the existing walk machinery needs

`walkV3` (`Tables/Walk.lean`) is key-agnostic: it consumes symbols from `KEYNIB (w, τ, sym, last)`
and follows `EDGE` / `BMAP` / `FINAL`, which are all shared with the node/value records.  A
`ContractData` walk is the *same table* with a different key-nibble producer.  The only new pieces
are

* a bus id for the ContractData key nibbles, `B_CDKEYNIB = 76` (unused: `nearBuses = 77`, the D1
  buses stop at `75`; `pq-state-port` shifts classical buses by `BUS_OFFSET = 128` at export);
* a relay (`cdKibV3`) that turns the public `PKEY` record of a ContractData key into
  `CDKEYNIB`, mirroring `kibV3` (`D1/Tables/RelayDefs.lean`) — or, for the D3 statement, the
  `HOSTB` byte stream supplies the key bytes directly and no public record is needed;
* the walk table itself: `cdWalkV3` below, literally `walkV3` with `B_KEYNIB` renamed.

The node, value, uniqueness, SHA-256, `upsV3`, `headV3` and `size` tables are **unchanged**: a
ContractData path is an ordinary trie path, its value is an ordinary value record (`VBYTES`), and
the post-state is an ordinary `upsV3` upsert.  This is the "D3-join, not D1-join" correction of
`docs/logs/pq-gap-analysis-2026-10-19.md` §4: the AIRs are reusable, the *key routing* is not.

## Prefix facts (`decide +kernel`, cheap)

`contractDataKey "s0rc" "a" = [9, 115, 48, 114, 99, 44, 97]`, i.e. nibbles
`[0,9, 7,3, 3,0, 7,2, 6,3, 2,12, 6,1]`.  The first two nibbles are the constant `(0,9)`; the last
two bytes before the key are `(2,12)` = `0x2c`.  The general lemma is the stated (unproved) shape
`nibbles_contractData`, kept as a `Prop` so this file adds no theorems it cannot prove here.
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-! ## The key and its prefix -/

/-- `col::CONTRACT_DATA` (`trie_key.rs`), one byte. -/
def colContractData : UInt8 := 9
/-- `ACCOUNT_DATA_SEPARATOR = b','` (`trie_key.rs`). -/
def accountDataSeparator : UInt8 := 44

/-- `TrieKey::ContractData(account, key)` as bytes (`NearSpec.Bytes`, little-endian-as-written). -/
def contractDataKey (account key : NearSpec.Bytes) : NearSpec.Bytes :=
  [colContractData] ++ account ++ [accountDataSeparator] ++ key

/-- The nibble path walked for a contract-data key (`NearSpec.nibbles`, high nibble first). -/
def contractDataPath (account key : NearSpec.Bytes) : List Nat :=
  NearSpec.nibbles (contractDataKey account key)

/-- `RealStore.pfx` of the current account, as `NearSpec.Bytes`
(`TTN.contractDataPrefix`, `TrieStore.lean:172`). -/
def contractDataPrefix (account : NearSpec.Bytes) : NearSpec.Bytes :=
  [colContractData] ++ account ++ [accountDataSeparator]

/-- The `TrieKey::ContractData` prefix of the executing account, in nibbles.  The first two
nibbles are the constant `(0, 9)`; the key's own nibbles follow the separator nibbles `(2, 12)`. -/
def contractDataPrefixPath (account : NearSpec.Bytes) : List Nat :=
  NearSpec.nibbles (contractDataPrefix account)

/-- **Stated (unproved) shape of the nibble path.**  For any account and key, the path is the
prefix path followed by the key's nibbles, and its length is `2·(1 + |account| + 1 + |key|)`.
This is the fact the walk table's `KEYNIB` stream must satisfy; it follows from
`nibbles (p ++ q) = nibbles p ++ nibbles q` (provable, and used as an `example` below). -/
def ContractDataPathSpec (account key : NearSpec.Bytes) : Prop :=
  contractDataPath account key = contractDataPrefixPath account ++ NearSpec.nibbles key ∧
    (contractDataPath account key).length = 2 * (contractDataKey account key).length

/-! ## Bus and table ids -/

/-- `CDKEYNIB (w, τ, sym, last)`: the ContractData key nibbles, one bus below `nearBuses = 77`.
`76` is unused by `nearAirV3` (max used `75`), by the D1 tables (`67 … 71`) and by the
`pq-state-port` export (classical buses are shifted by `128`). -/
def B_CDKEYNIB : Nat := 76

/-- The ContractData walk id base.  The walk id is `(receipt_index, op_index, key_kind)` on the
state side; it is the same namespace as `W_TX` so `FINAL` consumers can tell the walks apart. -/
def W_CD : Nat := 2 ^ 21

/-! ## The walk table: `walkV3` with the key-nibble bus renamed -/

/-- Rename every occurrence of bus `src` to bus `dst` in a table's interactions.  Constraints,
width and `maxLog` are untouched, so every `walkV3` constraint lemma applies verbatim and only
the key-stream producer changes. -/
def renameBus (src dst : Nat) (t : Table) : Table :=
  { t with interactions := t.interactions.map fun i => if i.bus = src then { i with bus := dst } else i }

/-- `cdWalkV3`: the ContractData key walk.  One table serves *all* ContractData walks of a chunk
(all accounts, all keys): the walks are distinguished by `(w, τ)` as in `walkV3`, and a chunk's
storage operations are linearised by the `HOSTQ` stream. -/
def cdWalkV3 : Table := renameBus B_KEYNIB B_CDKEYNIB WalkV3.table

/-- `cdKibV3`: the public-record relay for a ContractData key, mirroring `kibV3`
(`D1/Tables/RelayDefs.lean`).  A row carries the key's prefix and the key bytes; it sends the key
nibbles on `CDKEYNIB`.  This is the *state-side* alternative to taking the bytes from `HOSTB`;
a D3 implementation will normally use the `HOSTB` route (the bytes are already in the Wasm trace)
and keep this relay only for witnesses supplied with the key in the public tape. -/
def cdKibAct : Nat := 0
/-- `wl, wm, wh`: three bytes of the walk id `w = w0 + 2^8 w1 + 2^16 w2`. -/
def cdKibW (i : Nat) : Nat := 1 + i
/-- instance / continent id -/
def cdKibTau : Nat := 4
/-- key symbol and its last flag -/
def cdKibSym : Nat := 5
def cdKibLast : Nat := 6
def cdKibPrefix : Nat := 7
def cdKibWidth : Nat := 7

/-- `w = w0 + 2^8·w1 + 2^16·w2`. -/
def cdKibWE : Expr := sum [c (cdKibW 0), smul 256 (c (cdKibW 1)), smul 65536 (c (cdKibW 2))]

/-- One row per `(w, τ, sym, last)` relayed key symbol.  `act` is the multiplicity bit, so the
table is a one-row-per-symbol relay exactly like `kibV3`. -/
def cdKibConstraints : List Expr := [bool (c cdKibAct)]

/-- Opaque public record `CDPKEY (w0, w1, w2, τ, sym, last)`.  `cdKib` is its only producer; it
sends `CDKEYNIB`.  This bus is outside the state AIR's range (`nearBuses = 77`, ids `0 … 76`), so
including `cdKibV3` in one AIR with the state tables needs `numBuses ≥ 78`; `cdWalkV3` alone does
not, which is why the `HOSTB` route is preferred. -/
def B_CDPKEY : Nat := 77

def cdKibInteractions : List Interaction :=
  [ recv B_CDPKEY (c cdKibAct) [c (cdKibW 0), c (cdKibW 1), c (cdKibW 2), c cdKibTau,
        c cdKibSym, c cdKibLast],
    send B_CDKEYNIB (c cdKibAct) [cdKibWE, c cdKibTau, c cdKibSym, c cdKibLast] ]

/-- `≤ 2·NT0 · (1 + 2·65)` key symbols; `< 2^22`, the `walkV3` cap. -/
def cdKibMaxLog : Nat := 22

def cdKibV3 : Table :=
  { width := cdKibWidth, constraints := cdKibConstraints, interactions := cdKibInteractions,
    maxLog := cdKibMaxLog }

/-! ## Kernel-checked cheap facts -/

/-- `09 73 30 72 63 2c 61` = `0x09 "s0rc" 0x2c "a"`. -/
example : contractDataKey [115, 48, 114, 99] [97] = [9, 115, 48, 114, 99, 44, 97] := by
  decide +kernel

/-- The separator nibbles are `(2, 12)`; the collection nibble is `(0, 9)`. -/
example : NearSpec.nibbles [9, 115] = [0, 9, 7, 3] := by decide +kernel
example : NearSpec.nibbles [44, 97] = [2, 12, 6, 1] := by decide +kernel

/-- The prefix path of `"s0rc"`: `0x09 "s0rc" 0x2c` -> 12 nibbles. -/
example : contractDataPrefixPath [115, 48, 114, 99] =
    [0, 9, 7, 3, 3, 0, 7, 2, 6, 3, 2, 12] := by decide +kernel

/-- The full path of `"s0rc"` / `"a"`: 14 nibbles, prefix then the key nibble `(6, 1)`. -/
example : contractDataPath [115, 48, 114, 99] [97] =
    [0, 9, 7, 3, 3, 0, 7, 2, 6, 3, 2, 12, 6, 1] := by decide +kernel

example : (contractDataKey [115, 48, 114, 99] [97]).length = 7 := by decide +kernel

/-- The reusable nibble-splitting identity behind `ContractDataPathSpec`. -/
theorem nibbles_append (p q : NearSpec.Bytes) :
    NearSpec.nibbles (p ++ q) = NearSpec.nibbles p ++ NearSpec.nibbles q := by
  induction p with
  | nil => rfl
  | cons b bs ih => simp [NearSpec.nibbles, ih]

/-- `nibbles` has twice as many entries as bytes. -/
theorem nibbles_length (b : NearSpec.Bytes) : (NearSpec.nibbles b).length = 2 * b.length := by
  induction b with
  | nil => rfl
  | cons x xs ih => simp [NearSpec.nibbles, ih]; omega

/-- The path length identity (proved, from `nibbles_length`). -/
theorem contractDataPath_length (account key : NearSpec.Bytes) :
    (contractDataPath account key).length = 2 * (contractDataKey account key).length :=
  nibbles_length (contractDataKey account key)

/-- `ContractDataPathSpec` holds (the `∧` is the proved length plus the proved split). -/
theorem contractDataPathSpec_holds (account key : NearSpec.Bytes) :
    ContractDataPathSpec account key := by
  refine ⟨?_, contractDataPath_length account key⟩
  simp only [contractDataPath, contractDataPrefixPath, contractDataPrefix, contractDataKey,
    List.append_assoc, nibbles_append]

/-- The walk table is `walkV3` with one bus renamed: same width and constraints. -/
example : cdWalkV3.width = WalkV3.table.width := rfl
example : cdWalkV3.constraints = WalkV3.table.constraints := rfl
example : cdWalkV3.maxLog = WalkV3.table.maxLog := rfl

/-- `walkV3`'s first interaction receives `KEYNIB`; `cdWalkV3`'s receives `CDKEYNIB`, and no
interaction of `cdWalkV3` still uses `KEYNIB`. -/
example : (cdWalkV3.interactions.filter (·.bus = B_CDKEYNIB)).length = 1 := by decide +kernel
example : (cdWalkV3.interactions.filter (·.bus = B_KEYNIB)).length = 0 := by decide +kernel
example : B_CDKEYNIB ≠ B_KEYNIB := by decide +kernel
example : B_CDKEYNIB < 77 := by decide +kernel

/-- The relay's `act` is boolean and it is the only producer of `CDKEYNIB`; the relay receives
`CDPKEY`. -/
example : cdKibV3.constraints = [bool (c cdKibAct)] := rfl
example : (cdKibV3.interactions.map (·.bus)) = [B_CDPKEY, B_CDKEYNIB] := by decide +kernel

end ZkFormal.NearV3.D3
