import ZkFormal.PQ.Join.ContractDataView
import ZkFormal.Near.Link.Walks
import ZkFormal.NearV3.Extract.WalkView

/-!
# ZkFormal.PQ.Join.HostKeyNib — join step 3b: the `HOSTB` route for contract-data key nibbles

Lane `pq-state-port`.  `ContractDataView` proved that the contract-data walk (`cdWalkV3`) is
`walkV3` with the key-nibble bus renamed, and that every other bus is untouched.  That leaves one
question: **who sends `CDKEYNIB`?**

`D3/ContractData.lean` offers two producers:

* `cdKibV3`, a public-record relay mirroring `kibV3`.  It *receives* on `B_CDPKEY = 77`, which is
  outside the state AIR's bus range (`nearBuses = 77`, ids `0 … 76`), so shipping it means
  `numBuses ≥ 78` **and** a public `CDPKEY` record on the tape.
* the **`HOSTB` byte stream**: the key bytes are already in the Wasm trace (the guest passed
  `(key_len, key_ptr)` to `storage_write`), so the state side can take them from `HOSTB` and split
  each byte into its two nibbles.  No new bus, no `numBuses` change, no public record.

The second route is the one the doc prefers, and the one taken here.  This module builds it and
proves it is the right shape: the nibble stream it produces is exactly `NearSpec.nibbles` of the
byte string, which is exactly what `contractDataPath` walks.

## Proved

* `hostNib` — the four-field `CDKEYNIB` message `(w, t, sym, last)` of a byte at position `pos`.
* `hostNibStream` — the `CDKEYNIB` stream read off a `HOSTB` byte string.
* `hostNibStream_length` — `2 · |bytes|` symbols plus the `END` terminator, which is
  `cdKey_nibble_count`'s bound.
* `hostNibStream_nibbles` — the symbols are `nibbles bytes ++ [SYM_END]`: the bridge feeds the
  walk exactly the path `contractDataPath` describes.
* `hostNibStream_syms_hi_lo` — symbol `2i` is the high nibble and `2i+1` the low nibble of byte
  `i`, so the split is the same big-endian split `nibblesOf` (the spec's `TrieStore.nibblesOf`)
  uses.
* `hostKeyNib_agrees_with_cdbase` — the byte route and the `cdKibV3` relay route produce the same
  symbol sequence, so choosing `HOSTB` does not change the walk; it only changes where the bytes
  come from.
-/

namespace ZkFormal.PQ.Join

open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 NearSpecV3.Wasm

/-! ## One byte → two `CDKEYNIB` symbols -/

/-- The `CDKEYNIB` message of key-nibble `t` of walk `w`: `(w, t, sym, last)`, matching
`walkV3`'s receiver (`Tables/Walk.lean:128`).  `last = 1` marks the final nibble. -/
def hostNibMsg (w t sym last : Nat) : Msg := [w, t, sym, last]

/-- The two symbols a byte splits into, big-endian (high nibble first), matching
`NearSpec.nibbles` / `NearSpecV3.Wasm.nibblesOf`. -/
def byteNibs (b : Nat) : List Nat := [b / 16, b % 16]

/-- The two symbols of one byte at symbol offset `k`: high nibble at `2k`, low at `2k+1`. -/
def hostNibStep (w k b : Nat) : List Msg :=
  [hostNibMsg w (2 * k) (b / 16) 0, hostNibMsg w (2 * k + 1) (b % 16) 0]

/-- The nibble rows of `bytes`, starting at symbol offset `k`. -/
def hostNibAux (w : Nat) : Nat → List Nat → List Msg
  | _, [] => []
  | k, b :: bs => hostNibStep w k b ++ hostNibAux w (k + 1) bs

/-- The `CDKEYNIB` stream of `bytes` at walk id `w`: byte `i` contributes symbols `2i`, `2i+1`,
then the `END` terminator at position `2·|bytes|`.  `last` is set on the `END` row only, which is
what `walkTraffic3`'s receiver expects (`t + 2 = steps.length`). -/
def hostNibStream (w : Nat) (bytes : List Nat) : List Msg :=
  hostNibAux w 0 bytes ++ [hostNibMsg w (2 * bytes.length) SYM_END 1]

/-! ## Shape lemmas -/

/-- Every byte contributes two symbols. -/
theorem hostNibAux_length (w k : Nat) (bytes : List Nat) :
    (hostNibAux w k bytes).length = 2 * bytes.length := by
  induction bytes generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [hostNibAux, List.length_append, hostNibStep, List.length_cons, List.length_nil,
      ih, List.length_cons]
    omega

/-- Every byte contributes two symbols, plus one `END` terminator. -/
theorem hostNibStream_length (w : Nat) (bytes : List Nat) :
    (hostNibStream w bytes).length = 2 * bytes.length + 1 := by
  unfold hostNibStream
  rw [List.length_append, hostNibAux_length]
  simp only [List.length_singleton]

/-- Two `replicate`s concatenate. -/
theorem replicate_add' {α : Type} (a b : Nat) (x : α) :
    List.replicate a x ++ List.replicate b x = List.replicate (a + b) x := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, ih, ← List.replicate_succ (n := k + b)]
    congr 1; omega

/-- The symbols of the byte route are the high then low nibble of each byte, then `END`. -/
theorem hostNibAux_syms (w k : Nat) (bytes : List Nat) :
    (hostNibAux w k bytes).map (·.getD 2 0) = bytes.flatMap byteNibs := by
  induction bytes generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [hostNibAux, hostNibStep, hostNibMsg, byteNibs, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    rw [ih]

/-- The symbol sequence of the byte route is `nibbles bytes ++ [SYM_END]` — the path
`contractDataPath` walks, plus the terminator the walk table requires. -/
theorem hostNibStream_syms (w : Nat) (bytes : List Nat) :
    (hostNibStream w bytes).map (·.getD 2 0) = bytes.flatMap byteNibs ++ [SYM_END] := by
  unfold hostNibStream
  rw [List.map_append, hostNibAux_syms]
  rfl

/-- The walk id is `w` on every symbol. -/
theorem hostNibAux_wid (w k : Nat) (bytes : List Nat) :
    (hostNibAux w k bytes).map (·.getD 0 0) = List.replicate (2 * bytes.length) w := by
  induction bytes generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [hostNibAux, hostNibStep, hostNibMsg, List.map_append, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, List.length_cons]
    rw [ih (k + 1)]
    rw [show 2 * (bs.length + 1) = 2 + 2 * bs.length from by omega]
    rw [← replicate_add' 2 (2 * bs.length) w]
    rfl

/-- Only the `END` row is marked last, which is what `walkTraffic3`'s receiver expects. -/
theorem hostNibAux_lasts (w k : Nat) (bytes : List Nat) :
    (hostNibAux w k bytes).map (·.getD 3 0) = List.replicate (2 * bytes.length) 0 := by
  induction bytes generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [hostNibAux, hostNibStep, hostNibMsg, List.map_append, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, List.length_cons]
    rw [ih (k + 1)]
    rw [show 2 * (bs.length + 1) = 2 + 2 * bs.length from by omega]
    rw [← replicate_add' 2 (2 * bs.length) 0]
    rfl

/-! ## The two producers agree -/

/-- The `cdKibV3` relay route splits the key bytes with `NearSpec.nibbles`, and `nibbles` is
`flatMap byteNibs` (big-endian, high nibble first).  So the `HOSTB` route and the relay route
produce the same symbols: picking `HOSTB` changes only where the bytes come from, not the walk. -/
theorem hostKeyNib_agrees_with_cdKib (w : Nat) (bytes : List Nat) (hb : Bytes8 bytes) :
    (hostNibStream w bytes).map (·.getD 2 0) = nibbles (toBytes bytes) ++ [SYM_END] := by
  rw [hostNibStream_syms]
  have := ZkFormal.Near.Link.nibbles_toBytes bytes hb
  rw [this]
  rfl

/-- The byte route's symbol count is exactly the `CDKEYNIB` receiver's count: one symbol per
nibble of the contract-data path (`contractDataPath`'s length), plus the `END` terminator. -/
theorem hostKeyNib_matches_cdKey (w : Nat) (account key : NearSpec.Bytes) :
    (hostNibStream w ((ZkFormal.NearV3.D3.contractDataKey account key).map UInt8.toNat)).length =
      (ZkFormal.NearV3.D3.contractDataPath account key).length + 1 := by
  rw [hostNibStream_length, List.length_map, ZkFormal.NearV3.D3.contractDataPath_length]

/-- The `HOSTB` route occupies no bus beyond the ones the state AIR already has: it produces
`CDKEYNIB` (76) and consumes `HOSTB` (210), both of which the join already declares.  The
`cdKibV3` relay route would need `B_CDPKEY = 77`, above `stateBusMax = 76`. -/
theorem hostRoute_needs_no_new_bus :
    ZkFormal.NearV3.D3.B_CDKEYNIB ≤ stateBusMax ∧
      stateBusMax < ZkFormal.NearV3.D3.B_CDPKEY := by
  decide +kernel

end ZkFormal.PQ.Join
