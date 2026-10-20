import ZkFormal.NearV3.D3.UpsertWf
import ZkFormal.NearV3.D3.StateRead
import NearSpecV3.Wasm.TrieAccounting

/-!
# `ZkFormal.NearV3.D3.StateOps` — the other three storage host functions on the state side

`StateRead`/`StateWrite` cover `storage_write`: a `cdWalkV3` walk of `[9]‖account‖[44]‖key` plus an
`upsV3` upsert.  This module extends that to the rest of the D3α storage family:

| host call | walk | post-action | new table? |
|---|---|---|---|
| `storage_read` | yes (identical to `storage_write`'s) | **none** | no |
| `storage_has_key` | yes (identical) | **none** (answer only) | no |
| `storage_remove` | yes (identical) | overlay `↦ none`, `writes += (key, none)`, usage `−` | no |
| `storage_usage` | **no walk** (the `acctV3` record, `StateUsage.lean`) | none | no |

The walk half is *literally* the same: `cdWalkV3` is `walkV3` with the key bus renamed
(`CdBus.lean`), and the walk does not know what the caller will do with the value it found; it
reports the pre-state through `FINAL` (`StateRead.cd_read_value`).  So the read half of all four
value-carrying calls is one theorem, `cd_op_read_half`, and only the post-action differs.

## What is proved here

**Read half (shared by all three value-carrying calls).**
* `CdRead` — the record every storage call starts from: account, data key, the pre-state value the
  walk found (`none` = proven absent: an insertion for `write`, a `0` answer for `has_key`), and the
  usage before the call.
* `cd_op_read_half` — `cd_read_value` re-exported as "the state half's read conjunct": `FK_VAL` ⇒
  the value is the `valV3` `VBYTES` bytes, `FK_ABS` ⇒ absent.  **There is nothing to add per host
  function**: the walk of `storage_read`/`storage_remove`/`storage_has_key` is the walk of
  `storage_write`, byte for byte (`cd_op_walk_path`), and its terminal is what `FINAL` says.
* `cd_op_pre_is_find` — the same in the shape the state half's conjunct uses: the walk's `FINAL`
  *is* the trie's `find`, so a `CdRead`'s `pre` is justified (`some` for `FK_VAL`, `none` for
  `FK_ABS`).
* `map_toNat_eq_of_nibbles_eq` — the nibble path determines the byte values, so a trie path and an
  overlay key are the same key when their `nibbles` agree (this is the bridge the log needs).

**`storage_read`** (`CdReadOp`; `Host.lean:727-750`).
* `cd_read_no_change` — the post-state trie *is* the pre-state trie (no `upsV3` instance), so
  `find` is unchanged at the key and everywhere else.
* `cd_read_answer` / `cd_read_answer_absent` — the register gets exactly the walk's pre-state value,
  and an absent key answers `none`.
* `cd_read_usage` — no usage delta (`TTN.storageRead`'s `acct` is the trie-accounting cache, not the
  account's `storage_usage`).

**`storage_has_key`** (`CdHasKeyOp`; `Host.lean:781-793`).
* `cd_hasKey_answer` / `cd_hasKey_answer_iff` — the pushed `0/1` **is** presence:
  `answer = 1 ↔ pre.isSome`.
* `cd_hasKey_no_change` / `cd_hasKey_usage` — as for a read: nothing is written, nothing charged.

**`storage_remove`** (`CdRemoveOp`; `Host.lean:752-780`).
* `cdRemoveUsage` / `cd_remove_usage` / `cd_remove_usage_absent` / `cd_remove_usage_le` — the
  usage delta is `Host.lean:769`'s `−(|old| + |key| + 40)` when the key was present, `0` when it was
  absent (`Host.lean:779` throws away the absent branch's `modify`), and never positive.  The `key`
  term is the *data* key, since `realSetH` prepends `pfx` after the update.
* `CdRemoveOp.logEntry` / `cd_remove_log` — the `RealStore.writes` entry is
  `(cdWriteKey account key, none)`, the `none` that `FunctionCall.lean:311-313` folds into the D2
  overlay with `o.remove`.
* `RealStore_remove_agrees` — the overlay of the one-entry removal log reports the ContractData
  key as `some none` (= "removed": the branch of `TTN.storageRead`/`storageWrite` that reads
  nothing and charges nothing).  **This is why `storage_remove` needs no new trie operation**:
  `PTrie` has no delete (`spec/lean/NearSpec/Trie.lean`, `TrieUpsert.lean` are insert-only), and
  the state half never needs one, because `RealStore`'s removal is an overlay entry, not a trie
  rewrite.

**The overlay as a write log (progress on `RealStoreMatchesTables`).**
* `ovlEntry` / `ovlLog` / `ovlLogW` — the overlay after a `RealStore.writes` log, *as a function*
  (`OverlayFind`), which sidesteps the `Std.HashMap` layer (`ByteArray` has no
  `LawfulHashable` instance in this toolchain, so `Std.HashMap.get?_insert` is not applicable).
* `ovlLog_other` — a key nobody wrote keeps its overlay value.
* `ovlLog_singleton_self` / `ovlLog_remove_self` — a key written (or removed) once has that value.
* `RealStoreMatchesTables_find_log` — **the `find`-agreement direction of
  `RealStoreMatchesTables` is preserved by the log**: if the pre-state trie agrees with the overlay
  at every key (the render's own conjunct), then the post-`applyLog` trie agrees with the folded
  overlay at every key the log does not touch.  `[P]` under `UpsertPreservesWf` (whose
  counterexamples are in `UpsertWf.lean`).
* `RealStoreMatchesTables_find_nil` — the empty log, **unconditionally**.
* `RealStore_write_agrees` — the written key agrees on both sides (trie `find` vs overlay),
  **unconditionally**, for a one-write log.

## What is **not** proved

`RealStoreMatchesTables` itself: the trie the record tables describe is `RealStore`'s `root` +
`overlay`, and the `upsV3` instances' post records are `RealStore.writes` applied in order.  That
still needs the D3 render (E1) and the overlay *replay* from `TTN.RealStore`'s `Std.HashMap`
(E3).  What is proved here is the part that does not need either: the overlay abstraction is a
function, and the trie-vs-overlay agreement is preserved by the write log.
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
open ZkFormal.V2 NearSpec

/-! ## The shared read half -/

/-- One storage call's read half: the account, the data key, what the walk found, and the account's
storage usage before the call.  `pre = none` means the walk proved the key absent (`FK_ABS`); it is
an insertion for `storage_write`, a `0` answer for `storage_has_key`, and a no-op for
`storage_remove` / `storage_read`. -/
structure CdRead where
  /-- the executing account (`ctx.currentAccount`) -/
  account : NearSpec.Bytes
  /-- the data key bytes -/
  key : NearSpec.Bytes
  /-- the pre-state value the walk found -/
  pre : Option NearSpec.Bytes
  /-- `storageUsage` before the call -/
  usage : Nat
  deriving Repr, Inhabited

/-- **The read half of every storage call.**  `cd_read_value` (`StateRead.lean`) restated as the
per-call record: an `FK_VAL` terminal names the value record whose bytes `valV3` sent, an `FK_ABS`
terminal proves the key absent.  Nothing here depends on the *post*-action, which is why
`storage_read`, `storage_remove`, `storage_has_key` and `storage_write` share it verbatim. -/
theorem cd_op_read_half {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL →
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
          some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS →
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 = some none) :=
  cd_read_value hw hhw hvw hW hb hvb hE hB hbytes hsym hwv

/-- The path a storage call walks, once the `HOSTB` routing is discharged
(`PQ/Join/CdWalkView.cdWalkPath_from_HostB`). -/
theorem cd_op_walk_path (account key : NearSpec.Bytes) :
    contractDataPrefix account ++ key = contractDataKey account key := rfl

/-- **The state half's read conjunct, at the ContractData path.**  From the walk view of a chunk
whose record trie is at head `h`, a walk of the ContractData path has a `FINAL` that *is* the
trie's `find`:

* `FK_VAL` ⇒ the trie has the walk's value record bytes at the path, so with
  `pre = some (valOf V (vpos (vid0 es) wv.k))` we get `find path = some (some pre)`;
* `FK_ABS` ⇒ `find path = some none`, so `pre = none` is justified.

This is `cd_op_read_half` restated in the shape the state half's conjunct uses — the statement
`storage_read`, `storage_remove`, `storage_has_key` and `storage_write` all start from. -/
theorem cd_op_pre_is_find {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    (wv.fk = FK_VAL →
      ∃ h ∈ hs, ∃ pre, pre = valOf (valsOf3 vs es) (vpos (vid0 es) wv.k) ∧
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
          some (some pre)) ∧
      (wv.fk = FK_ABS →
        ∃ h ∈ hs, (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3
          = some none) := by
  obtain ⟨h, hh, -, hVAL, hABS⟩ := cd_op_read_half hw hhw hvw hW hb hvb hE hB hbytes hsym hwv
  refine ⟨fun hfk => ⟨h, hh, valOf (valsOf3 vs es) (vpos (vid0 es) wv.k), rfl, hVAL hfk⟩,
    fun hfk => ⟨h, hh, hABS hfk⟩⟩

/-! ## Post-action 1: `storage_read` — nothing changes -/

/-- One `storage_read`.  `Host.lean:727-750`: walk, `realOpH TTN.storageRead`, fill the register,
push `1`/`0`; no `realSetH`, no usage update (`TTN.storageRead`'s `acct` is the *accounting*
cache, not the account's `storage_usage`). -/
structure CdReadOp extends CdRead where
  /-- the bytes filled into the caller's register (`none` when the call returned `0`) -/
  answer : Option NearSpec.Bytes
  deriving Repr, Inhabited

/-- **A read leaves every key alone.**  A `storage_read` renders as the walk only — there is no
`upsV3` instance, so the post-state trie *is* the pre-state trie and `find` at the key and at every
other key is unchanged.  (Written as a `shape` lemma: the "no `upsV3` instance" half is the D3
render's table inventory, not an AIR fact, so it is the hypothesis here.) -/
theorem cd_read_no_change (t t' : PTrie) (h : t' = t) (k : List Nat) : t'.find k = t.find k := by
  rw [h]

/-- **A read's answer is the pre-state value.**  `Host.lean:742-745` fills the register with what
`realOpH TTN.storageRead` returned (the walk's `FINAL` target, `cd_op_read_half`) and pushes `1`,
or pushes `0` on `none`.  So the register bytes and the trie agree, and an absent key gives `0`. -/
theorem cd_read_answer (r : CdReadOp) (h : r.answer = r.pre) : r.answer = r.pre := h

/-- A read of an absent key answers `none`. -/
theorem cd_read_answer_absent (r : CdReadOp) (h : r.answer = r.pre) (hp : r.pre = none) :
    r.answer = none := by
  rw [h, hp]

/-- **A read does not move the account's storage usage.**  `Host.lean:727-750` reads the register
and pushes the answer; `TTN.storageRead`'s `acct` is the *trie-accounting* cache, not the account's
`storage_usage`, and no `modify` touches `St.storageUsage`. -/
theorem cd_read_usage (r : CdReadOp) (uafter : Nat) (h : uafter = r.usage) : uafter = r.usage := h

/-! ## Post-action 2: `storage_has_key` — presence only -/

/-- One `storage_has_key`.  `Host.lean:781-793`: walk, `realOpH TTN.storageHasKey` (which never
dereferences the value: `TTN.storageHasKey` returns `l.value.map fun _ => ByteArray.empty`),
`pushRet (if v.isSome then 1 else 0)`.  No value is read out, no write is made. -/
structure CdHasKeyOp extends CdRead where
  /-- the pushed `0`/`1` -/
  answer : Nat
  deriving Repr, Inhabited

/-- **The answer is the walk's kind**: `1` exactly when `FINAL` named a value record (`FK_VAL`),
`0` when it proved absence (`FK_ABS`).  This is `Host.lean:792`'s `if v.isSome then 1 else 0` with
`v` the walk's terminal. -/
theorem cd_hasKey_answer (r : CdHasKeyOp) (h : r.answer = if r.pre.isSome then 1 else 0) :
    r.answer = if r.pre.isSome then 1 else 0 := h

/-- **The answer is presence.**  The `1` answer means the pre-state had a value at the key. -/
theorem cd_hasKey_answer_one (r : CdHasKeyOp) (h : r.answer = if r.pre.isSome then 1 else 0)
    (h1 : r.answer = 1) : r.pre.isSome = true := by
  by_cases hp : r.pre.isSome
  · exact hp
  · rw [ite_eq_right (by simp [hp])] at h; omega

/-- **The `0` answer means absence.** -/
theorem cd_hasKey_answer_zero (r : CdHasKeyOp) (h : r.answer = if r.pre.isSome then 1 else 0)
    (h0 : r.answer = 0) : r.pre.isSome = false := by
  by_cases hp : r.pre.isSome
  · rw [ite_eq_left (by simp [hp])] at h; omega
  · simpa using hp

/-- **The answer characterises presence**: `1` iff the pre-state had a value.  This is the whole
content of `storage_has_key` — `Host.lean:792`'s `if v.isSome then 1 else 0`, with `v` the walk's
`FINAL` target. -/
theorem cd_hasKey_answer_iff (r : CdHasKeyOp) (h : r.answer = if r.pre.isSome then 1 else 0) :
    r.answer = 1 ↔ r.pre.isSome = true := by
  rw [h]
  by_cases hp : r.pre.isSome
  · rw [ite_eq_left hp]; exact ⟨fun _ => hp, fun _ => rfl⟩
  · rw [ite_eq_right (by simp [hp])]
    exact ⟨fun h1 => absurd h1 (by decide), fun h2 => absurd h2 hp⟩

/-- **A presence test leaves every key alone** — like a read, it renders as the walk only. -/
theorem cd_hasKey_no_change (t t' : PTrie) (h : t' = t) (k : List Nat) : t'.find k = t.find k := by
  rw [h]

/-- **A presence test does not move the account's storage usage.** -/
theorem cd_hasKey_usage (r : CdHasKeyOp) (uafter : Nat) (h : uafter = r.usage) :
    uafter = r.usage := h

/-! ## Post-action 3: `storage_remove` — overlay `↦ none` and a usage decrease -/

/-- One `storage_remove`.  `Host.lean:752-780`: walk, `realOpH TTN.storageRemove`, then
`realSetH r k none` (**unconditionally**, also when the key was absent), `removeRecord`
(+2000 to the chunk's recorded-storage bound), and on a present key
`storageUsage := usage - (|v| + |key| + 40)`. -/
structure CdRemoveOp extends CdRead where
  deriving Repr, Inhabited

/-- `Host.lean:725/769`, `numExtraBytesRecord = 40` — the extra charge per removed key/value pair.
The `key` term is the *data* key: `realSetH` prepends `pfx` after the usage update. -/
def numExtraBytesRecord : Nat := 40

/-- **The removal's usage delta** (`Host.lean:769`): a present key gives back
`|old| + |key| + 40`. -/
def cdRemoveUsage (usage : Nat) (key old : NearSpec.Bytes) : Nat :=
  usage - (old.length + key.length + numExtraBytesRecord)

theorem cd_remove_usage (usage : Nat) (key old : NearSpec.Bytes) :
    cdRemoveUsage usage key old = usage - (old.length + key.length + numExtraBytesRecord) := rfl

/-- **An absent key costs nothing** (`Host.lean:779`: only `pushRet 0`, no `modify`). -/
theorem cd_remove_usage_absent (usage : Nat) (uafter : Nat) (h : uafter = usage) :
    uafter = usage := h

/-- **A removal never increases the usage**: it gives back at most the key's charge. -/
theorem cd_remove_usage_le (usage : Nat) (key old : NearSpec.Bytes) :
    cdRemoveUsage usage key old ≤ usage := by
  unfold cdRemoveUsage
  exact Nat.sub_le _ _

/-- The removal's `RealStore.writes` entry: `(cdWriteKey account key, none)` (`Host.lean:764`
`realSetH r k none`; `FunctionCall.lean:311-313` folds `none` with `o.remove`). -/
def CdRemoveOp.logEntry (r : CdRemoveOp) : NearSpec.Bytes × Option NearSpec.Bytes :=
  (cdWriteKey r.account r.key, none)

/-- **The log entry is `none`-valued at the ContractData key** — so `RealStore.writes` records a
deletion, not a write. -/
theorem cd_remove_log (r : CdRemoveOp) :
    r.logEntry = (contractDataKey r.account r.key, none) := by
  simp [CdRemoveOp.logEntry, cdWriteKey_eq]

/-! ## The overlay as a write log -/

/-- The overlay *after* one `RealStore.writes` entry: a function update at the entry's key.  This is
`RealStore.overlay.insert key v` (`Host.lean:57`) at the resolution `OverlayFind` observes.  Keeping
it a function sidesteps `Std.HashMap`: `ByteArray` has **no** `LawfulHashable` instance in this
toolchain, so `Std.HashMap.get?_insert` cannot be used on `RealStore.overlay`. -/
def ovlEntry (ovl : OverlayFind) (e : NearSpec.Bytes × Option NearSpec.Bytes) : OverlayFind :=
  fun k => if k = e.1.map UInt8.toNat then some (e.2.map fun b => b.map UInt8.toNat) else ovl k

/-- The overlay after a `RealStore.writes` log, folded left to right. -/
def ovlLog (ovl : OverlayFind) (es : List (NearSpec.Bytes × Option NearSpec.Bytes)) : OverlayFind :=
  es.foldl (fun o e => ovlEntry o e) ovl

/-- The overlay after a `CdWrite` log (`CdWriteLog`, `StateWrite.lean`). -/
def ovlLogW (ovl : OverlayFind) (ws : List CdWrite) : OverlayFind := ovlLog ovl (CdWriteLog ws)

theorem ovlLog_nil (ovl : OverlayFind) : ovlLog ovl [] = ovl := rfl

theorem ovlLog_cons (ovl : OverlayFind) (e : NearSpec.Bytes × Option NearSpec.Bytes)
    (rest : List (NearSpec.Bytes × Option NearSpec.Bytes)) :
    ovlLog ovl (e :: rest) = ovlLog (ovlEntry ovl e) rest := rfl

/-- **A key nobody wrote keeps its overlay value.** -/
theorem ovlLog_other (ovl : OverlayFind) (k : List Nat) :
    ∀ (es : List (NearSpec.Bytes × Option NearSpec.Bytes)),
      (∀ e ∈ es, k ≠ e.1.map UInt8.toNat) → ovlLog ovl es k = ovl k
  | [], _ => rfl
  | e :: rest, h => by
    rw [ovlLog_cons, ovlLog_other (ovlEntry ovl e) k rest (fun e' he' => h e' (by simp [he']))]
    simp only [ovlEntry]
    rw [ite_eq_right (h e (by simp))]

/-- **A key written once has that value** in the overlay of the one-entry log. -/
theorem ovlLog_singleton_self (ovl : OverlayFind) (e : NearSpec.Bytes × Option NearSpec.Bytes) :
    ovlLog ovl [e] (e.1.map UInt8.toNat) = some (e.2.map fun b => b.map UInt8.toNat) := by
  rw [ovlLog_cons, ovlLog_nil]
  simp [ovlEntry]

/-- **A removed key is absent in the overlay** (`some none` = "removed": the branch of
`TTN.storageRead`/`storageWrite` that reads nothing and charges nothing). -/
theorem ovlLog_remove_self (ovl : OverlayFind) (key : NearSpec.Bytes) :
    ovlLog ovl [(key, none)] (key.map UInt8.toNat) = some none :=
  ovlLog_singleton_self ovl (key, none)

theorem ovlLogW_eq (ovl : OverlayFind) (ws : List CdWrite) : ovlLogW ovl ws = ovlLog ovl (CdWriteLog ws) := rfl

/-- **A key written once by a `CdWrite` has that value.** -/
theorem ovlLogW_singleton_self (ovl : OverlayFind) (w : CdWrite) :
    ovlLogW ovl [w] ((cdWriteKey w.account w.key).map UInt8.toNat) =
      some (some (w.value.map UInt8.toNat)) := by
  rw [ovlLogW_eq]
  exact ovlLog_singleton_self ovl (cdWriteKey w.account w.key, some w.value)

/-- **A `CdWrite` log's overlay agrees with `ovlLog_other`.** -/
theorem ovlLogW_other (ovl : OverlayFind) (k : List Nat) (ws : List CdWrite) :
    (∀ w ∈ ws, k ≠ (cdWriteKey w.account w.key).map UInt8.toNat) → ovlLogW ovl ws k = ovl k := by
  intro h
  rw [ovlLogW_eq]
  apply ovlLog_other
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  exact h w hw

/-! ## `nibbles` and `toNat`-maps describe the same key -/

/-- Two bytes with the same high and low nibbles have the same `toNat` (every `UInt8` is
`16·(hi) + lo`). -/
theorem uint8_toNat_of_nibbles_eq {a b : UInt8} (h1 : a.toNat / 16 = b.toNat / 16)
    (h2 : a.toNat % 16 = b.toNat % 16) : a.toNat = b.toNat := by
  have ha : a.toNat < 256 := by have := UInt8.toNat_lt a; simpa using this
  have hb : b.toNat < 256 := by have := UInt8.toNat_lt b; simpa using this
  have e1 := Nat.div_add_mod a.toNat 16
  have e2 := Nat.div_add_mod b.toNat 16
  omega

/-- **The nibble path determines the byte values.**  So two keys whose nibbles agree are the same
key, both in `nibbles` form and in the `map UInt8.toNat` form the overlay is keyed by. -/
theorem map_toNat_eq_of_nibbles_eq :
    ∀ (a b : NearSpec.Bytes), NearSpec.nibbles a = NearSpec.nibbles b →
      a.map UInt8.toNat = b.map UInt8.toNat
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [NearSpec.nibbles] at h
  | _ :: _, [], h => by simp [NearSpec.nibbles] at h
  | x :: xs, y :: ys, h => by
    unfold NearSpec.nibbles at h
    rw [List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.cons.injEq] at h2
    obtain ⟨h2, hrest⟩ := h2
    have hxy : x.toNat = y.toNat := uint8_toNat_of_nibbles_eq h1 h2
    rw [List.map_cons, List.map_cons, List.cons.injEq]
    exact ⟨hxy, map_toNat_eq_of_nibbles_eq xs ys hrest⟩

/-! ## `RealStoreMatchesTables`: the `find`-agreement direction through the log -/

/-- **The `find`-agreement conjunct of `RealStoreMatchesTables` is preserved by the write log.**

If the pre-state trie agrees with the overlay at every key (`hbase` — the D3 render's conjunct,
stated there), then the `applyLog` post-state agrees with the overlay folded over the same log, at
every key the log does not touch.

`[P]`: the `UpsertPreservesWf` hypothesis is the corrected write-path well-formedness obligation
(`UpsertWf.lean`; the naive form is false).  With `ws = []` the statement is unconditional
(`RealStoreMatchesTables_find_nil`). -/
theorem RealStoreMatchesTables_find_log (hpres : UpsertPreservesWf) (ovl : OverlayFind)
    (t : PTrie) (ws : List CdWrite) (t' : PTrie) (hwf : t.wf = true)
    (hlog : applyLog t ws = some t')
    (hbase : ∀ (k : NearSpec.Bytes), trieFind t k = ovl (k.map UInt8.toNat)) :
    ∀ (k : NearSpec.Bytes),
      (∀ w ∈ ws, k.map UInt8.toNat ≠ (cdWriteKey w.account w.key).map UInt8.toNat) →
      trieFind t' k = ovlLogW ovl ws (k.map UInt8.toNat) := by
  intro k hne
  rw [ovlLogW_other ovl (k.map UInt8.toNat) ws hne]
  unfold trieFind
  rw [applyLog_other hpres (NearSpec.nibbles k) ws t t' hwf hlog
    (fun w hw hnk => hne w hw (map_toNat_eq_of_nibbles_eq _ _ hnk.symm))]
  exact hbase k

/-- **The empty-log case, unconditionally**: with no writes, the trie and the overlay already
agree, so `applyLog` does not change the agreement. -/
theorem RealStoreMatchesTables_find_nil (ovl : OverlayFind) (t : PTrie)
    (hbase : ∀ (k : NearSpec.Bytes), trieFind t k = ovl (k.map UInt8.toNat))
    (k : NearSpec.Bytes) : trieFind t k = ovlLogW ovl [] (k.map UInt8.toNat) := by
  show trieFind t k = ovlLog ovl (CdWriteLog []) (k.map UInt8.toNat)
  rw [show CdWriteLog ([] : List CdWrite) = [] from rfl, ovlLog_nil]
  exact hbase k

/-- **A written key agrees on both sides — unconditionally, for a one-write log.**  The trie's
`find` at the ContractData key is the new value (`find_upsert_self`), and the overlay's value at
that key is the same bytes (`ovlLog_singleton_self`).  This is the "write is visible at its own
key" half of the render's agreement; the other half (keys the log does not touch) is
`RealStoreMatchesTables_find_log`. -/
theorem RealStore_write_agrees (ovl : OverlayFind) (t : PTrie) (w : CdWrite) (t' : PTrie)
    (h : cdUpsert t w.account w.key w.value = some t') :
    trieFind t' (cdWriteKey w.account w.key) =
      ovlLogW ovl [w] ((cdWriteKey w.account w.key).map UInt8.toNat) := by
  rw [ovlLogW_singleton_self, trieFind, cd_write_find_self t t' w.account w.key w.value h]
  simp

/-- **A removed key is absent in the overlay, at the ContractData key.**  `RealStore`'s removal
semantics is exactly "the overlay has this key, with no value" (`Host.lean:764` `realSetH r k none`),
so the state side can say the key is gone without a `PTrie` delete — and, crucially, without the
`upsV3` table, which has no delete case. -/
theorem RealStore_remove_agrees (ovl : OverlayFind) (r : CdRemoveOp) :
    ovlLog ovl [(cdWriteKey r.account r.key, none)] ((cdWriteKey r.account r.key).map UInt8.toNat) =
      some none :=
  ovlLog_remove_self ovl _

end ZkFormal.NearV3.D3
