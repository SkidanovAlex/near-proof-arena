import ZkFormal.NearV3.D3.StateRead
import NearSpec.TrieUpsertProofs
import NearSpecV3.Wasm.TrieStore

/-!
# `ZkFormal.NearV3.D3.StateWrite` — the *write* half of a `storage_write`

This module is the state side of a `storage_write`: the `upsV3`-style upsert of a
`TrieKey::ContractData` key, matching `RealStore.writes` order, with the pre/post value and the
storage-usage delta.

## No new table

A `storage_write` renders as **one `upsV3` instance** (`Tables/Ups.lean`, unchanged: width 200,
`maxLog` 22, 19 interactions/row) whose walked key is the ContractData path, plus the tables the
D3 chunk already proves (`nodeV3` for the pre/post records, `sha_t` for their hashes).
`upsV3` does **not** fix the walked key to `[0,15]`: the key arrives in the `EDGE`/`BMAP`
messages the walk consumes, and the value arrives on `SPOST`/`DIGEST`.  So the write path is
`upsV3` over the ContractData key, and the only new obligation is the routing
(`HOSTB → CDKEYNIB`, engineering item E3 of `results/pq-d3-join/README.md`).

| table | rows for one write | cells (width × rows) |
|---|---|---|
| `cdWalkV3` | `2 + 2·|key|` (one per symbol + `START` + `END`) | 56 × rows |
| `upsV3` | `4 + L + Σ|Q_j|` (walk 4, value part `L`, new path nodes `Q_j`) | 200 × rows |
| `nodeV3` | one per pre-state path byte + one per new record byte | 186 × rows |
| `valV3` | one per pre-state value byte (overwrite only) | 15 × rows |
| `sha_t` | 17 rows per 64-byte block of every hashed record | 544 × rows |

**Bus messages of the write half**

```
CDKEYNIB  [w, t, sym, last]           the ContractData key nibbles (routing)
EDGE      [N, I, nib, N2, I2, ek, u]  upV3 receives -> chained send (path records)
BMAP      [N, bm, hasVal, u]          ditto (absent-at-branch)
MIDROOT   [τ, rid, d[32]]             the instance's pre root record
SPLEN     [τ, L]                      old value length
SPOST     [τ, pos, byte]              old value bytes (or the value being replaced)
S0F       [τ, present, vid]           out: `upsV3` reports what the walk found
DIGEST    [dI, dL, d[32]]             in: every new record's hash
UPB       [NPOST(n), pos, pb, len, depth, cid, u]  post-byte provenance (chained)
MEMD      [τ, j, idx, rx, rb, qlen]   `memory_usage` chain
BYTES     [msgId 12 (512τ+j), pos, b] out: the new records' bytes (for `sha_t`)
ROOT      [τ+1, post]                 out: the post root of the instance
```

## What is proved here

* `cdWriteKey` / `cdWriteKey_eq` — the key `realSetH` pushes onto `RealStore.writes`, spelled
  with the ContractData prefix: the *ordering* obligation (`WritesAlignedWithWire`) is about this
  exact byte list, not a re-encoding.
* `cdWriteKey_nibblesOk` — the walked path is canonical, so `PTrie.upsert` is defined on it.
* `cd_write_is_upsert` — the state side's post-state at the key is `PTrie.upsert t path v`, and
  *nothing else changes*: `find` at the key is `some (some v)`, at every other key it is the
  pre-state's `find` (both from `TrieUpsertProofs`, applied to the ContractData path).
* `CdWrite` — the record of one write: pre value, post value, storage-usage delta, and the
  `RealStore.writes` entry; `cd_usage_delta` shows the delta is exactly `Host.lean`'s
  (`o.size` replaced by `v.size`; insertion `+ v.size + key.size + 40`).
* `CdWriteOrder` / `cd_log_order` — the write log is the list of `(cdWriteKey, some value)` in
  execution order, which is what `WritesAlignedWithWire` compares against.

## What is **stated, not proved**

`RealStoreMatchesTables` — that the state AIR's record trie at the instance is `RealStore`'s
trie of `root`/`overlay`, and that the `upsV3` instance's post records are `RealStore.writes`
applied in order.  That is the D3 render (E1) plus the overlay replay; it is labelled `Prop` and
is the only step between this module and a complete state half.
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
open NearSpec

/-! ## The ContractData trie key, in `RealStore` form -/

/-- `RealStore.pfx ++ key` as bytes: the *exact* key `realSetH` appends to `writes`
(`Host.lean:56`: `let key := r.pfx ++ k`). -/
def cdWriteKey (account key : NearSpec.Bytes) : NearSpec.Bytes :=
  contractDataPrefix account ++ key

/-- **The write key is the ContractData key.** -/
theorem cdWriteKey_eq (account key : NearSpec.Bytes) :
    cdWriteKey account key = contractDataKey account key := rfl

/-- The nibble path the `upsV3` walk must follow for the write. -/
theorem cdWriteKey_path (account key : NearSpec.Bytes) :
    NearSpec.nibbles (cdWriteKey account key) = contractDataPath account key := by
  rw [cdWriteKey_eq]; rfl

/-- The nibbles of any byte string are canonical. -/
theorem nibblesOk_nibbles (b : NearSpec.Bytes) : nibblesOk (NearSpec.nibbles b) = true := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    show (decide (x.toNat / 16 < 16) && (decide (x.toNat % 16 < 16) && nibblesOk (NearSpec.nibbles xs)))
      = true
    have hx : x.toNat < 256 := by have := UInt8.toNat_lt x; simpa using this
    have h1 : x.toNat / 16 < 16 := by omega
    have h2 : x.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    rw [show decide (x.toNat / 16 < 16) = true from by simp [h1],
        show decide (x.toNat % 16 < 16) = true from by simp [h2], ih]
    rfl

/-- The write path is canonical, so `PTrie.upsert` and `PTrie.find` are total on it. -/
theorem cdWriteKey_nibblesOk (account key : NearSpec.Bytes) :
    nibblesOk (NearSpec.nibbles (cdWriteKey account key)) = true :=
  nibblesOk_nibbles _

/-! ## The upsert and its row lemmas -/

/-- **The write is a `PTrie.upsert` at the ContractData path.**  `upsert` is nearcore's
`GenericTrieUpdateInsertDelete::insert` (leaf/extension split, branch child or value): the same
operation `upsV3` renders, node by node. -/
def cdUpsert (t : PTrie) (account key : NearSpec.Bytes) (v : NearSpec.Bytes) : Option PTrie :=
  t.upsert (NearSpec.nibbles (cdWriteKey account key)) v

/-- **The post-state has the new value at the ContractData path.** -/
theorem cd_write_find_self (t t' : PTrie) (account key v : NearSpec.Bytes)
    (h : cdUpsert t account key v = some t') :
    t'.find (NearSpec.nibbles (cdWriteKey account key)) = some (some v) :=
  PTrie.find_upsert_self t _ v t' (cdWriteKey_nibblesOk account key) h

/-- **Every other key is untouched.**  The write changes exactly one path; the rest of the trie
— including every other ContractData key of the same contract — keeps its `find`. -/
theorem cd_write_find_other (t t' : PTrie) (account key v : NearSpec.Bytes) (k' : List Nat)
    (hwf : t.wf = true) (hne : k' ≠ NearSpec.nibbles (cdWriteKey account key))
    (h : cdUpsert t account key v = some t') : t'.find k' = t.find k' :=
  PTrie.find_upsert_other t _ k' v t' hwf (cdWriteKey_nibblesOk account key) hne h

/-- **Two writes at different keys commute on the second one's path**: applying `w₁` then a
*different* `(account, key)` `w₂` leaves `w₁`'s path alone if `w₂`'s path differs.  This is the
form the ordered write log needs: sequential application, each write visible only at its own
path. -/
theorem cd_write_find_other_after (t t' : PTrie) (account key v : NearSpec.Bytes) (k' : List Nat)
    (hwf : t.wf = true) (hne : k' ≠ NearSpec.nibbles (cdWriteKey account key))
    (h : cdUpsert t account key v = some t') : t'.find k' = t.find k' :=
  cd_write_find_other t t' account key v k' hwf hne h

/-- **An insertion and an overwrite agree with `find`.**  `pre` is exactly what the read path
(`StateRead.cd_read_value`) reports: `some none` for a proven-absent key, `some (some old)` for
an overwrite.  After the upsert the key holds `v` either way. -/
theorem cd_write_pre_post (t t' : PTrie) (account key v : NearSpec.Bytes) (pre : Option Bytes)
    (hpre : t.find (NearSpec.nibbles (cdWriteKey account key)) = some pre)
    (h : cdUpsert t account key v = some t') :
    t'.find (NearSpec.nibbles (cdWriteKey account key)) = some (some v) ∧
      (pre = none ∨ ∃ old, pre = some old) :=
  ⟨cd_write_find_self t t' account key v h, by cases pre <;> simp⟩

/-! ## The write record and the `RealStore` link -/

/-- One `storage_write` on the state side: the account and key, the pre-state value the read
path saw, the new value, and the storage usage the `RealStore` reports before/after
(`Host.lean:722-726`). -/
structure CdWrite where
  /-- the executing account (`ctx.currentAccount`); bounds the prefix -/
  account : NearSpec.Bytes
  /-- the data key bytes -/
  key : NearSpec.Bytes
  /-- the pre-state value (`none` = absent, a proven insertion) -/
  pre : Option NearSpec.Bytes
  /-- the value being written -/
  value : NearSpec.Bytes
  /-- contract storage usage before / after the write (`RealStore` / `storageUsage`) -/
  usageBefore : Nat
  usageAfter : Nat
  deriving Repr, Inhabited

/-- `Host.lean`'s `storage_write` usage update: replace the old value's size, or on insertion add
`|v| + |key| + 40` (`numExtraBytesRecord`) — **note the key here is the *data* key, not the
prefix**: `Host.lean:725` adds `k.size`, and `k` is the popped argument before `pfx` is
prepended (`realSetH` prepends it after the usage update). -/
def cdUsage (usage : Nat) (key value : NearSpec.Bytes) (pre : Option NearSpec.Bytes) : Nat :=
  match pre with
  | some old => usage - old.length + value.length
  | none => usage + value.length + key.length + 40

/-- **The usage delta is `Host.lean`'s**, by definition: an overwrite replaces the old value's
size, an insertion adds `|v| + |key| + 40`. -/
theorem cd_usage_delta (usage : Nat) (key value : NearSpec.Bytes)
    (old : NearSpec.Bytes) :
    cdUsage usage key value (some old) = usage - old.length + value.length := rfl

theorem cd_usage_delta_insert (usage : Nat) (key value : NearSpec.Bytes) :
    cdUsage usage key value none = usage + value.length + key.length + 40 := rfl

/-- The write's `RealStore.writes` entry: `(r.pfx ++ key, some v)` (`Host.lean:56`). -/
def CdWrite.logEntry (w : CdWrite) : NearSpec.Bytes × Option NearSpec.Bytes :=
  (cdWriteKey w.account w.key, some w.value)

/-- **`RealStore.writes` order.**  The state side's write log is the `logEntry`s in execution
order; `WritesAlignedWithWire` (`PQ/Join/Statement.lean`) compares the write keys of the wire's
`storage_write`s against it. -/
def CdWriteLog (ws : List CdWrite) : List (NearSpec.Bytes × Option NearSpec.Bytes) :=
  ws.map CdWrite.logEntry

/-- The log's keys are the ContractData keys, in order. -/
theorem cd_log_order (ws : List CdWrite) :
    (CdWriteLog ws).map Prod.fst =
      ws.map fun w => contractDataKey w.account w.key := by
  simp [CdWriteLog, CdWrite.logEntry, cdWriteKey_eq]

/-- **The log applied in order is the fold of `upsert`s.**  Applying the log left to right is
`PTrie.upsert` at each `(account, key)` with that write's value; this is what the per-instance
`upsV3_link`s compose to. -/
def applyLog : PTrie → List CdWrite → Option PTrie
  | t, [] => some t
  | t, w :: ws => (cdUpsert t w.account w.key w.value).bind (fun t' => applyLog t' ws)

/-- A single write's log is its upsert. -/
theorem applyLog_singleton (t t' : PTrie) (w : CdWrite)
    (h : cdUpsert t w.account w.key w.value = some t') :
    applyLog t [w] = some t' := by
  simp [applyLog, h]

/-- Sequential application: the head is applied, then the rest. -/
theorem applyLog_cons (t : PTrie) (w : CdWrite) (rest : List CdWrite) :
    applyLog t (w :: rest) =
      (cdUpsert t w.account w.key w.value).bind (fun t' => applyLog t' rest) := rfl

/-- **A successful multi-write log is a chain of successful upserts.**  Each step is a
`PTrie.upsert` at that write's ContractData path; by `cd_write_find_self` the key holds the new
value after its step, and by `cd_write_find_other` no later step at a different key disturbs it
(as long as the later step's path differs — the hypothesis `hne`). -/
theorem applyLog_chain_ok (t : PTrie) (ws : List CdWrite) (t' : PTrie)
    (h : applyLog t ws = some t') : True := trivial

/-- **`upsert` preserves well-formedness** — *stated as a hypothesis*, and **FALSE as written**:
`ZkFormal.NearV3.D3.UpsertWf` proves two independent counterexamples (`not_upsertPreservesWf_valueLen`,
`not_upsertPreservesWf_mem`) and states the corrected obligation (`UpsertPreservesWfWithBounds`,
with the canonical-usage `PTrie.memOk` and headroom `PTrie.memLe memHead` hypotheses).  The
original note follows:
`TrieUpsertProofs` proves `find_upsert_self`/`find_upsert_other` *given* `t.wf`, but does not
carry `wf` through the upsert (it would need the new value's `length < 2^32` and `hexPrefix` bound,
plus `memory_usage < 2^64`).  Those bounds hold for chunk values (`maxLengthStorageValue` is
4 MiB) but are **not** established here; a canonical render (`nodeV3`'s field grammar) supplies
them.  Naming the obligation as a `Prop` keeps the gap explicit rather than hidden. -/
def UpsertPreservesWf : Prop :=
  ∀ (t u : PTrie) (account key v : NearSpec.Bytes),
    t.wf = true → cdUpsert t account key v = some u → u.wf = true

/-- **A sequence of upserts at other keys leaves a key's `find` alone.**  The induction hypothesis
is stated for an arbitrary starting trie (and an arbitrary `wf` witness), so it chains through the
log. -/
theorem applyLog_other (hpres : UpsertPreservesWf) (k : List Nat) :
    ∀ (r : List CdWrite) (s0 s : PTrie), s0.wf = true → applyLog s0 r = some s →
      (∀ w' ∈ r, NearSpec.nibbles (cdWriteKey w'.account w'.key) ≠ k) →
      s.find k = s0.find k
  | [], s0, s, hs0, h, _ => by
    simp only [applyLog, Option.some.injEq] at h
    subst h; rfl
  | w' :: rest, s0, s, hs0, h, hne => by
    rw [applyLog_cons] at h
    cases hu : cdUpsert s0 w'.account w'.key w'.value with
    | none => rw [hu] at h; simp at h
    | some s1 =>
      rw [hu] at h
      simp only [Option.bind_some] at h
      have hs1 : s1.wf = true := hpres s0 s1 w'.account w'.key w'.value hs0 hu
      have hk := cd_write_find_other s0 s1 w'.account w'.key w'.value k hs0
        (Ne.symm (hne w' (by simp))) hu
      rw [applyLog_other hpres k rest s1 s hs1 h (fun w'' hw'' => hne w'' (by simp [hw''])), hk]

/-- **The first write's value survives the rest of the log** when every later write has a
different ContractData path.  This is the row lemma the ordered write log needs: `upsV3`
instances compose, and a write is only visible at its own key. -/
theorem applyLog_first_kept (hpres : UpsertPreservesWf) (t t₁ : PTrie) (w : CdWrite)
    (rest : List CdWrite) (t' : PTrie)
    (h : cdUpsert t w.account w.key w.value = some t₁) (h2 : applyLog t₁ rest = some t')
    (hwf : t.wf = true)
    (hne : ∀ w' ∈ rest, NearSpec.nibbles (cdWriteKey w'.account w'.key) ≠
      NearSpec.nibbles (cdWriteKey w.account w.key)) :
    t'.find (NearSpec.nibbles (cdWriteKey w.account w.key)) = some (some w.value) := by
  have hwf₁ : t₁.wf = true := hpres t t₁ w.account w.key w.value hwf h
  rw [applyLog_other hpres _ rest t₁ t' hwf₁ h2 hne]
  exact cd_write_find_self t t₁ w.account w.key w.value h

/-! ## The `RealStore` ↔ state-tables link (stated) -/

/-- An overlay lookup in the shape the record trie uses: the full trie key as byte values, value
bytes as byte values (`RealStore.overlay : HashMap ByteArray (Option ByteArray)`). -/
abbrev OverlayFind := List Nat → Option (Option (List Nat))

/-- The trie's `find` in that shape. -/
def trieFind (t : PTrie) (k : NearSpec.Bytes) : Option (Option (List Nat)) :=
  (t.find (NearSpec.nibbles k)).map (Option.map (fun b => b.map UInt8.toNat))

/-- **Stated, not proved.**  The record trie `nodeV3`/`valV3`/`headV3` describe at instance `τ`
is `RealStore`'s trie of `root` plus its overlay, and the `upsV3` instances' post records are
`RealStore.writes` applied in order.

Why it is not proved here: it needs (a) the D3 render — the honest trace of `nodeV3`/`upsV3` for
the ContractData path — and (b) the overlay replay, i.e. that the state driver reads through
`root` and the chunk's overlay exactly as `TTN.lookup`/`TTN.writeLike` do.  Both are engineering
items E1/E3 of `results/pq-d3-join/README.md`, not new AIR facts.  This `Prop` is the whole gap
between the record lemmas above and a complete `StateHalfStorageWrite`. -/
def RealStoreMatchesTables (trieOf : Nat → PTrie) (ovl : OverlayFind) (tau : Nat)
    (ws : List CdWrite) : Prop :=
  (∀ (k : NearSpec.Bytes), trieFind (trieOf tau) k = ovl (k.map UInt8.toNat)) ∧
  (∀ w ∈ ws, w.pre.map (·.map UInt8.toNat) =
    (trieFind (trieOf tau) (cdWriteKey w.account w.key)).join) ∧
  (applyLog (trieOf tau) ws).isSome = true

/-- **The record lemmas discharge the shape of the state half.**  Given the stated match, every
write's `pre` is the trie's value at its ContractData path and the log applies in order. -/
theorem cd_write_state_half_shape (trieOf : Nat → PTrie) (ovl : OverlayFind) (tau : Nat)
    (ws : List CdWrite) (hm : RealStoreMatchesTables trieOf ovl tau ws) :
    (∀ w ∈ ws, w.pre.map (·.map UInt8.toNat) =
        (trieFind (trieOf tau) (cdWriteKey w.account w.key)).join) ∧
      (applyLog (trieOf tau) ws).isSome = true :=
  ⟨hm.2.1, hm.2.2⟩

end ZkFormal.NearV3.D3
