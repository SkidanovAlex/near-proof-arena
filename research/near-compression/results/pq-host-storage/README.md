# pq-host-storage: the 8 D3α storage host functions on the state side

Lane `lane/pq-host-storage2`, from `main` @ `639387b1a` (2026-10-20). This extends
`pq-cd-storage` (which did `storage_write` only) to the whole D3α storage family.

Labels: **[K]** kernel-checked in Lean, **[P]** proved with a *stated* prerequisite (a clearly
labelled `Prop`), **[S]** stated, not proved, **[O]** out of domain / out of reach (with the
reason).

## 0. The result in one paragraph

Of the eight functions, **four have a complete state half in Lean today** (`storage_write` from
`pq-cd-storage`, plus `storage_read`, `storage_has_key`, `storage_remove` added here), **one**
(`storage_usage`) is proved to be a pure projection of the `acctV3` record with no trie work at
all, and **three** (`storage_iter_prefix` / `_range` / `_next`) are **out of domain, with a
theorem**: under D3α they always abort (`Host.lean:795-801`), so no run of them can move storage
and no ordered table is needed *for D3α*.  The read half of every value-carrying call is
**literally one theorem** — the walk of `storage_read`/`storage_remove`/`storage_has_key` is the
walk of `storage_write`, byte for byte, so only the post-action differs.  `storage_remove`
needs **no trie delete**: `RealStore`'s removal is an overlay entry `↦ none`, and the overlay
abstracted as a function is what `RealStoreMatchesTables`'s `find`-agreement direction is proved
against here.

## 1. Per-function status

| function | state half | tables | new table? | status |
|---|---|---|---|---|
| `storage_write` | `upsV3` upsert at the ContractData path | `cdWalkV3` + `upsV3` + `nodeV3`/`valV3`/`sha_t` | no | **[K]** `StateWrite.lean` (previous lane) |
| `storage_read` | none (walk only) | `cdWalkV3` + `nodeV3`/`valV3` | no | **[K]** walk+answer+no-change+no-usage (`StateOps.lean`) |
| `storage_has_key` | none (walk only) | `cdWalkV3` | no | **[K]** answer = presence, iff proved (`cd_hasKey_answer_iff`) |
| `storage_remove` | overlay `↦ none`, `writes += (key, none)`, usage `−` | `cdWalkV3` (+ no `upsV3`) | no | **[K]** log entry, usage delta, overlay-absent; **[P]** the trie-vs-overlay agreement through the log |
| `storage_usage` | none — reads the `acctV3` record | `acctV3` | no | **[K]** bytes→`Nat` round trip, host body is a register read, key is not a ContractData key |
| `storage_iter_prefix` | — | — | **out of domain** | **[K]** `iter_prefix_aborts` (always aborts) |
| `storage_iter_range` | — | — | **out of domain** | **[K]** `iter_range_aborts` |
| `storage_iter_next` | — | — | **out of domain** | **[K]** `iter_next_aborts` |

### 1.1 What transfers from `StateWrite.lean`, precisely

`storage_write`'s state half is three layers. Only the first is shared, but it is the expensive one:

1. **The walk** (`StateRead.cd_read_value`, `CdBus.cdWalkFind`) — **transfers verbatim** to all
   three other value-carrying calls. A walk does not know what the caller does with the value; its
   `FINAL` row reports the pre-state. This is `StateOps.cd_op_read_half`, which *is*
   `cd_read_value` (same statement, same hypotheses; the module just names it as "the read half of
   any storage call").
2. **The `upsV3` upsert** (`StateWrite.cdUpsert`, `cd_write_find_self`/`_other`,
   `cd_usage_delta`, `applyLog*`) — **does not apply** to read/has_key (no write) and **must not**
   apply to remove (`upsV3` has no delete case; `PTrie` has no delete either — see §3).
3. **The `RealStore` link** (`cdWriteKey_eq`, `cdWriteKey_nibblesOk`, `RealStoreMatchesTables`) —
   `cdWriteKey_eq`/`_nibblesOk` transfer (the key is the same key); `RealStoreMatchesTables` is
   extended in §4.

So the realistic target — "`storage_read`/`remove`/`has_key` reusing the write path" — is met
exactly: the walk is reused verbatim, and the write half is *replaced* by per-op post-actions that
are each a few lines because `Host.lean` itself does almost nothing for them.

## 2. `storage_read` / `storage_has_key` (`StateOps.lean`)

`Host.lean:727-750` and `:781-793` are: walk, `realOpH TTN.storageRead` / `TTN.storageHasKey`,
fill a register (read) or push `0/1` (has_key), `observeH` (read only). No `realSetH`, no
`modify … storageUsage`. So on the state side the **post-state trie is the pre-state trie**:

* `cd_read_no_change`, `cd_hasKey_no_change` — `find` is unchanged at the key and everywhere else
  (the "no `upsV3` instance" half is the D3 render's table inventory, so it is the hypothesis).
* `cd_read_answer`, `cd_read_answer_absent` — the register bytes are the walk's `FINAL` target,
  which is the `valV3` `VBYTES` list (`cd_read_value_bytes`), so the answer and the trie agree by
  definition and an absent key answers `none`.
* `cd_hasKey_answer`, `cd_hasKey_answer_iff` — the pushed `0/1` **is** presence:
  `answer = 1 ↔ pre.isSome`. This is the one non-trivial content of `has_key` (the "presence test
  only" the brief asked about), and it is proved from `Host.lean:792`'s
  `if v.isSome then 1 else 0`.
* `cd_read_usage`, `cd_hasKey_usage` — usage unchanged. `TTN.storageRead`/`TTN.storageHasKey`
  return an updated **trie-accounting** `Acct` (the node cache, `TrieStore.lean:125`), which is a
  *different* object from the account's `storage_usage` (`Machine.lean`'s `St.storageUsage`); no
  host-body branch touches the latter except the write/remove ones.

## 3. `storage_remove` — and why it needs no trie delete

`Host.lean:752-780`: walk, `realOpH TTN.storageRemove`, then **unconditionally**
`realSetH r k none` (also when the key was absent), `removeRecord` (+2000 to the chunk's
recorded-storage bound), and on a present key `storageUsage := usage − (|v| + |key| + 40)`.

* `cdRemoveUsage`, `cd_remove_usage`, `cd_remove_usage_absent`, `cd_remove_usage_le` — the delta
  is `Host.lean:769`'s, is `0` for an absent key (`Host.lean:779` discards the `modify`), and is
  never positive. The `key` term is the **data** key: `realSetH` prepends `pfx` after the usage
  update.
* `CdRemoveOp.logEntry`, `cd_remove_log` — the `RealStore.writes` entry is
  `(cdWriteKey account key, none)`; `FunctionCall.lean:311-313` folds `none` with `o.remove` into
  the D2 overlay.
* `RealStore_remove_agrees` — the overlay after the one-entry removal log reports the
  ContractData key as `some none`, i.e. "removed". `TTN.storageRead`/`storageWrite`'s
  `overlay.get? key = some none` branch then reads nothing and charges nothing — exactly
  nearcore's post-removal behaviour.

**The key point.** `PTrie` is insert-only: `spec/lean/NearSpec/Trie.lean` and `TrieUpsert.lean`
have `upsert`/`find`/`get`/`set` and **no** delete, and `upsV3` has no delete case either. That is
not a gap in *this* lane: the state half never needs a delete, because the post-state the chunk
proof commits is `RealStore.root` **plus the overlay**, and `RealStore` represents a removal as an
overlay entry with no value. So `storage_remove`'s state half is the walk (shared), a `none` log
entry (proved), and a usage delta (proved). Rendering that as tables is the *same* `upsV3`
instance machinery with the value slot `↦ none` — i.e. a `removeV3` variant of `upsV3`, which is an
engineering item (E1-flavoured), not a new semantic obligation.

## 4. `storage_usage` — the acct table, not a `ContractData` value (`StateUsage.lean`)

`Host.lean:602` is `payBaseH C.base; pushRet (← get).storageUsage`; `Exec.lean:486` seeds the
register from the call context, and `D3/FunctionCall.lean:289` seeds that from `acct.usage`. On
the state side the account record is the `acctV3` value, so `storage_usage` is a **projection**:

* `usageBytes`, `usageBytes_eq_drop_take` — the field is bytes `64 … 71` of the 72-byte
  `AccountV1` value (`amount(16) ‖ locked(16) ‖ code_hash(32) ‖ storage_usage(8)`), and those are
  exactly the `acctV3` table's `gS`-gated `VBYTES (vid, 64+i, ·)` sends
  (`NearV3/Rcpt/Tables/Acct.lean:38`).
* `usage_lane_mem` — those lanes are among the messages `acctV3` emits, so the state side reads
  the value off the acct table's own traffic.
* `leNatN`, `leNN`, `leNatN_leNN`, `usageNat_encode`, `usage_encode_canonical` — the field is the
  little-endian number of those bytes and the **round trip holds**: for any `u < 2^64`, an account
  value ending in `leNN 8 u` reports `u`. This is what pins the register to the account's usage
  rather than to an arbitrary word.
* `hostCall_storage_usage` — the body, named; `storage_usage_reads_register` — it moves neither
  `real` (overlay/writes/roots), nor `storageUsage`, nor `trie`; it is one base charge and one
  register read/push. So: no walk, no `upsV3`, no `writes` entry, usage delta `0`.
* `storage_usage_not_contract_data` — the account key `[0] ‖ account`
  (`NearSpec.accountKeyPath`) is **not** a ContractData key `[9] ‖ account ‖ [44] ‖ …`: the second
  nibble is `0` vs `9`. So no `cdWalkV3` instance is needed for `storage_usage`. [K]

## 5. `storage_iter_prefix` / `_range` / `_next` — out of domain, proved

This is the honest answer to "is iteration in reach". In D3α it is not a *reach* question at all:

```
| "storage_iter_prefix" => some do let _ ← popArgs 2; hErr "Deprecated { method_name: … }"
| "storage_iter_range"  => some do let _ ← popArgs 4; hErr "Deprecated { method_name: … }"
| "storage_iter_next"   => some do let _ ← popArgs 3; hErr "Deprecated { method_name: … }"
```

(`Host.lean:795-801`). Each **always aborts** after popping its arguments, and `Exec.callHost`
turns a non-`"unmodeled"` abort into a Wasm `abort`. `StateIter.lean` proves it:

* `popArgs_ok` — `popArgs n` always returns `ok` (the vector it builds has `n` entries by
  construction, so the arity test's error branch is dead);
* `popArgs_preserves` — `popArgs` moves only `stack`: `real`, `storageUsage`, `registers`,
  `trie`, `actions` all survive, so a `storage_iter_*` call **cannot move storage**;
* `hostCall_iter_prefix/_range/_next` — the bodies, by `rfl`;
* `iter_prefix_aborts`, `iter_range_aborts`, `iter_next_aborts` — each aborts on **every** state,
  with only the stack moved.

**If the rung is later widened** to real iteration, the smallest sound slice is a *new table
family*, not a lemma:

```
prefix-only, single call, bounded result count N:
  srtV3 over the account's contract-data keys (sorted-key witness, rows (τ, j, key_j, key_{j+1})
  with a lexicographic `key_j < key_{j+1}` check, plus a PREFIX row block checking
  isPrefix(contractDataPrefixPath account, key_j) on every returned key), and
  one ORDER chain over the j's.
range and next are outside even that slice: `storage_iter_next(iterator_id, …)` returns
successive entries of one iterator, so it needs a cursor register file carried across calls plus
a NEXT chain — a third new table (or a cursor public record).
```

`cdWalkV3` cannot be reused for this: it follows *one* path decided by `CDKEYNIB`, while returning
the *next* key is a different operation (nearcore's `TrieIterator` descends and then backtracks
over siblings), so the `EDGE` provider would have to expose sibling order too. This is roughly the
weight of the whole `cdWalkV3` + `upsV3` state half, and it has no consumer in the current D3α
spec. Reported as **[O]** for this lane.

## 6. Progress on `RealStoreMatchesTables` (`StateOps.lean` §"overlay as a write log")

`RealStoreMatchesTables` (`StateWrite.lean`) is three conjuncts: (a) every key of the trie agrees
with the overlay, (b) each write's `pre` is the trie's value at its path, (c) the log applies.
What is proved now:

* **The overlay is a function.** `ovlEntry` / `ovlLog` / `ovlLogW` fold `RealStore.writes` into an
  `OverlayFind`. This deliberately sidesteps `Std.HashMap`: `ByteArray` has **no**
  `LawfulHashable` instance in this toolchain, so `Std.HashMap.get?_insert` is *not usable* on
  `RealStore.overlay` (`#synth LawfulHashable ByteArray` fails). Proving the HashMap layer itself
  is a separate prerequisite.
* `ovlLog_other` — a key nobody wrote keeps its overlay value; `ovlLog_singleton_self` /
  `ovlLog_remove_self` — a key written (removed) once has that value (absent).
* **`RealStoreMatchesTables_find_log`** — conjunct (a) is preserved by the log: from a pre-state
  agreement at every key, the `applyLog` post-state agrees with the folded overlay at every key the
  log does not touch. This is the *interaction* of `applyLog_other` (trie) with `ovlLog_other`
  (overlay), joined by `map_toNat_eq_of_nibbles_eq` (nibble path ⇒ same bytes ⇒ same overlay key).
  **[P]** under `UpsertPreservesWf`.
* **`RealStoreMatchesTables_find_nil`** — the empty log, **unconditionally**.
* **`RealStore_write_agrees`** — the written key agrees on both sides, **unconditionally**, for a
  one-write log (`find_upsert_self` vs `ovlLogW_singleton_self`). This is conjunct (a) *at the
  write*, which is the part the render used to have to do by hand.
* `RealStore_remove_agrees` — the removed key is `some none` in the overlay, unconditionally.

Still **not** proved, and why: (a)'s *base* case, i.e. that the record trie the `nodeV3`/`headV3`
tables describe at instance `τ` **is** `RealStore.root`+`overlay`. That needs the D3 render (E1)
plus the overlay replay from `TTN.RealStore`'s `Std.HashMap` (E3). [S]

## 7. What compiles, and what was run

New modules (all imported from `zk-formal/ZkFormal.lean`, **no** `sorry`, no `native_decide`, no
`implemented_by`):

| file | content |
|---|---|
| `zk-formal/ZkFormal/NearV3/D3/StateOps.lean` | read/remove/has_key: `cd_op_read_half`, `cd_op_pre_is_find`, `cd_op_walk_path`, `CdRead`/`CdReadOp`/`CdHasKeyOp`/`CdRemoveOp`, answer/usage/no-change lemmas, `map_toNat_eq_of_nibbles_eq`, the overlay log (`ovlEntry`/`ovlLog`/`ovlLogW`) and `RealStoreMatchesTables_find_log` / `_find_nil` / `RealStore_write_agrees` / `RealStore_remove_agrees` |
| `zk-formal/ZkFormal/NearV3/D3/StateUsage.lean` | `storage_usage`: `usageBytes`, `usage_lane_mem`, `leNatN`/`leNN` and the round trip, `hostCall_storage_usage`, `storage_usage_reads_register`, `storage_usage_not_contract_data` |
| `zk-formal/ZkFormal/NearV3/D3/StateIter.lean` | `storage_iter_*`: `popArgs_ok`/`_preserves`, the three abort theorems, and the design note for a real iterator |

Exact commands and key output:

```
$ HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy \
    sh -c 'cd zk-formal && lake build ZkFormal.NearV3.D3.StateOps \
      ZkFormal.NearV3.D3.StateUsage ZkFormal.NearV3.D3.StateIter'
Build completed successfully (701 jobs).

$ HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy \
    sh -c 'cd zk-formal && lake build'
✔ [3050/3050] Built ZkFormal
Build completed successfully (3050 jobs).

$ make pin-check
pin-check exit: 0

$ cd zk-formal && lake env lean /tmp/opencode/ax_check.lean    # the axiom footprint
'…cd_op_read_half'                     [propext, Classical.choice, Quot.sound]
'…cd_op_walk_path'                     (none)
'…cd_op_pre_is_find'                   [propext, Classical.choice, Quot.sound]
'…cd_hasKey_answer_one'                [propext, Quot.sound]
'…cd_read_no_change'                   (none)
'…ovlLog_other'                        [propext]
'…ovlLog_singleton_self'               [propext]
'…RealStoreMatchesTables_find_log'     [propext, Classical.choice, Quot.sound]
'…RealStoreMatchesTables_find_nil'     (none)
'…RealStore_write_agrees'              [propext, Quot.sound]
'…RealStore_remove_agrees'             [propext]
'…cd_remove_log'                       [propext]
'…map_toNat_eq_of_nibbles_eq'          [propext, Quot.sound]
'…usageBytes_eq_drop_take'             [propext, Quot.sound]
'…usage_lane_mem'                      [propext, Quot.sound]
'…usageNat_encode'                     [propext, Classical.choice, Quot.sound]
'…usage_encode_canonical'              [propext, Classical.choice, Quot.sound]
'…hostCall_storage_usage'              [propext, Classical.choice, Quot.sound]
'…storage_usage_reads_register'        [propext, Classical.choice, Quot.sound]
'…storage_usage_not_contract_data'     [propext, Quot.sound]
'…popArgs_ok'                          [propext, Classical.choice, Quot.sound]
'…popArgs_preserves'                   [propext, Classical.choice, Quot.sound]
'…hostCall_iter_prefix'                [propext, Classical.choice, Quot.sound]
'…iter_prefix_aborts'                  [propext, Classical.choice, Quot.sound]
'…iter_range_aborts'                   [propext, Classical.choice, Quot.sound]
'…iter_next_aborts'                    [propext, Classical.choice, Quot.sound]
```

`nearAirV3`, `nearAirV3D1`, `spec/`, the pinned artifacts, `challenges/` and `oracle/` are
untouched; `make pin-check` exits 0.

## 8. What the state side must supply (per function)

| function | walk rows | `upsV3` rows | other | routing |
|---|---|---|---|---|
| `storage_read` | `2 + 2·|key|` (`cdWalkV3`) | 0 | `nodeV3`/`valV3` as for `write` | `HOSTB → CDKEYNIB` |
| `storage_has_key` | same | 0 | `nodeV3` only (no value deref) | same |
| `storage_remove` | same | `removeV3` (a `upsV3` whose value slot is `none`) | `nodeV3` | same |
| `storage_usage` | 0 | 0 | `acctV3` (already in the chunk proof) | none |

The **state-side obligation is therefore uniform**: one `cdWalkV3` per call (already measured at
1,680 cells, 0.3 % of a write's state half — `pq-cd-storage/README.md` §5.1), and a post-action
that is either nothing (read/has_key), a `none` upsert (remove), or an `acctV3` projection
(usage). No function in the family needs a new bus, a new constraint or a new table — iteration
excluded, with the theorem that it is out of domain.

## 9. Files

* `zk-formal/ZkFormal/NearV3/D3/StateOps.lean` — read/remove/has_key + overlay-log progress.
* `zk-formal/ZkFormal/NearV3/D3/StateUsage.lean` — `storage_usage` via the acct record.
* `zk-formal/ZkFormal/NearV3/D3/StateIter.lean` — `storage_iter_*` out of domain + design note.
* `zk-formal/ZkFormal.lean` — three import lines appended.
* `research/near-compression/results/pq-host-storage/README.md` — this file.
