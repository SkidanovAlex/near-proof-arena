# pq-cd-storage: contract-data storage provable on the state side

Lane `lane/pq-cd-storage`, from `main` @ `8412a9c2a`. This is the state half of a
`storage_write` host call. It is genuinely new work: D1 is transfer-only
(`spec/lean/v3/NearSpecV3/TxD1.lean:97` rejects every action that is not `Transfer`;
`RuntimeD1.txKeys` walks only account and access-key paths; no `nearAirV3`/`nearAirV3D1` table
touches `TrieKey::ContractData`).

Labels: **[K]** kernel-checked in Lean, **[P]** proved with a *stated* prerequisite (a clearly
labelled `Prop`), **[S]** stated, not proved, **[M]** measured here.

## 0. The result in one paragraph

A `storage_write` renders on the state side as a **ContractData key walk + an `upsV3` upsert**,
with **no new table and no new constraint**. `cdWalkV3` is `walkV3` with the key-nibble bus
renamed (`CDKEYNIB = 76`), and this lane proves the rename is a *transport*: local legality,
the `walkV3` view and the walk link all carry over (`CdBus.lean`). `upsV3` is key-agnostic
(the walked key arrives in `EDGE`/`BMAP`, not as a fixed `[0,15]`), so the write is an ordinary
`upsV3` instance over the ContractData path. What is left is the **routing** (`HOSTB → CDKEYNIB`)
and the **D3 render**, both engineering items, not AIR facts. The read path is proved down to
"the trie value is the `valV3` `VBYTES` bytes"; the write path is `PTrie.upsert` with the
self/other/usage/ordering lemmas; the only gaps are three explicitly stated `Prop`s (§6).

## 1. Table shapes and bus messages

### 1.1 The key

`nearcore` (`core/primitives/src/trie_key.rs:452-560`, `col::CONTRACT_DATA = 9`,
`ACCOUNT_DATA_SEPARATOR = b',' = 0x2c`):

```
key_bytes = 0x09 ‖ account_id ‖ 0x2c ‖ data_key
```

`RealStore.pfx ++ key` (`spec/lean/v3/NearSpecV3/Wasm/TrieStore.lean`,
`Wasm/Host.lean:40,56`) is exactly that. `D3.StateWrite.cdWriteKey` spells it and
`cdWriteKey_eq` proves `cdWriteKey account key = contractDataKey account key` — so the write log
`WritesAlignedWithWire` compares against is the *exact* byte list `realSetH` pushes, not a
re-encoding.

### 1.2 Tables touched by one `storage_write`

| table | role | width | interactions/row | rows for one write |
|---|---|---:|---:|---|
| `cdWalkV3` | the ContractData path walk (read half) | 56 | 6 | `2 + 2·|key|` |
| `upsV3` | the post-state upsert (write half) | 200 | 19 | `4 + L + Σ|Q_j|` (4 walk rows, `L` value rows, one part per new record) |
| `nodeV3` | pre-state path records + new records | 186 | 21 | one per serialized byte |
| `valV3` | the pre-state value (overwrite only) | 15 | 9 | one per value byte |
| `sha_t` | hashing every record + the value | 544 | 17 | 17 per 64-byte block |

`cdWalkV3` = `renameBus B_KEYNIB B_CDKEYNIB WalkV3.table`: **same width (56), same constraints,
same `maxLog` (21)**. `cdWalkV3_no_dst` (kernel) checks `KEYNIB`'s rename target `76` is unused
by `walkV3`, and `cdWalkLocal` transfers local legality. `cdWalkView` then yields `WalkWf3 ws`
from any `HoldsP` at a `cdWalkV3` index.

### 1.3 Bus messages

```
CDKEYNIB  [w, t, sym, last]           the ContractData key nibbles, one per key symbol
                                      (walkV3's KEYNIB receive, renamed)
EDGE      [N, I, nib, N2, I2, ek, u]  chained provider: nodeV3/headV3 -> cdWalkV3 (step/absent-key)
BMAP      [N, bm, hasVal, u]          chained: nodeV3 -> cdWalkV3 (absent-at-branch)
FINAL     [w, τ, fk, k]               cdWalkV3 -> consumers; fk=0 VAL ⇒ k = value record id,
                                      fk=1 ABS ⇒ k = 0
VBYTES    [vid, pos, byte]            valV3 receives the pre-state value bytes
```

Write half (`upsV3`, unchanged buses):

```
MIDROOT   [τ, rid, d[32]]                         in: the instance's pre root record
SPLEN     [τ, L]                                  in: old value length
SPOST     [τ, pos, byte]                          in: old value bytes
S0F       [τ, present, vid]                       out: what the walk found
DIGEST    [dI, dL, d[32]]                         in: every new record's hash
UPB       [NPOST(n), pos, pb, len, depth, cid, u] chained: post-byte provenance
MEMD      [τ, j, idx, rx, rb, qlen]               memory_usage chain
BYTES     [msgId 12 (512τ+j), pos, b]             out: the new records' bytes (to sha_t)
ROOT      [τ+1, post]                             out: the post root
```

`cdKeynibMsgs wv` is the `CDKEYNIB` list (`[w, t, sym, last]`, `t = 0 … L-2`, `last = 1` on
`END`), and `cd_nib_symbols`/`cd_nib_is_path` prove its `sym`s are exactly
`contractDataPath account key ++ [END]`.

## 2. What compiles, and what was run

New modules (all in `ZkFormal`, imported from `zk-formal/ZkFormal.lean`, no `sorry`, no
`native_decide`, no `implemented_by`):

| file | content |
|---|---|
| `zk-formal/ZkFormal/NearV3/D3/CdBus.lean` | the rename transport: `renameOne`, `contrib_renamed`, `cdWalkLocal`, `cdWalkView`, `cdWalkViewOfHolds`, `cdWalkFind`, `keyStream`, `cd_key_stream`, `cdKeynibMsgs` |
| `zk-formal/ZkFormal/NearV3/D3/StateRead.lean` | the read path: `CdReadRow`, `cdReadRow_mode`/`_last_end`/`_start`, `cd_nib_is_path`, `cd_read_value`, `cd_read_value_bytes` |
| `zk-formal/ZkFormal/NearV3/D3/StateWrite.lean` | the write path: `cdWriteKey`, `cdWriteKey_eq`, `nibblesOk_nibbles`, `cdUpsert`, `cd_write_find_self`/`_other`/`_pre_post`, `CdWrite`, `cdUsage`, `cd_usage_delta(+_insert)`, `CdWriteLog`, `cd_log_order`, `applyLog`, `applyLog_other`, `applyLog_first_kept`, `UpsertPreservesWf`, `RealStoreMatchesTables` |
| `zk-formal/ZkFormal/PQ/CdStorage/Link.lean` | the link to `StateHalfStorageWrite`: `WalkKeyIsContractData`, `UpsV3AppliesLog`, `cd_walkPath_of_view`, `cd_walkFinal_val`/`_abs`, `cd_k_abs`, `cd_writes_of_log`, `cd_postRoot_of_ups`, `cd_state_half_of` |

Exact commands and key output:

```
$ cd zk-formal && HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy \
    lake build ZkFormal.NearV3.D3.CdBus ZkFormal.NearV3.D3.StateRead \
      ZkFormal.NearV3.D3.StateWrite ZkFormal.PQ.CdStorage.Link
Build completed successfully (714 jobs).

$ cd zk-formal && HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy lake build
✔ [3038/3038] Build ZkFormal
Build completed successfully (3038 jobs).

$ cd zk-formal && lake env lean /tmp/ax_check.lean      # the axiom footprint
'…cdWalkView'          depends on axioms: [propext, Classical.choice, Quot.sound]
'…cdWalkFind'          depends on axioms: [propext, Classical.choice, Quot.sound]
'…cd_key_stream'       depends on axioms: [propext, Quot.sound]
'…cd_read_value'       depends on axioms: [propext, Classical.choice, Quot.sound]
'…cd_write_find_self'  depends on axioms: [propext, Quot.sound]
'…cd_write_find_other' depends on axioms: [propext, Classical.choice, Quot.sound]
'…nibblesOk_nibbles'   depends on axioms: [propext, Quot.sound]
'…applyLog_first_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
'…cd_write_pre_post'   depends on axioms: [propext, Quot.sound]
'…cd_walkPath_of_view' depends on axioms: [propext]
'…cd_writes_of_log'    depends on axioms: [propext, Quot.sound]
'…cd_state_half_of'    depends on axioms: [propext]

$ make pin-check      # exit 0 (all pinned artifacts unchanged)
pin-check exit: 0
```

The Lean build reuses the compiled `.lake` artifacts of the `pq-native-hermetic` worktree
(copied in, not rebuilt; disk was at 93 %). `nearAirV3`, `nearAirV3D1`, the signed relations,
`challenges/`, `oracle/` and `Join/Statement.lean` are untouched.

## 3. The read path (deliverable 1)

`cd_read_value` is the lookup lemma: for a `cdWalkV3` walk of an instance whose record trie is the
chunk's pre-state trie, `FK_VAL` gives
`find path = some (some (valOf V (vpos (vid0 es) wv.k)))` and `FK_ABS` gives
`find path = some none`. It is `walk3_find'` (the already-proved `walkV3` walk link) applied to
the `cdWalkV3` view, which is what `CdBus.lean` makes possible. `cd_read_value_bytes` then shows
that this value is *literally* the byte list `valV3` receives on `VBYTES`, so the state side's
`HOSTR`/register fill and the trie value are the same bytes.

The `CDKEYNIB` traffic the state side must produce is `cdKeynibMsgs`, and `cd_nib_is_path` shows
its symbols are `contractDataPath account key ++ [END]` — the prefix path then the data key, and
nothing else.

## 4. The write path (deliverable 2)

`cdUpsert t account key v := t.upsert (nibbles (cdWriteKey account key)) v`. `PTrie.upsert` is
nearcore's `GenericTrieUpdateInsertDelete::insert` (leaf split, extension split, branch child or
value, exact `memory_usage`), which is node-for-node what `upsV3` renders.

* `cd_write_find_self` — the key holds `v` after the upsert.
* `cd_write_find_other` — every key whose path differs keeps its `find`, so a write is visible
  only at its own key.
* `cd_write_pre_post` — with the read path's `pre`, the post value is `v` for both an insertion
  and an overwrite; the new value never enters the walk.
* `cdUsage` / `cd_usage_delta` / `cd_usage_delta_insert` — the storage-usage delta is
  `Host.lean`'s: `usage - |old| + |v|` on an overwrite, `usage + |v| + |key| + 40` on an
  insertion (`numExtraBytesRecord = 40`; the `key` there is the *data* key, since `pfx` is
  prepended after the usage update).
* `CdWrite.logEntry` / `CdWriteLog` / `cd_log_order` — the write log is
  `(cdWriteKey account key, some v)` in execution order; `cd_log_order` shows its keys are the
  ContractData keys in that order, exactly what `WritesAlignedWithWire` compares.
* `applyLog` / `applyLog_other` / `applyLog_first_kept` — landed left to right, the log is a
  chain of `upsert`s; a key written first keeps its value through every later write at a
  *different* path (`[P]`, under `UpsertPreservesWf`, §6).

## 5. The `RealStore` link (deliverable 3)

`cdWriteKey` is `RealStore.pfx ++ key` and `cdWriteKey_eq` identifies it with the trie key. The
semantic link — that `RealStore.root`/`overlay` is the trie the records describe, and that the
`upsV3` instances' post records are `RealStore.writes` applied in order — is
`RealStoreMatchesTables` **[S]**. `PQ.CdStorage.cd_state_half_of` turns it plus the stated
`upsV3` obligation (`UpsV3AppliesLog`) into the four conjuncts of `StateHalfStorageWrite`'s
shape. No `RealStore` semantics are re-derived: the prefix, path-split and key-encoding facts
are proved (`cdWriteKey_path`, `cdWriteKey_nibblesOk`, `nibblesOk_nibbles`).

## 6. What remains unproved (explicit)

| # | item | label | why it is not proved here |
|---|---|---|---|
| 1 | `WalkKeyIsContractData` (`PQ/CdStorage/Link.lean`) | **[S]** | That the `CDKEYNIB` bytes are `[9]‖account‖[44]‖key` depends on the `HOSTB → CDKEYNIB` relay (E3). An AIR fact about the *routing*, not the walk. |
| 2 | `RealStoreMatchesTables` (`D3/StateWrite.lean`) | **[S]** | That the record trie is `RealStore`'s `root`+`overlay` needs the D3 render (E1) and the overlay replay. |
| 3 | `UpsV3AppliesLog` (`PQ/CdStorage/Link.lean`) | **[S]** | `UpsLink.upsV3_link` proves the post root equals `upsert` at `[0,15]`; the ContractData instance is the same proof against a different walked key, but needs the render to *instantiate*. |
| 4 | `UpsertPreservesWf` (`D3/StateWrite.lean`) | **[S]** | `TrieUpsertProofs` proves `find_upsert_self`/`_other` *given* `t.wf` but does not carry `wf` through the upsert. It is true for chunk values (the record grammar keeps lengths and hex-prefixes in range) and is supplied by any canonical render. |
| 5 | `ContractDataPathSpec`'s "stated" label in `ContractData.lean` | moot | It is already **proved** there (`contractDataPathSpec_holds`). |

Everything else in §2–§5 is proved, kernel-checked, with axioms `⊆ {propext, Classical.choice,
Quot.sound}`.

Also not attempted (other lanes / engineering):

* the `HOSTB` byte binding (Wasm memory ↔ state bytes), `HOSTR` gas binding — `pq-host-gas`,
  `pq-host-bytes`;
* the `HOSTQ/HOSTR/HOSTB` wire commitment and NV passthrough — `pq-nv-tape`;
* the `Joint → RelD3` composition (`Compose`) — the runCall fold.

## 7. The measurement (deliverable 4) [M]

Driver: `research/near-compression/native/pq-cd-storage/measure_state_half.py`. It runs the
clean-room D3 reference (`oracle/tools/spec_check_v3_d3.py`) on a real fixture, captures every
`storage_write` with its pre-state root, walks the ContractData path exactly as
`D3Store._lookup` does, applies the write with `Trie2.update`, and lays out the tables above.
Row→cell mapping uses the Lean widths (56/200/186/15/544). Verdict for every case is `accept`,
so the numbers are honest.

```
$ taskset -c 14-15,28-29 python3 research/near-compression/native/pq-cd-storage/measure_state_half.py \
    /data/illia/nearproof-deps/corpora/d3c10/d3/{00-h10011-s3,00-h10013-s3,00-h10014-s0,00-h10018-s2,00-h10020-s2}
# totals: {'walk_rows': 162, 'ups_rows': 2684, 'node_rows': 5546, 'val_rows': 13,
#          'sha_rows': 1700, 'cells': 2502423, 'inters': 196731}
```

| case | key B | nib | path nodes | pre ser B | old→new B | walk rows | ups rows | node rows | val rows | sha rows | cells | inters |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 00-h10011-s3 | 14 | 28 | 6 | 600 | 8→5 | 30 | 612 | 1200 | 8 | 357 | 541,608 | 43,029 |
| 00-h10013-s3 | 14 | 28 | 6 | 568 | 5→5 | 30 | 9 | 568 | 5 | 204 | 220,179 | 15,672 |
| 00-h10014-s0 | 14 | 28 | 5 | 508 | 0→8 | 30 | 612 | 1108 | 0 | 340 | 515,128 | 40,716 |
| 00-h10018-s2 | 20 | 40 | 5 | 604 | 0→5 | 42 | 711 | 1306 | 0 | 391 | 600,172 | 47,634 |
| 00-h10020-s2 | 14 | 28 | 5 | 636 | 0→8 | 30 | 740 | 1364 | 0 | 408 | 625,336 | 49,680 |

### 5.1 The cost of one `storage_write` state half

Median over the five: **541,608 cells and 43,029 interaction slots**. Against the D0a baseline
(1,262,608 committed cells and 76,428 interaction slots, `pq-state-port` README §1) that is
**42.9 % of the cells and 56.3 % of the interaction slots** — one storage write costs about as
much as the storage-free transfer fixture itself. `00-h10013-s3` is the floor (an overwrite whose
whole path is already revealed: 220,179 cells); `00-h10020-s2` (28-nibble insert, 636 pre-state
node bytes) is the typical case.

Where the cells go (median case):

| family | cells | share |
|---|---:|---:|
| `sha_t` (path + value hashing) | 194,208 | 35.9 % |
| `nodeV3` (pre + new records) | 223,200 | 41.2 % |
| `upsV3` (new records + value) | 122,400 | 22.6 % |
| `valV3` (pre value) | 120 | 0.02 % |
| `cdWalkV3` (the walk) | 1,680 | 0.3 % |

The walk itself is **1,680 cells — 0.3 %**. The cost is the path's bytes and their hashes, both
of which the ported tables already handle; the genuinely new content is the routing.

The emitted `cdWalkV3` traffic for the median case is 29 `CDKEYNIB`, 30 `EDGE`, 1 `FINAL`: one
nibble message per key symbol, one edge per step, one terminal.

### 5.2 Storage-usage deltas

| case | kind | usage delta (`Host.lean`) |
|---|---|---:|
| 00-h10011-s3 | overwrite | `-8 + 5 = -3` |
| 00-h10013-s3 | overwrite (same length) | `0` |
| 00-h10014-s0 | insert | `+8 + 1 + 40 = +49` |
| 00-h10018-s2 | insert | `+5 + 1 + 40 = +46` |
| 00-h10020-s2 | insert | `+8 + 1 + 40 = +49` |

The `key` term is the *data* key (1 byte in these fixtures): the `pfx` is prepended after the
usage update, exactly as `Host.lean:725` does.

### 5.3 Caveats

* Cells are per-table `width × rows` at natural heights, not a proved D3 trace. This is the
  honest shape of the state half; the *proof* of it is the render (E1).
* `upsV3` rows are counted as `4 + L + Σ|new record bytes|`; the A7 duplicate elision is not
  applied, so it is an upper bound.
* The `upsV3` interaction count assumes every part row fires all 19 interactions; the true count
  is lower (only the shared buses are gated).

## 8. Files

* `zk-formal/ZkFormal/NearV3/D3/CdBus.lean` — the bus-rename transport (read half's walk reuse).
* `zk-formal/ZkFormal/NearV3/D3/StateRead.lean` — the read path and its row/lookup lemmas.
* `zk-formal/ZkFormal/NearV3/D3/StateWrite.lean` — the `upsV3`-style write, usage delta, log.
* `zk-formal/ZkFormal/PQ/CdStorage/Link.lean` — the link to `StateHalfStorageWrite`'s shape.
* `zk-formal/ZkFormal.lean` — four import lines appended.
* `research/near-compression/native/pq-cd-storage/measure_state_half.py` — the measurement.
* `research/near-compression/results/pq-cd-storage/README.md` — this file.
* `research/near-compression/results/pq-cd-storage/logs/` — the measurement output.
