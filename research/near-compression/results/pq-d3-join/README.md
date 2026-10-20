# pq-d3-join: the joint Wasm × state statement and the state half of `storage_write`

Lane `lane/pq-d3-join`, from `lane/pq-state-port` @ `c69358866` (2026-10-19). This is the third
blocking gap of `docs/logs/pq-gap-analysis-2026-10-19.md`: a Wasm `FunctionCall` proof and a NEAR
state proof must compose, and the state half of contract storage is **new work**.

Labels: **[M]** measured here, **[K]** kernel-checked in Lean, **[S]** stated (a `Prop`, not
proved), **[E]** estimate.

**Scope.** Deliverables only: the statement, the `TrieKey::ContractData` prefix + walk/key-nibble
tables, the measurement of one `storage_write`, and the remaining checklist. The join itself
(15–25 agent-days, §6) is **not** attempted.

## 0. The correction this lane is built on

The D1 tables are **transfer-only**. `spec/lean/v3/NearSpecV3/TxD1.lean:97` rejects any action
that is not `Transfer(3)`; `RuntimeD1.txKeys` (`RuntimeD1.lean:214-215`) walks only
`accountKeyPath` and `keyAccessKey`; no table in `nearAirV3`/`nearAirV3D1` references
`TrieKey::ContractData`. The ported trie tables are key-agnostic, so they *can* walk a
ContractData path — but nothing routes a ContractData key into them, and no statement carries the
contract's storage. That routing is §3 below.

## 1. The joint statement [S]

### 1.1 Two proofs, not one AIR

| | Wasm side (`lane/pq-wasm-base`) | State side (this lane / `pq-state-port`) |
|---|---|---|
| relation | `Holds (wasmBaseAir …) pub tr` + HOST chip | `HoldsP nearAirV3D1 … pub tr` + the D3 `runCall` fold |
| public values | base statement: `N, S_final, nres, rtag, result, status, mem, dataEnd`, local tags, initial globals, `stackRem`, plus the cached commitments `code_root`, `func_root`, `data_root` | the D1 statement's 15 public segments + header PVs, plus the TAPE commitment |
| verified by | native SWIRL verifier, then V_d's `code_root` recomputation | native SWIRL verifier, then V_d's TAPE/header checks |
| today | F1+div+locals+memory+globals+calls; **no host call** (`check` rejects import calls) | D0a 25 tables prove; D1 23/30; **no ContractData** |

The join is a **statement over the two proofs' public values and one shared host wire**, exactly
as `pq-wasm-base` README §14.2 proposes. It is not a third AIR merged into either side.

### 1.2 Public values

The joint public values are the disjoint union of the two sides' public values, plus the three
wire commitments, plus four values that must be duplicated (and therefore bound to agree):

```
joint PVs =   wasm:  code_root, func_root, data_root,
                     N, S_final, nres, rtag, result[0..4], status,
                     mem, dataEnd, locals[nloc], globals[ngl], stackRem
            ∪ state: prev_state_root, post_state_root,
                     header PVs (350 bytes), TAPE root
            ∪ wire:  commit(HOSTQ), commit(HOSTR), commit(HOSTB)
            ∩ agree: prev_state_root, post_state_root, account_id, code_hash
```

* `code_hash` is **computed on the state side** from the executing account's contract
  (`TTN.RealStore` code lookup / the D2 account value) and is a public value on both proofs.
  The Wasm side binds it through `code_root` (`pq-wasm-base/STATEMENT.md` §2: V_d recomputes the
  cached commitment from the code, and `sha256(code) = code_hash` is checked natively).
* `prev_state_root` and `post_state_root` are the claim's `prev_state_root` and the main
  transition's `post_state_root`; the Wasm side must use `prev_state_root` as the trie root its
  host responses were produced against, and the state side publishes the post root after the
  writes. A successful receipt's writes must be in `post_state_root`; a failed receipt's must be
  rolled back (`FunctionCall.lean:322-329`, `Ovl.rollback`).
* `account_id` is the executing account (`ctx.currentAccount` in `FunctionCall.lean:264,297`);
  it is what makes the `ContractData` prefix `[9] ‖ account ‖ [44]` unambiguous.
* The wire commitments are **cached-commitment** statement components exactly like
  `code_root`: V_d (or the aggregation layer) recomputes them from the host traffic it is given,
  so the prover cannot open a different wire. This is the M2 pattern of the envelope study
  (`pq-d1-envelope` §3), reused.

The Lean `Prop` is `ZkFormal.PQ.Join.Joint` (`zk-formal/ZkFormal/PQ/Join/Statement.lean`):

```lean
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
```

`Joint`, `CodeBound`, `StateHalfStorageWrite`, `WritesAlignedWithWire`, `JointBusBalance` and
`Compose` are all **stated**, not proved. The two side relations (`wasmHolds`, `stateHolds`) are
parameters, because each side's theorem lives in its own lane.

### 1.3 The host wire

```
HOSTQ [ts, host_id, S, a0, a1, a2, a3, a4]           (Wasm → state, one per call)
HOSTR [ts, status, r_lo, r_hi, g_lo, g_hi, 0, 0]     (state → Wasm, one per call)
HOSTB [ts, dir, pos, byte]                           (both directions, one per byte)
```

* `ts` is the Wasm row clock (`WasmBase/Chips.lean` `cTs`); it strictly increases along `HOSTQ`,
  which is what lets the state side process the requests as a sequence and keep the trie overlay
  in order (`Wire.tsIncreasing`).
* `S` is the instruction-gas count so far; the state side reproduces `sync` by
  `burnt += R · (S − S_prev)` and returns the resynchronised budget `g` as `HOSTR.g`.
* `status ∈ {0 ok, 1 host error, 2 gas exhausted}`; `r` is the result word (two 16-bit limbs).
* `HOSTB` is the same shape as D1's `VBYTES (vid, pos, byte)`, so the state side consumes key and
  value bytes exactly as it consumes trie value bytes today. `dir = 0` is Wasm → state (a
  `storage_write`'s key/value), `dir = 1` is state → Wasm (a `storage_read` register fill, the
  `input`, a context string).
* `storage_write(key_len, key_ptr, val_len, val_ptr, reg)` is one `HOSTQ` with
  `host_id = 0`, `args = [key_len, val_len, reg]` and the bytes on `HOSTB` at the same `ts`.

**Bus ids.** The join uses `HOSTQ = 208`, `HOSTR = 209`, `HOSTB = 210` — above the state export's
`BUS_OFFSET = 128` shift (`128 + 76 = 204`) and above the Wasm base family's `0 … 6`. This is
kernel-checked (`host_bus_safe`) and is the only new global bus numbering in the lane. [K]

### 1.4 Cross-proof bus balance

`HostTrafficAgrees` says the Wasm proof's `HOSTQ/HOSTR/HOSTB` projections equal the state proof's.
Because both project the same ordered wire, this is an equality of projections; the aggregation
checks it as a multiset equality per `(bus, message)`, just like a segment boundary. Over the
state side's own buses, the balance is `HoldsP.balance` (proved for the D0a port, `Bridge`); over
the Wasm side's own buses it is `Holds.balance` (the base AIR's theorem). The *only* new balance
obligation is `HOSTQ/HOSTR/HOSTB` across the two proofs (`JointBusBalance`). [S]

### 1.5 What a `storage_write` adds on the state side

The state half of one `storage_write` is `StateHalfStorageWrite`: a ContractData walk of
`[9] ‖ account ‖ [44] ‖ key` over the **pre-state** trie, a terminal that describes the pre-state
(`FK_ABS` for an insertion, `FK_VAL` into a value record equal to the old bytes for an overwrite),
the write appearing in the ordered `RealStore.writes` log, and (when committed) the post root
being the `upsV3` upsert of the pre-state by the log. The new value never enters the walk; it
enters only through `upsV3`. §4 measures it.

## 2. What compiles

New Lean modules (both in `ZkFormal`, built by `lake build`, no `sorry`, standard axioms only):

* `zk-formal/ZkFormal/NearV3/D3/ContractData.lean` — key prefix, path, bus `B_CDKEYNIB = 76`,
  `cdWalkV3` (`walkV3` with the key bus renamed), `cdKibV3` (public-record relay), the prefix
  facts, and the path lemmas.
* `zk-formal/ZkFormal/PQ/Join/Statement.lean` — the joint statement, host message shapes, bus
  ids, `StateHalfStorageWrite`, `JointBusBalance`, `Joint`, and the named obligations
  `WasmHalf`/`StateHalf`/`Compose`.

Both are imported from `zk-formal/ZkFormal.lean`, so `lake build` (and CI's Lean target)
compiles them. Measured:

```
$ cd zk-formal && lake build ZkFormal.NearV3.D3.ContractData ZkFormal.PQ.Join.Statement
✔ [70/71] Built ZkFormal.NearV3.D3.ContractData (247ms)
✔ [71/71] Built ZkFormal.PQ.Join.Statement (301ms)
Build completed successfully (71 jobs).

$ lake build          # whole library, 1021 jobs
Build completed successfully (1021 jobs).

$ # `ax_check.lean` (imports the two modules, prints the axiom footprint)
$ cd zk-formal && lake env lean ../research/near-compression/native/pq-d3-join/ax_check.lean
#print axioms
ZkFormal.NearV3.D3.nibbles_append          : [propext]
ZkFormal.NearV3.D3.nibbles_length          : [propext, Quot.sound]
ZkFormal.NearV3.D3.contractDataPath_length : [propext, Quot.sound]
ZkFormal.NearV3.D3.contractDataPathSpec_holds : [propext, Quot.sound]
ZkFormal.PQ.Join.host_bus_safe             : []            -- decide +kernel
```

No `sorry` inside anything presented as a theorem. The `Prop`s of §1 are labelled **[S]** and
are definitions of obligation, not theorems.

`make pin-check`: **passes** (`taskset` not needed; ~1 s).

### Reused deps

The Lean build needs the `pq-state-port` worktree's `.lake` artifacts. They were **copied** into
this worktree's four projects (`formal-core`, `spec/lean`, `spec/lean/v3`, `zk-formal`), not
re-built (disk: 54 GB free). Nothing in `nearAirV3`, `nearAirV3D1`, the signed relations,
challenges, pinned files or `oracle/` was modified.

## 3. The `ContractData` prefix result [K]

### 3.1 The encoding

`nearcore` (`core/primitives/src/trie_key.rs:452-560`, `col::CONTRACT_DATA = 9`,
`ACCOUNT_DATA_SEPARATOR = b',' = 0x2c`):

```
key_bytes = 0x09 ‖ account_id ‖ 0x2c ‖ data_key
```

This is exactly `NearSpecV3.Wasm.TTN.contractDataPrefix`
(`spec/lean/v3/NearSpecV3/Wasm/TrieStore.lean:172`), and `TrieStore.RealStore.pfx` holds it. The
host functions build the full trie key as `r.pfx ++ k` (`Wasm/Host.lean:40,56`; `realSetH`), so the
state side must walk `pfx ++ data_key`, **not** the account key.

Concrete example (`account = "s0rc"`, `key = "a"`):

| form | bytes | nibbles |
|---|---|---|
| prefix | `09 73 30 72 63 2c` | `0,9, 7,3, 3,0, 7,2, 6,3, 2,12` |
| full key | `09 73 30 72 63 2c 61` | `0,9, 7,3, 3,0, 7,2, 6,3, 2,12, 6,1` |

`contractDataPrefix ""` is `[9, 44]` (the empty account is not a valid account id, but the
function is total).

### 3.2 What was added

`zk-formal/ZkFormal/NearV3/D3/ContractData.lean`:

* `colContractData = 9`, `accountDataSeparator = 44`, `contractDataKey`, `contractDataPath`,
  `contractDataPrefix`, `contractDataPrefixPath`.
* `ContractDataPathSpec`: path = prefix path ++ key nibbles, and length = `2·|key_bytes|` **[S]**
  with the conjunction **proved** (`contractDataPathSpec_holds`).
* `B_CDKEYNIB = 76` — unused by `nearAirV3` (max 75), the D1 tables (`67 … 71`) and the
  `pq-state-port` export (`BUS_OFFSET = 128`).
* `cdWalkV3 := renameBus B_KEYNIB B_CDKEYNIB WalkV3.table`. It is the **same table**: same width
  (56), same constraints, same `maxLog` (22). Only the key-nibble producer changes. So every
  `walkV3` soundness/render lemma applies verbatim; the new content is the routing.
* `cdKibV3` — a `kibV3`-shaped relay `CDPKEY (w0,w1,w2,τ,sym,last) ↦ CDKEYNIB (w,τ,sym,last)`
  with `B_CDPKEY = 77`, for the case where the key is supplied as a public record. `77` is just
  outside `nearBuses = 77`, so using this relay in the state AIR needs `numBuses ≥ 78`; `cdWalkV3`
  alone does not. For the D3 statement the normal route is `HOSTB` (the bytes are already in the
  Wasm trace), and the relay is only needed for a witness whose key is in the public tape.

Kernel-checked facts (all `decide +kernel`, no `sorry`):

```
contractDataKey [s0rc] [a]        = [9,115,48,114,99,44,97]
nibbles [9,115]                   = [0,9,7,3]
nibbles [44,97]                   = [2,12,6,1]
contractDataPrefixPath [s0rc]     = [0,9,7,3,3,0,7,2,6,3,2,12]
contractDataPath [s0rc] [a]       = [0,9,7,3,3,0,7,2,6,3,2,12,6,1]
(cdWalkV3 interacts on CDKEYNIB)  = 1,  (… on KEYNIB) = 0
B_CDKEYNIB < 77
```

**What is still needed for a real ContractData AIR**: the *node/value/ups* side is unchanged, but
the D3 statement also needs (a) the `ContractData` key bytes to enter as `HOSTB` reads in the
`nodeV3`/`walkV3` key stream (a `HOSTB → CDKEYNIB` relay row family), and (b) the post-state
`upsV3` instance for the write. Both are the checklist's "D3 render" items, not new table
constraints.

## 4. The measurement [M]

### 4.1 Driver

`research/near-compression/native/pq-d3-join/measure_storage_write.py` verifies a case with the
clean-room D3 reference (`oracle/tools/spec_check_v3_d3.py`, which is the same implementation the
D3 oracle judges against), captures every `D3Store.write` with its pre-state trie root, walks the
`ContractData` path exactly as `TTN.lookupFrom` does, applies the write with `Trie2.update`
(nearcore's insert), and counts the rows the existing tables must render.

Cell counts use the D0a measured **widths and per-row costs** (one `nodeV3` row per serialized
byte, one `valV3` row per value byte, one `sha_t` block per 64-byte hash, `upsV3` per new record
byte). They are a **proxy**: they are not an AIR proof of a D3 fixture (that needs the render,
§5). The point is to price the state half and to show where the cells go.

### 4.2 Fixtures

The smallest honest fixtures with a `storage_write` are one-write D3 cases (a `d3rich` program
with op `01`, `19` or `1a`). Runs:

```
$ taskset -c 14-15,28-29 python3 research/near-compression/native/pq-d3-join/measure_storage_write.py \
    /data/illia/nearproof-deps/corpora/d3c10/d3/00-h10011-s3 ... 00-h10020-s2
```

| case | key B | nibbles | path nodes | pre ser B | old→new B | node cells | val cells | sha cells | ups cells | **cells** | walk rows | **inters** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 00-h10011-s3 | 14 | 28 | 6 | 600 | 8→5 | 225,600 | 136 | 194,208 | 122,210 | **542,154** | 30 | 39,704 |
| 00-h10013-s3 | 14 | 28 | 6 | 568 | 5→5 | 106,784 | 85 | 110,976 | 1,010 | **218,855** | 30 | 13,588 |
| 00-h10014-s0 | 14 | 28 | 5 | 508 | 0→8 | 208,304 | 0 | 184,960 | 122,816 | **516,080** | 30 | 37,556 |
| 00-h10018-s2 | 20 | 40 | 5 | 604 | 0→5 | 245,528 | 0 | 212,704 | 142,814 | **601,046** | 42 | 44,114 |
| 00-h10020-s2 | 14 | 28 | 5 | 636 | 0→8 | 256,432 | 0 | 221,952 | 148,672 | **627,056** | 30 | 45,944 |

Totals over the five: 2,505,191 cells, 180,906 interactions.

`00-h10013-s3` is an **overwrite of a key whose whole path is already revealed** (`old→new = 5→5`,
no new path nodes), so it hashes only the value and costs ~2.5x less than an insertion; it is the
floor, and `00-h10020-s2` (28-nibble key, insert, 636 pre-state node bytes) is the typical case.

Larger honest cases (multi-write, for range):

| case | writes | max key B | max val B | Σ cells | Σ inters |
|---|---:|---:|---:|---:|---:|
| d3c7/02-h10023-s4 | 4 | 19 | 4,018 | 4,084,744 | 276,271 |
| d3c9/03-h10143-s1 | 4 | 8 | 90 | 4,656,269 | 346,056 |
| d3c10/02-h10069-s2 | 1 | 16 | 16 | 902,004 | 67,599 |

### 4.3 What one `storage_write` adds

Against the D0a fixture baseline (1,262,608 committed cells and 76,428 interaction slots =
Σ rows × interactions over the 26 proved tables at their natural heights, `logs/baseline-d0a-prove.log`):

| quantity | single write (median of the five) | share of baseline |
|---|---:|---:|
| committed cells | 542,154 | **42.9 %** |
| interaction slots | 39,704 | **52.0 %** |

The structure, which is the interesting part:

* **SHA-256 dominates** (~36 % of the cells): each write hashes ~5–10 path nodes and the value,
  and `sha_t` is 544 columns wide. This is the same SHA-256 the D0a port already proves; it is
  not new, but it confirms that storage cost is hash-dominated, not walk-dominated.
* **`nodeV3` is second** (~42 %): one row per serialized byte of the pre-path *and* the newly
  created path records. A 28-nibble key is ~600 pre-state node bytes; the insert adds ~1,200.
* **`upsV3` is third** (~23 %): the post-state records (the new path nodes + value).
* **`walkV3` itself is tiny** (30 rows, 180 interactions for a 28-nibble key): the walk is a
  linear function of the key length and is *not* where the cost is.
* **`valV3` is negligible** for inserts; a 4 KB overwrite costs ~1,900 `val` cells plus ~800 KB
  more SHA (the `sha_t` term grows with the value length).

**Interpretation.** A single honest `storage_write` roughly doubles the D0a proof's work at these
small heights. Most of that is the SHA-256 and `node`/`ups` bytes of the *path*, both of which the
ported tables already handle — the genuinely new table content is the `ContractData` routing and
the D3 render. That is the quantitative backing for "the AIRs are reusable, the key routing is
not" (§0).

Caveats: the numbers are **byte-proxy** cells, not a proved D3 trace; the D3 fixture's other
tables (scheduler, receipts, scheduler rows for the FunctionCall) are **not** included; and the
`upsV3` count uses the post-state recut without the A7 duplicate elision, so it is an upper bound.

## 5. Remaining checklist

Owners are lane names; sizes are agent-days [E].

### Proof obligations

| # | obligation | owner | size | why it is a proof obligation |
|---|---|---|---:|---|
| P1 | `holdsP_of_swirl` | **done** in `lane/pq-state-port` @ `426b73deb` (not in this lane's base) | 0 | The generic SWIRL⇒`HoldsP` bridge. This lane consumes it, does not duplicate it. |
| P2 | `Joint → RelD3` composition (`Compose`) | this lane + `pq-state-port` | 3–5 | The statement is written (§1); the theorem from the two side relations plus `JointBusBalance` to `RelD3` is not. Needs the `runCall` fold over the D1/D3 extraction (`RelD3`'s hooks) and the `writes` log replay. |
| P3 | `WasmHalf`: `wasm_base_sound` with the HOST chip | `lane/pq-host-chip` | 5–8 | The current theorem has no host call. HOST chip, import-call `check`, `g_after`, and the spec-side `callHost` simulation given a response oracle (`pq-wasm-base` §14.3). |
| P4 | `StateHalf`: ContractData walk + `upsV3` in the D3 relation | this lane + `lane/v3-d3` render | 4–6 | The walk table exists (§3) but the D3 statement's key stream must consume `HOSTB`, and `upsV3` must apply the write log. The D0a/D1 renders do not cover contract data. |
| P5 | `CodeBound` across the two proofs | `pq-wasm-base` + `pq-state-port` | 1–2 | The receipt → `code_hash` binding is assumed today (`pq-wasm-base/STATEMENT.md` §5). The state side must publish the executed account's contract hash and prove it is the account value's hash. |
| P6 | `HOSTB` byte binding (Wasm memory ↔ state bytes) | `pq-host-chip` | 3–4 | `HOSTB` messages must be exactly the linear-memory range `(ptr, len)`; needs the MEMIO mover and its soundness. |
| P7 | `HOSTR` gas binding (`g_after`) | `pq-host-chip` | 2–3 | The state side's `sync`/`g := remaining` must produce the `g_after` the Wasm budget register consumes; this is the gas half of the interface. |
| P8 | TAPE / wire commitment passthrough to V_d | `pq-nv-preprocessed` / `pq-state-port` | 3–5 | M2 of the envelope study; the wire commitments need the same cached-root passthrough through every NV level. |
| P9 | `multBoundP` for the joined table set | this lane | 0.5 | One `decide +kernel` fact, as `nearAirV3D1_multBoundP_lt`; the joined `HOST`+classical total must stay `< p`. |
| P10 | SWIRL soundness (P5 of the envelope study) | shared | — | Not formalised for any PQ AIR; no extra cost for the join. |

### Engineering (no new theorem)

| # | item | owner | size |
|---|---|---|---:|
| E1 | D3 honest render for one `storage_write` (`statedump` mode `d3` + ContractData + `upsV3`) so §4's proxy becomes a proved trace | this lane / `v3-d3` | 5–8 |
| E2 | `HOSTQ/HOSTR/HOSTB` in the native SWIRL driver: a harness `TAPE`-like cached table per wire, and the cross-proof balance check | this lane | 2–3 |
| E3 | `ContractData` key routing in the state driver: `HOSTB → CDKEYNIB` relay, walk ids `W_CD`, and the write log → `upsV3` instance | this lane | 3–5 |
| E4 | the HOST chip and import-call support in `wasmBaseAir` (the `pq-host-chip` program) | `pq-host-chip` | 10–15 |
| E5 | a two-proof aggregation statement and its NV level | `pq-recursion-sha384` | 5–8 |
| E6 | raise the AIR cap / wire-bus numbering in the vk and NV (the join adds HOST tables on top of 30 + TAPE) | `pq-nv-preprocessed` | 2–3 |

### Blocked by another lane

* **P3, P6, P7, E4** are blocked on `lane/pq-host-chip` (HOST chip + import calls). Without them
  the Wasm proof cannot represent any real contract, so the join has nothing to join.
* **P4, E1, E3** are blocked on the D3 render (the `v3-d3` tooling) and on the state driver's
  ContractData support; they depend on §3's prefix, which is in place.
* **P8, E5, E6** are blocked on `pq-nv-preprocessed`/`pq-recursion-sha384`.
* **P2** is not blocked, but it needs P3/P4 to be meaningful; it can be stated against an abstract
  side relation now (it is) and proved once the sides exist.

### What is explicitly *not* a proof obligation

* The `ContractData` prefix encoding, the path split, the bus ids and the table rename — these
  are definitions and kernel facts (§3). Done.
* Extending `walkV3` with new constraints — **not needed**: `walkV3` is key-agnostic (§3.2).
* Re-deriving NEAR state semantics — not needed; the D0a/D1 port is reused.

## 6. Files

* `zk-formal/ZkFormal/NearV3/D3/ContractData.lean` — prefix, path, `B_CDKEYNIB`, `cdWalkV3`,
  `cdKibV3`, kernel facts.
* `zk-formal/ZkFormal/PQ/Join/Statement.lean` — the joint `Prop`, host messages, bus ids,
  `StateHalfStorageWrite`, `JointBusBalance`, `Joint`, `Compose`.
* `zk-formal/ZkFormal.lean` — two import lines appended.
* `research/near-compression/native/pq-d3-join/measure_storage_write.py` — the measurement.
* `research/near-compression/results/pq-d3-join/README.md` — this file.
* `research/near-compression/results/pq-d3-join/logs/` — the measurement output.

Nothing pinned was touched; `make pin-check` passes; `nearAirV3`, `nearAirV3D1`, the signed
relations, `challenges/` and `oracle/` are unchanged.
