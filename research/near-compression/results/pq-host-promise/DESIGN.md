# pq-host-promise: the widened HOST chip and the promise/receipt family

Lane `lane/pq-host-promise`, branched from `main` `639387b1a`, 2026-10-20.

Two deliverables:

* **Part 1 (built, proved, KAT'd)** — the single shared-file change that unblocks the D3α host
  functions: the HOST chip's argument window is widened from `np ≤ 2` to `np ≤ 9` while
  `ar ≤ 1`.  This is the piece 28 of the 64 D3α host functions need.
* **Part 2 (designed, priced)** — the 23 promise/receipt functions are added to the fixed host
  table with their true arities, and the receipt/promise state side is scoped: what is
  bookkeeping and what needs a new table.

Everything below is measured on this branch; the commit hash is in §6.

---

## 1. Part 1 — the widened HOST chip

### 1.1 The shapes

`research/near-compression/wasm-base-lean/WasmBase/HostChip.lean`:

| item | before | after |
|---|---|---|
| `Host.nArgs` | — (literal `2`) | **9** |
| argument columns | `pf0, pf1`, `tagP0/1`, `P0/P1` (4 limbs each), `tP0/1`, `hP0/1` | `pf 0..8`, then 7 columns per argument (`tagPj`, `Pj_0..3`, `tPj`, `hPj`) — 63 argument columns |
| `Host.kSb` / `Host.kCid` | 35 / 36 | **91 / 92** |
| `Host` table width | 37 | **93** |
| HOSTQ message | `[ts, hid, S, a0lo, a0hi, a1lo, a1hi, np]` (8) | `[ts, hid, S, np, (aLo j, aHi j) for j = 0..8]` (**22**) |
| HOSTR message | `[ts, st, rlo, rhi, glo, ghi, ar, 0]` (8) | unchanged |
| `HOSTO` (oracle) width | 19 (`q0..q7` + 11) | **33** (`q0..q21` + 11); `HostO.qLen := Host.qMsg.length` (derived, cannot drift) |
| constraints | 30 | **90** |
| CH receives | 2 `stkRecv` | **9**, one per argument |

`wasmBaseHostAir` is still `wasmBaseAir ++ [HOST, HOSTO, HOSTT, HOSTB]`, and `wasmBaseAir` is
**byte-identical**: `WasmBase/Chips.lean`, `WasmBase/Air.lean`, `WasmBase/Bus.lean` and
`Tool.lean` are untouched in this branch, and the exported `air` JSON is unchanged for every
`(nloc, ngl)`.

### 1.2 Constraints, generalized

The two-argument constraint names are kept (so the documented algebraic content is recognisable),
and every one of them now quantifies over `Host.argRange = List.range 9`:

```
cAct, cSt, cAr                 -- bits
cNres = nres − ar + st·ar      -- nres = (1 − st)·ar
cGLo/cGHi/cRLo/cRHi            -- 16-bit limb reconstruction (always true; documents the split)
cNp   = np − Σ_j pf j          -- np is the number of present arguments
cP j  = pf j · (pf j − 1)      -- every flag is a bit
cPOrder j = pf(j+1) − pf j·pf(j+1)      -- prefix-closed (j = 0..7)
cPad j, cTag j, cPadL j        -- an absent argument has zero tag and zero limbs; a present one tag 1
cActPf j, cActNres             -- inactive rows emit nothing
```

The one **semantic addition** is prefix-closure, `cPOrder j`.  With `np ≤ 2` it was only stated
for `(pf0, pf1)`; for nine arguments it is what makes `np = Σ pf j` the number of *leading*
arguments, which is what aligns the stack slots `sb + h − np + j` with the stack messages (and
what rules out the "holes" that would otherwise let a row cherry-pick argument positions).  It is
the natural n-ary form of the old `cP1P0` and it is required for `host_arg_view` to stay true.

### 1.3 One wide HOSTQ, not one message per argument

README §14.2 sketches "a second message row for more than five words" for `np > 5`.  Both options
were evaluated:

* **One message per argument** — needs either a bus per `k` or a variable-length wire with an
  index field and a per-`k` count column, and the HOST chip would need `np`-dependent gated
  interactions with a `k < np` range condition (a comparison the chip does not have).  The join's
  balance would become per-`(ts, k)`.  More columns, more rows, a new gadget.
* **One 22-field message** — one interaction, one balance obligation, exact native bus pre-check,
  no new gadget.

**Chosen: one wide message.**  The only cost is LogUp message length, and the NV envelope is
`log_max_message_length = 7`, i.e. `message.len() + 1 ≤ 128` fields *including the bus*
(`stark-backend .../keygen/mod.rs:146-151` checks exactly this at keygen).  22 + 1 = 23 ≤ 128, so
the wide message uses **18 % of the envelope**.  Even a four-limb-per-argument encoding at the
same arity (4 + 36 = 40 fields) would fit.  The envelope does not need to move for Part 1.  The
Rust driver was nevertheless changed from `log_max_message_length = 4` (16 fields, which the new
22-field HOSTQ would violate at keygen) to **7** — the NV value — so the driver and the join lane
use one number.  The extra 2 bits of LogUp slack cost 3 LogUp bits (333.3 → 330.3 at `2^28`
interactions); the printed soundness total does not move because it is proximity-bound (268.2).

This is kernel-checked, not asserted: `Chips.hostQ_len : Host.qMsg.length + 1 ≤ 128` and
`Chips.hostFns_shape : hostFns.all (np ≤ Host.nArgs ∧ ar ≤ 1) = true` (axioms: `propext` only for
the second, none for the first).

### 1.4 What had to be re-proved (nothing weakened)

| lemma | change |
|---|---|
| `RowHost.HostRowFacts` | fields `pf0Bit/pf1Bit → pfBit (∀ j < nArgs)`, scalar `npEq`/`order`/`pad0`/`pad1` → `npEq : np = cellSum …`, `order (∀ j+1 < nArgs)`, `pad (∀ j < nArgs)` |
| `RowHost.host_rowfacts` | re-proved from the grouped constraint list (`Host.cBase/cFlags/cOrder/cPads/cGates`); new membership lemmas `host_c*_mem` are `List.mem_append_*` chains rather than `by simp` (the 90-element list is too large for `simp` to unfold) |
| `RowHost.eval_pfSum` | **new** — `Σ_j pf j` over `argRange` as `cellSum` (reuses `Local.Call.eval_sumE`) |
| `RowHostSpec.host_inters_stk` | `List.range 2 → Host.argRange` (still `decide`) |
| `RowHostSpec.host_rawCons` | re-proved by induction on `argRange` with a per-slot `single_recv` lemma and a `flatMap_congr'` helper |
| `RowHostSpec.map_decMsg_flatMap` | **new** — `decMsg` through `flatMap` |
| `RowHostSpec.host_row_cons` | now `rowCons = argRange.flatMap (if pf j = 1 then [argMsg j] else [])`, takes no hypotheses |
| `RowHostSpec.host_pf_bits` | `∀ j < nArgs` |
| `RowHostSpec.host_arg_slot` / `host_arg_view` | `j < 2 → j < Host.nArgs`; `host_arg_slot` gained `rw [hn] at hj` (the bound `size − np + j < P` now needs `j < 9`, not `j < 2`) |
| `RowHostSpec.HostRowSpec.npBits` | `(∀ j ≤ 1 per flag) ∧ (prefix-closed, as nats) ∧ np = cellSum` |
| `RowHostSpec.host_rowspec` | re-proved: `host_order_nat` converts the field prefix-closure to `Nat` and feeds `Local.Call.le_of_mulsub`; `cellSum_argRange_lt` bounds the sum by 9 |
| `ExecHost.HostTraceOK` | `pf 0 = pf 1 = 0` → `(∀ j < nArgs, pf j = 0)`; `host_row_cons_inactive` re-proved via `flatMap_eq_nil_iff` |
| `ExecHost.host_part_ch_recv_active` | the n-ary `argRange.flatMap` form |
| `ExecHost.host_arg_stack` | `j < 2 → j < Host.nArgs` |
| `HostChipFacts.host_row_inactive_emits_nothing` | `pf j = 0` now derived for every `j` from `cActPf j`; `cActPf`'s membership is now `host_cActPf_mem` |

`host_row_prod`, `host_word_is_resp`, `host_row_cons_inactive`, `msgs_ch_host`,
`host_part_ch_send_active`, `host_r16_sound`, `host_rb_limb` are unchanged apart from the
signatures above.  **No statement was weakened.**  `host_row_cons` got *stronger* (its two
hypotheses are gone).  Axioms of every touched declaration: `⊆ {propext, Classical.choice,
Quot.sound}` (`#print axioms`).

### 1.5 Rust trace generator: two real bugs the widening exposed

Both were latent: with `np ≤ 1` in every previous KAT program they never fired.

1. **Argument order.** The generator popped arguments top-of-stack-first into `args[0..]`, but the
   spec's `popArgs` reverses, so `args[0]` is the *lowest* slot.  For `np ≥ 2` this swapped the
   arguments on HOSTQ and unbalanced the CH bus.  Fixed by popping then reversing.
2. **Producer time.** Every argument got `tp := ts − 1`.  That only works when the arguments were
   the *only* values pushed since the previous clock tick; with several arguments pushed at
   different rows, the time-check lookups were wrong.  Fixed by using the stack entry's own `tp`.

`tracegen.rs` also gains `HOST_NARGS = 9` / `HOST_QLEN = 22` constants shared with the HOSTO
request, an assertion `np ≤ HOST_NARGS`, and the HOSTO request built from all arguments.

### 1.6 Evidence

```
KAT:        79 passed, 0 failed   (77 previous + hostwide + hostwide9)
            python reference = Lean spec = Rust trace + constraint/bus pre-check
difftest:   base  air  3 2: 6600 points / 184,500 constraints / 131,700 interactions agree
            host airH 0 0: 5200 points / 143,200 constraints / 103,600 interactions agree
prove:      hostwide (np = 3)  → PROVE OK, verifies, 268.2-bit, 32.8 s, RSS 1.3 GiB
            hostwide9 (np = 9) → PROVE OK, verifies, 268.2-bit, 33.6 s, RSS 1.3 GiB
tamper:     hostwide 67/67, hostwide9 55/55, hostarg 77/77, hosttrap 65/65,
            hostkat8 (airH-2-g0) 84/84 — all rejected
```

The tamper suite gained explicit wide-window cases: `HOST.tagP{j}+1 (past np)`,
`HOST.P{j}_{0,3}+1 (past np)` (an absent argument's limbs must be zero),
`HOST.pf{j} (past np)` (turning on an argument beyond `np` breaks `np = Σ pf`), and
`HOST.pf{j} = 0 (drop arg)` (a hole in the middle breaks prefix-closure) — for `np = 3` and for
`np = 9`.  All rejected.

**`hostwide9`** is the new KAT that really exercises the maximum: nine distinct argument values
pushed, then `promise_batch_action_add_key_with_function_call` — so any permutation or off-by-one
in the window shows up as an unbalanced CH bus.  It aborts on the account-id check, which is
enough to exercise the window (the promise state side is Part 2).

---

## 2. Part 2 — the fixed host table grows to the promise family

`Chips.promiseFns`, appended after `hostFnsBase` so ids `0..7` are unchanged (the cached `HOSTT`
rows of an already-checked module stay byte-identical for those):

| id | name | np | ar |
|---:|---|---:|---:|
| 8 | promise_create | 8 | 1 |
| 9 | promise_then | 9 | 1 |
| 10 | promise_and | 2 | 1 |
| 11 | promise_batch_create | 2 | 1 |
| 12 | promise_batch_then | 3 | 1 |
| 13 | promise_set_refund_to | 3 | 0 |
| 14 | promise_batch_action_create_account | 1 | 0 |
| 15 | promise_batch_action_deploy_contract | 3 | 0 |
| 16 | promise_batch_action_function_call | 7 | 0 |
| 17 | promise_batch_action_function_call_weight | 8 | 0 |
| 18 | promise_batch_action_transfer | 2 | 0 |
| 19 | promise_batch_action_stake | 4 | 0 |
| 20 | promise_batch_action_add_key_with_full_access | 4 | 0 |
| 21 | promise_batch_action_add_key_with_function_call | 9 | 0 |
| 22 | promise_batch_action_delete_key | 3 | 0 |
| 23 | promise_batch_action_delete_account | 3 | 0 |
| 24 | promise_yield_create | 7 | 1 |
| 25 | promise_yield_create_with_id | 9 | 1 |
| 26 | promise_yield_resume | 4 | 1 |
| 27 | promise_yield_resume_with_yield_id | 4 | 1 |
| 28 | promise_results_count | 0 | 1 |
| 29 | promise_result | 2 | 1 |
| 30 | promise_return | 1 | 0 |

Arities are `NearSpecV3.Wasm.hostSigs` verbatim.  `hostFns_shape` is the kernel-checked guarantee
that all 31 entries fit the `np ≤ 9, ar ≤ 1` chip.

**One chip-level caveat, not fixed here** (deliberately: it needs a new result-tag column and is
cheap, but it is a separate change with its own KAT).  `promise_yield_resume` and
`promise_yield_resume_with_yield_id` return an **i32** (`pushRet … (is64 := false)`,
`Host.lean:1000-1130`).  The HOST row's result tag is the literal `1` (`stkSend sbNew 1 …`), so an
i32 result would be encoded as i64 on the stack.  The fix is `Host.rtag` (a column constrained to
`{0,1}` and pinned by the host table, exactly as `CALL`'s `resTag` is), 1 column + 1 bit
constraint + a `HOSTT` field.  Tracked as P2 below.

---

## 3. The promise/receipt state side: what exists and what is missing

**Nothing in the PQ stack constructs a receipt.**  `zk-formal/ZkFormal/NearV3/` has no D2
Actions/AR equivalent, and `spec/lean/v3/NearSpecV3/D2/Actions.lean` defines `ActionHooks` whose
`d2Hooks.functionCall` is `.error "out of domain (e.wasm)"` — the D3 hook is exactly the missing
piece.  So the promise family is **new AIR work**, not a port.  The division:

### 3.1 Bookkeeping — a faithful counting/encoding AIR over an existing wire (cheap)

These need the WASM↔state wire (`HOSTQ`/`HOSTR`, already built) plus counters/registers whose
values are *witnessed and range-checked*, with a small induction over the call log.  No trie, no
hashing, no new cryptographic object:

| function(s) | bookkeeping content | what is constrained |
|---|---|---|
| `promise_batch_create`, `promise_batch_then`, `promise_create`, `promise_then` | promise index counter, receipt index counter, dependency count | `next_idx = idx + 1`; a returned index is `< #receipts`; deps are a bounded multiset |
| `promise_and` | joint-promise node: `n` dependency indices read from memory | `n ≤ budget`; each index `< #promises` |
| `promise_set_refund_to` | a `refund_to` write on receipt `r` | `r < #receipts`, write-once |
| `promise_batch_action_*` (all 10) | action appended to receipt `r`: kind + field count | `r < #receipts`; per-kind field count; gas fields as 64-bit words |
| `promise_yield_create(_with_id)` | data-id counter, yield-id uniqueness | `next_data_id = data_id + 1`; a duplicate id short-circuits (returns `u64::MAX`); **32-byte** yield id |
| `promise_yield_resume*` | resumable flag + payload size | `|payload| ≤ 1024`; `|did| = 32`; the (i32) return is `0/1` |
| `promise_results_count`, `promise_result`, `promise_return` | result slot, return-data kind | slot index `< count`; `ret` is `Value | ReceiptIdx k` with `k < #receipts`; joint-promise rejection |

**Pricing (bookkeeping only):** 1 new table, ~15–25 columns (index counters, `n`, kind, `k`),
~10 degree-≤2 constraints, 2–4 `HOSTQ`/`HOSTR` interactions; ~1,500–2,500 Lean lines including the
call-log induction (`runHost` already reuses `run`).  **2–3 lane-weeks.**  The gas side is
*already* the `HOSTR.g_after` resynchronisation, so no new gas invariant object is needed.

### 3.2 Needs a new table — the receipt *contents* must be committed to a real object

`promise_*` is not just counting if the receipt has to be the receipt the state layer executes.
`apply_action_receipt` `NewReceipt` validation (`D2/Receipts.lean`, `validReceipt`) and
`receiptIdFrom parent height k = sha256(parent ‖ u64le height ‖ u64le k)` bind
`rid = sha256(…)` to the receipt *bytes*, and the action payloads are **borsh encodings** of
`ActionR` whose fields include byte strings (method name, args, key, public key, beneficiary).
Those bytes must be bound to the Wasm linear memory (the `HOSTB`/`MEMIO` wire) and hashed.

| piece | why a new table | cost |
|---|---|---|
| **Borsh/`ActionR` encoder** | `FunctionCall`'s `[kind ‖ signer ‖ pk ‖ gas_price ‖ outputs ‖ inputs ‖ actions]` is a variable-length encoding; a circuit must pin every byte and the length prefix | an encoding table (`RECTYPE`): 20–40 cols, ~40 constraints; **Lean 3–5 k lines**, beware 4 MiB args (a `sha0`/`sha1` *per-byte* path is the 2–3 G-cell cost class of the D3α study §8) |
| **Receipt id = SHA-256** | `receiptIdFrom` | **reuse** the existing `sha0`/`sha1` tables (a new *instance*, not a table); 0 new Lean, 512 rows per 64-byte block (already counted in D1) |
| **`RIDS` / `SRC` / `RCL`** (receipt id set, source routing, receipt-call log) | the D3 join names them as new receipt tables; the receipt set must be a permutation-committed multiset (every emitted receipt appears exactly once in the outcome) | 3 small tables: ~10 cols each, one multiset bus each; **1.5–2.5 lane-weeks** |
| **`newReceipts` / `logs` / `ret` fold** | `actionLoop`'s `merge` (append-only, order-sensitive) | a chained list table (a `cons`-list on a bus), 15–20 cols; **1–2 k Lean** |

### 3.3 What is *not* needed (reuse)

* `emitReceipts`, `refunds`, `actionLoop`, `processReceipt` — D2 code, reused unchanged
  (spec/near-chunk-validation-d3.md §8).
* The receipt **trie writes**: they are the state-side ContractData walk (P5/P4 in
  `pq-d3-join/README.md` §5), not this lane.
* The yield/resume **state mapping** (`YieldIdToDataId`, `PromiseYieldReceipt`): trie, state side.

### 3.4 Pricing summary and the honest gap

| block | kind | new Lean (lines) | lane-weeks |
|---|---|---:|---:|
| HOST chip widening (Part 1) | built | ~700 (changed+new) | **done** |
| bookkeeping table (counters/indices/kinds) | new table, small | 1.5–2.5 k | 2–3 |
| Borsh `ActionR` encoder + byte binding | new table, **the expensive one** | 3–5 k | 4–6 |
| `RIDS`/`SRC`/`RCL` + `newReceipts` fold | 4 small tables | 2.5–4.5 k | 3–4 |
| per-byte args at D3α scale (4 MiB) | **row cost**, not Lean | — | 2–3 (segmentation) |
| i32 result tag (`Host.rtag`) | chip column | ~100 | 0.5 |

So: **≈ 7–12 lane-weeks and ≈ 7–12 k Lean lines** for a receipt family that a state layer can
execute, of which only **2–3 weeks** is the "bookkeeping" part that is cheap.  The single dominant
cost is that there is **no receipt-construction AIR anywhere in the PQ stack** — the byte encoding
is the work, not the promise indices.  Until then the 23 entries give the Wasm side a correct
*trace-level* host call (arguments consumed, request on HOSTQ, `g_after` returned) with the
receipt semantics a `HOSTO` oracle, exactly as `storage_*` and `input` are today.

---

## 4. Follow-ups (out of scope here, filed for the lanes that own them)

| id | item | owner | size |
|---|---|---|---|
| P1 | `Host.rtag` (i32 results for `promise_yield_resume*`), `HOSTT` gains a tag field | this lane | 0.5 wk |
| P2 | the bookkeeping table (§3.1) + the call-log induction over `runHost` | this lane | 2–3 wk |
| P3 | Borsh `ActionR` encoder + `HOSTB` byte binding | `pq-host-bytes` + this lane | 4–6 wk |
| P4 | `RIDS`/`SRC`/`RCL` + `newReceipts` fold | `pq-d3-join` | 3–4 wk |
| P5 | a `HOSTQ`-side state-port consumer for the wide request (state side must parse 22 fields) | `pq-state-port` | 1 wk |
| P6 | `wasm_base_exec_host` (the segmented induction) — unchanged by this lane, still the top gap | `pq-exec-host` | 3–4 wk |

P5 is the only *interface* change this lane forces on another lane: `HOSTQ` is now 22 fields, so
the state port's `HOSTQ` message must be widened to match (it must not silently keep 8).

---

## 5. Bus numbering (unchanged)

`HOSTQ = 208`, `HOSTR = 209`, `HOSTB = 210` (cross-proof), `HOSTT = 9` (Wasm-internal).  No new
bus was introduced.  See `pq-d3-join/BUS-NUMBERING.md`.

---

## 6. Reproduce

```
# Lean
HEAVY_MEM=16G taskset -c 8-10,24-25 /data/illia/nearproof-deps/bin/heavy sh -c \
  'cd research/near-compression/wasm-base-lean && lake build'
# Rust
cd research/near-compression/native/wasm-base && taskset -c 8-10,24-25 cargo build --release
# KAT (rebuild BOTH binaries first — a stale wasmbase-tool gave false failures before)
cd research/near-compression/native/wasm-base && \
  taskset -c 8-10,24-25 /data/illia/nearproof-deps/bin/heavy env \
    WASMBASE_BIN=$PWD/target/release/nearproof-wasm-base bash run_kat.sh /tmp/kat 8 64
```

Commit: `pq-host-promise: widen the HOST chip to np ≤ 9 and add the promise host table` (see
`git log lane/pq-host-promise -1`).
