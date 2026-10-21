# pq-host-logreg: the D3α log/panic and register/return host functions

Lane `lane/pq-host-logreg`, from `main` @ `639387b1a`.  2026-10-20.

Scope: the ten D3α host functions the HOST chip does not yet cover, in the direct-Wasm PQ base layer:

| group | functions |
|---|---|
| log / panic | `log_utf8`, `log_utf16`, `panic`, `panic_utf8`, `abort` |
| register / return | `input`, `read_register`, `register_len`, `write_register`, `value_return` |

The Wasm-side HOST chip is **generic**: it takes `(hid, np, ar)` from `hostFns` and moves arguments
and results through `HOSTQ`/`HOSTR` to the in-trace oracle `HOSTO`, so no per-function chip is
needed.  What was needed is (1) `hostFns` entries, (2) the register space (channel space 6), (3)
the byte payloads through `HOSTB`, and (4) KATs.  This is what this lane delivers.

## 1. `hostFns` entries

Appended to `Chips.hostFns` (`WasmBase/HostChip.lean`), ids 0-7 unchanged:

| id | name | np | ar | group |
|---:|---|---:|---:|---|
| 8 | `log_utf8` | 2 | 0 | log |
| 9 | `log_utf16` | 2 | 0 | log |
| 10 | `panic_utf8` | 2 | 0 | log |
| 11 | `abort` | 4 | 0 | **blocked** (arity) |
| 12 | `input` | 1 | 0 | register |
| 13 | `read_register` | 2 | 0 | register |
| 14 | `write_register` | 3 | 0 | **blocked** (arity) |
| 15 | `value_return` | 2 | 0 | return |

`panic` (7) and `register_len` (6) were already in the table.

`hostFns_all_arity` (`by decide`) proves every **admitted** entry still has `np ≤ 2 ∧ ar ≤ 1`: the
HOST chip's `np ≤ 2`/`ar ≤ 1` constraint set is **unchanged**.  `abort` (np 4) and `write_register`
(np 3) are recorded in `hostFnsWide` (ids 11/14 reserved, names and arities fixed) but are **not**
accepted by `hostIdOf`/`hostSig`: a module importing one is outside the proved domain until another
lane widens the arity.  `hostFns_covered` (`by decide`) records that they are exactly the entries
with `np > 2`.

## 2. The register space (channel space 6)

### 2.1 Message model — `WasmBase/RegisterSpace.lean`

A channel `Msg` has one `slot`, so `(register_id, pos)` is encoded as

```
slot rid pos = rid · 2^24 + pos          cap = 2^24,   posBits = 24
byteSlot rid i = slot rid (i + 1)        lenSlot rid = slot rid 0
```

Two message shapes share the space and differ in `tag`:

* a **byte** message `byteMsg rid i b tp = [6, byteSlot rid i, 0, b, 0, 0, 0, tp]`;
* a **length** message `lenMsg rid len tp = [6, lenSlot rid, 2, len, 0, 0, 0, tp]`.

`tag = 2` (not 1) is deliberate: `Msg.ok` reads tag 1 as an `i64`, and a register length is not a
value.  `lenMsg_not_ok` proves a length message is *not* a value message, so the register file cannot
be confused with the operand stack.

**Domain conditions** (explicit, `Bool`-valued, with `_iff` lemmas): `regOK rid = rid ≤ 99`
(`maxNumberRegisters = 100`), `posOK pos = pos < 2^24`, `lenOK len = len < 2^24`, bundled in
`domainOK rid pos len = regOK rid && posOK pos && lenOK len && pos < len`.

**Proved** (no `Holds`, axioms ⊆ `{propext, Classical.choice, Quot.sound}`): `slot_mod`, `slot_inj`
(the key is injective on the domain), `slot_lt_P` (`rid ≤ 99, pos < 2^24 ⇒ slot < p`, so the
encoding is exact in the field), `byteSlot_eq`/`_div`/`_mod`/`_inj`/`_ne`, `lenSlot_eq`,
`lenSlot_ne_byteSlot`, `byteMsg_ok`, `lenMsg_not_ok`, `mem_view`, `view_len_mem`, `view_byte`,
`regMsgs_disjoint` (two registers' message sets are disjoint) and `regMsgs_nodup` (one register's view
is `Nodup`).  `view` maps a register file `Array (Nat × ByteArray)` to its messages, one length and
one byte message per register.

**Stated, not proved** (labelled `Prop`): `RegBusSound` (every live space-6 message is a message of
the final register file — the state-side obligation) and `RegLenAgree` (a byte group's length agrees
with its length message — the group walk; see §2.3).

### 2.2 The AIR wire — `WasmBase/RegChip.lean` (table `REG`)

Registers are a **persistent state**, so a row is modelled like the globals (space 2): every access
**produces** the register's message at `ts` and consumes the previous one at `tp` unless it creates
the register.  One row per register byte (`kind = 0`) or per register length (`kind = 1`):

```
act, kind, rd, rid, pos, len, byte, hid, ts, dir, gap, fresh, tp, hp, ptr
```

* `rd = 0` — **fill** (`input`): creates the register (`cFreshFill` ⇒ `fresh = 0`).  A fill byte
  *receives* the byte from `HOSTB` (`dir = 1`, state → Wasm); `HOSTB` carries the state-side half of
  the same message (`HOSTB.reg = 1`), so the wire balances across the two tables.
* `rd = 1` — **read** (`read_register`, `register_len`, `value_return` from a register): consumes
  the current message at `tp` and re-produces it at `ts`, so a register can be read repeatedly.
  Wasm-side only, so it emits no `HOSTB` message; `ptr` is the read's destination address, carried
  for the deferred MEMIO link.

| constraint | expression | meaning |
|---|---|---|
| `cAct`/`cKind`/`cRd`/`cFresh`/`cDir` | `x·(x−1)` | the five flags are bits |
| `cDirRd` | `act·(1−kind)·(dir − (1 − rd))` | a byte row's `dir` is `1 − rd` |
| `cFreshFill` | `act·(1−rd)·fresh` | a fill creates the register |
| `cPosLtLen` | `act·(1−kind)·(len − pos − 1 − gap)` | `pos < len` on a byte row |

plus lookups: `byteQ 0 byte 0 0 (act·(1−kind))` (`byte < 256`), `r16 gap`, `r16 len`, `r16 rid`, and
the time check `r16 (ts−tp−1−2^16·hp)`, `r16 (4·hp)` with count `act·fresh`.  All constraints have
degree ≤ 2.

`wasmBaseRegAir nloc ngl = wasmBaseHostAir nloc ngl ++ [REG]` (REG at index 26, `reg_air_len` = 27).
`wasmBaseHostAir` is **untouched**, so every proved index (0-25) is unchanged.

`HOSTB` gains a `reg` column and the constraint `cRegDir` (`reg·(1−dir) = 0`: only a response byte
fills a register).  When `reg = 1` the byte is a register fill: `HOSTB` sends the state-side half and
`REG` receives the Wasm-side half; when `reg = 0` the byte is a plain payload and `HOSTB` carries both
halves (the self-permutation of the minimum slice).  `HOSTB`'s `BYTE`/`gap` lookups are gated by
`1 − reg`, since `REG` owns them for a register byte.

`WasmBase/Main/RegFacts.lean` extracts the row facts from `Holds`: `reg_row_constraints`,
`reg_row_bits`, `reg_recv_only_range16` (only RANGE16 answers R16 in the reg AIR) and
`reg_r16_query_16bit` (a count-1 R16 query is one value `< 2^16`).  `Chips.reg_row_key_bounds` shows
the AIR's R16 bounds (`rid, len < 2^16`, `pos + gap + 1 = len`) are inside the model's key domain.

### 2.3 What is blocked (named)

1. **The group walk.**  Nothing forces the byte rows of a register to be `pos = 0 .. len−1` with no
   gaps/duplicates/extra rows, nor the length row's `len` to equal that count.  This is exactly
   `Register.RegLenAgree`.  It needs a `next`-based group structure keyed by `(rid, ts)` plus a
   `cLast`-style endpoint pin — the shape `HOSTB` already uses for `(ts, dir)`.
2. **The memory direction of a read.**  A `read_register` row should write its byte into linear
   memory (space 3) at `ptr + pos`.  That is the same `(ptr, len)` MEMIO link `HOSTB` defers; `ptr`
   is carried so the join has the address.  Without it a program cannot observe read bytes through
   `i64.load`, so the KAT returns `register_len` for the length and uses `read_register` for its
   channel effect.
3. **Joining REG into the `wasmBaseHostAir` execution theorem.**  REG carries space-6 CH
   interactions, so `Main/ExecHost.msgs_ch_host` and the bus decomposition would have to include it.
   This lane keeps the 26-table AIR byte-identical and exports REG separately (`airR`).

## 3. `value_return` and the logs on `HOSTB`

`log_utf8` / `log_utf16` / `panic_utf8` / `value_return` are `np = 2` calls whose byte payload goes
on `HOSTB`: a `dir = 0` (Wasm → state) group `[ts, hid, 0, pos, byte]` for `pos = 0 .. len−1`, keyed
by the call's `(ts, hid)`, with `len`/`gap` committed and `pos < len` proved by the R16 gap lookup.
`hostByteIds = [8, 9, 10, 15]` is the set; `hostByteIds_mem` (`by decide`) proves each is in the
host table.  `panic` (id 7) has no payload and needs nothing beyond its existing HOST row.  The AIR
side is the existing `HOSTB` table (unchanged except the `reg` column and its gating), so no new chip
was needed for the logs.

## 4. Rust / KAT

* `programs/gen.py`: `regkat` (input(0) 5 bytes → `register_len` → `read_register(0,64)` →
  `register_len`, result 5007), `regloop8` (input + 8 reads + a final length), `logkat`
  (`log_utf8`, `log_utf16`, `value_return` over a data segment), `logtrap` (`log_utf8` then `panic`).
  `refinterp.py` models `input`/`register_len`/`read_register`/`log_*`/`value_return`.
* `run_kat.sh` passes the program's `input` hex to `wasmbase-tool prep` and selects `airR` when a
  program has register events (a new `input` on `prep`; a new `evalR`/`airR` in `Tool.lean`).
* `tracegen.rs`: REG fill/read rows (from the spec's own post-call register file `ev.regs`), the fill
  bytes on `HOSTB` (`reg = 1`), the log/return payload groups, and a DRAIN of the final register file
  on space 6 (which *is* `Register.view`).  Two real bugs were found and fixed on the way: HOST
  arguments were filled in the wrong order for `np = 2` and their producer time was faked as `ts−1`
  (now the stack entry's own `tp`), and `HOSTT`'s multiplicities were indexed by row instead of by
  host id (ids 11/14 are reserved, so the table is not contiguous).  `HOSTO`'s request word now uses
  the same 32-bit halves as `HOSTQ`.
* `main.rs`: REG tamper cases.
* `difftest.py`: `WASMBASE_AIRR=1` for `wasmBaseRegAir`.

### Results

Lean build (`HEAVY_MEM=16G taskset -c 11-13,26-27 …/heavy sh -c 'lake build'`):
`Build completed successfully (132 jobs).`  No `sorry`; axioms ⊆ `propext, Classical.choice,
Quot.sound`.

KAT (`run_kat.sh /tmp/rk 8 64`): **81 passed, 0 failed** (78 existing + `regkat`, `regloop8`,
`logkat`; `logtrap` replaces nothing and is `trap`-compared).

`check` on the register program (`airR`, 27 tables):

```
TABLE HOSTB  width 10 rows 8  constraints 13 interactions 7 degree 3
TABLE REG    width 15 rows 16 constraints  8 interactions 11 degree 3
CHECK OK result Some((1, 5007))
```

Tamper, `regkat` on `airR`: **76/76 rejected** (9 REG cases: `byte+1`, `pos+1`, `rid+1`, `bv+1`,
`rd=1-rd`, `kind=1`, `fresh=1`, a length row's `len+1`, and a duplicate `(rid,pos)`).  `logkat` on
`airH`: **61/61**.  Pre-existing suites unchanged: `hostarg` 65/65, `hosttrap` 53/53, `hostkat8`
72/72.

Difftest: `wasmBaseRegAir` 432 points, 10,608 constraint values and 7,696 interactions agree; the
base and host difftests still pass (352 / 416 points).

`make pin-check`: exit 0; no `spec/`, `challenges/` or `oracle/` file modified.

## 5. Per-function status

| function | np | ar | what it needed | status |
|---|---:|---:|---|---|
| `panic` | 0 | 0 | HOST row only (id 7, already present) | **covered** (HOST + KAT `logtrap`) |
| `log_utf8` | 2 | 0 | `hostFns` 8, payload group on `HOSTB` | **covered** (AIR + KAT `logkat`) |
| `log_utf16` | 2 | 0 | `hostFns` 9, payload group on `HOSTB` | **covered** (AIR + KAT `logkat`) |
| `panic_utf8` | 2 | 0 | `hostFns` 10, payload group on `HOSTB` | **covered** (AIR; no dedicated KAT) |
| `value_return` | 2 | 0 | `hostFns` 15, payload group on `HOSTB` | **covered** (AIR + KAT `logkat`) |
| `input` | 1 | 0 | `hostFns` 12; REG fill rows (space 6) + `HOSTB` half | **covered** (AIR + KAT `regkat`) |
| `register_len` | 1 | 1 | already id 6; REG length message | **covered** (AIR + KAT `regkat`) |
| `read_register` | 2 | 0 | `hostFns` 13; REG read rows (consume + re-produce) | **covered** (AIR + KAT `regkat`) |
| `abort` | 4 | 0 | `hostFns` id 11 reserved; needs `np` widened past 2 | **blocked** (arity; other lane) |
| `write_register` | 3 | 0 | `hostFns` id 14 reserved; needs `np` widened past 2.  Its register *half* (a fill from memory) is the REG fill case, so the space-6 model covers it once the call is admitted | **blocked** (arity; other lane) |

## 6. Files touched

* `wasm-base-lean/WasmBase/HostChip.lean` — 6 new `hostFns` entries, `hostFnsWide`,
  `hostByteIds`, `HOSTB.reg` + `cRegDir` + gated lookups.
* `wasm-base-lean/WasmBase/RegisterSpace.lean` (new) — space-6 model, key encoding, domain
  conditions, view, stated `Prop`s.
* `wasm-base-lean/WasmBase/RegChip.lean` (new) — the `REG` table, `wasmBaseRegAir`, cheap facts.
* `wasm-base-lean/WasmBase/Main/RegFacts.lean` (new) — REG row facts from `Holds`.
* `wasm-base-lean/WasmBase.lean`, `Tool.lean` — imports; `airR`/`evalR`; `prep` input hex; `regs` in
  the host event.
* `native/wasm-base/src/tracegen.rs`, `src/main.rs`, `programs/{gen,refinterp}.py`, `run_kat.sh`,
  `difftest.py`.
