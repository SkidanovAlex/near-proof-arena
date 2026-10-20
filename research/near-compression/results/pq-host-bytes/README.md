# pq-host-bytes: the `HOSTB` byte-payload bus (minimum slice)

Lane `lane/pq-host-bytes` @ `8412a9c2a`.  This is deliberately the **minimum** slice: one bus, one
table, one trace generator, three tamper cases.  Nothing about memory pointers, lengths or the
register space.

## 1. Bus and table shapes

**Bus** (`WasmBase/Chips.lean` numbering, in `WasmBase/HostChip.lean`):

```
busHostQ = 208   (HOSTQ)   existing
busHostR = 209   (HOSTR)   existing
busHostT =   9   (HOSTT)   existing, Wasm-internal
busHostB = 210   (HOSTB)   new
```

208/209 are taken by `HOSTQ`/`HOSTR`, the state side's shifted buses occupy 128-203, and 9 is the
Wasm-internal `HOSTT`, so 210 is the free id (matches `PQ/Join/Statement.lean`'s `B_HOSTB`).

**Bus message**: `[ts, dir, pos, byte]`, one message per byte moved.

| field | meaning |
|---|---|
| `ts` | Wasm row clock of the host call |
| `dir` | `0` = Wasm → state (request bytes), `1` = state → Wasm (response bytes) |
| `pos` | byte offset inside the `(ts, dir)` string, `0, 1, 2, …` |
| `byte` | the byte value, `0..255` |

**Table `HOSTB`** (appended to `wasmBaseHostAir` after `HOST`/`HOSTO`/`HOSTT`, index 25):

```
cols = [ts, dir, pos, byte, act, f]
```

`act` is row activity (0 on padding rows), `f` is the group-break flag (1 on the first row of a
`(ts, dir)` group).

## 2. What is constrained (all degree ≤ 2)

| constraint | expression | meaning |
|---|---|---|
| `cAct` | `act·(act−1)` | `act` is a bit |
| `cF` | `f·(f−1)` | `f` is a bit |
| `cDir` | `dir·(dir−1)` | `dir` is a bit (0 request, 1 response) |
| `cFirst` | `first·(1−f)` | row 0 starts a group |
| `cLast` | `last·(1−f)` | the last row starts a group too |
| `cTs` | `(1−nxt.f)·(nxt.ts − ts)` | a group keeps `ts` |
| `cDirG` | `(1−nxt.f)·(nxt.dir − dir)` | a group keeps `dir` |
| `cPos` | `(1−nxt.f)·(nxt.pos − pos − 1)` | inside a group `pos` increases by exactly one |
| BYTE lookup | `byteQ 0 byte 0 0 act` | `byte < 256` via the `BYTE` kind-0 table (count `act`) |

`cFirst` + `cLast` are the group/final-row checks: the table begins and ends at a group break, so
the cyclic `next` of the last row is also a break and the `next`-based constraints cannot fire
across the wrap.  The trace generator pads with group-start rows (`f = 1`, `act = 0`, `ts = dir =
pos = byte = 0`), which satisfies all of them.

**Bus usage in this table**, with 0/1 multiplicities as everywhere else:

```
send   act·(1−dir)  [ts, dir, pos, byte]      Wasm side → state side (request)
recv   act·(1−dir)  [ts, dir, pos, byte]      state side → Wasm side (request)
send   act·dir      [ts, dir, pos, byte]      Wasm side ← state side (response)
recv   act·dir      [ts, dir, pos, byte]      state side ← Wasm side (response)
```

The first send/receive pair of each `dir` is the same message with the same count, so the wire is a
self-permutation and balances by construction.  This mirrors how `HOSTO` stands in for the state
side on `HOSTQ`/`HOSTR`: a joined proof keeps the Wasm-side half and replaces the other half by the
state tables on bus 210.  `act·dir` and `act·(1−dir)` are bits because `act` and `dir` are.

## 3. What is NOT modelled

* **the memory pointer** — no `(ptr, len)` range, no channel space 3 link;
* **the byte length** — no length message, no `pos < len` constraint;
* **the register space (space 6)** — not built;
* **the byte content** — a byte in `0..255` is a free witness: it is not tied to memory or to the
  state side, so a proof says "these bytes were moved", not "these exact memory bytes were moved";
* **the mapping of a `HOSTB` group to a `HOSTQ` call** — groups are keyed by `ts` but this slice
  does not constrain that `ts` to be a HOST row's `ts`, nor that `dir = 1` groups answer a matching
  request;
* **what an empty string looks like** — there is no zero-byte group, so lengths are not implied;
* **space 3 (linear memory) and registers** — untouched;
* `wasmBaseAir` — untouched (byte-identical, first 22 tables); only `wasmBaseHostAir` grows.

## 4. Trace generation (Rust)

`native/wasm-base/src/tracegen.rs`: for the first host call of a host program the generator emits

* 4 request rows `(ts, 0, 0..3, byte)` — the low four bytes of the call's first argument;
* 4 response rows `(ts, 1, 0..3, byte)` — the low four bytes of the result word;
* padding group-start rows up to a power of two.

The bytes are a placeholder for the `(ptr, len)` memory range (see §3).  The `BYTE` multiplicity
`m0` is incremented once per active row, matching the lookup count `act`.

The Rust side needed **no loader change**: `src/air.rs` reads the Lean export generically
(`wasmbase-tool airH nloc ngl`), so a new table is picked up from the JSON with no code.

## 5. Commands run and results

Lean build (heavy wrapper, cores 11-13/26-27):

```
HEAVY_MEM=16G taskset -c 11-13,26-27 /data/illia/nearproof-deps/bin/heavy \
  sh -c 'cd research/near-compression/wasm-base-lean && lake build'
  -> Build completed successfully (119 jobs).
```

Rust build (shared dependency target, no vendoring):

```
cd research/near-compression/native/wasm-base
CARGO_TARGET_DIR=/data/illia/nearproof-deps/pq-wasm-base/target \
  taskset -c 11-13,26-27 cargo build --release --offline
  -> Finished `release` profile [optimized] target(s)
```

KAT harness (77 host+base programs):

```
WASMBASE_BIN=/data/illia/nearproof-deps/pq-wasm-base/target/release/nearproof-wasm-base \
  bash run_kat.sh /tmp/hb-kat2 8 64
  -> KAT: 77 passed, 0 failed (python ref = Lean spec = Rust trace + AIR pre-check)
```

`logs/kat.log`.

`check` on the new table (constraint + bus pre-check):

```
nearproof-wasm-base check airH-0-g0.json progs/hostarg.prep.json
  TABLE HOSTB     width   6 rows     16 height     16 cells       96 constraints   8 interactions   5 degree 2
  CHECK OK result Some((1, 18446744073709551615))
```

`logs/check-hostarg.log`.

### Tamper cases (3 new, all rejected by the native verifier)

| case | rejected by |
|---|---|
| `HOSTB[row 0].byte+1` | bus (the `BYTE` lookup moves) |
| `HOSTB[row 0].dir=2` | constraint `dir·(dir−1)` |
| `HOSTB dup pos rows 0,1` | constraint `nxt.pos − pos − 1` |

```
hostarg  : TAMPER summary 62/62 rejected   (logs/tamper-hostarg.log)
hostkat8 : TAMPER summary 69/69 rejected   (logs/tamper-hostkat8.log)
hosttrap : TAMPER summary 50/50 rejected   (logs/tamper-hosttrap.log)
```

Lean/Rust AIR difftest on `wasmBaseHostAir` (26 tables):

```
WASMBASE_AIRH=1 python3 difftest.py 0 0 /tmp/hb-dt2 16
  -> DIFFTEST OK: 416 points, 10352 constraint values and 7488 interactions agree
```

`logs/difftest-host.log`.

`make pin-check`: exit 0; no pinned file, challenge, `oracle/` or `spec/` file was modified.

## 6. Files touched

* `wasm-base-lean/WasmBase/HostChip.lean` — `busHostB := 210`, `namespace HostB` (table +
  constraints + interactions), `wasmBaseHostAir` appends `Chips.HostB.table`.
* `native/wasm-base/src/tracegen.rs` — HOSTB row generation and padding.
* `native/wasm-base/src/main.rs` — three HOSTB tamper cases.

`wasmBaseAir` is unchanged (the exported first 22 tables are byte-identical).
