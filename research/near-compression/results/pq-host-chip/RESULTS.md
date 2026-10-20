# pq-host-chip: HOST chip and host-call buses (direct-Wasm PQ base layer)

Lane `lane/pq-host-chip` (branched from `lane/pq-wasm-base` @ `7952ca42e`), 2026-10-20.
Implements README §14.2/§14.3 of `../pq-wasm-base/README.md`: the first blocking gap — a Wasm run
that makes a host call — for the PQ FunctionCall proof.

## 1. What was built

| piece | where |
|---|---|
| HOST chip, HOSTQ/HOSTR/HOSTT/HOSTO buses, fixed host table, `wasmBaseHostAir` | `wasm-base-lean/WasmBase/HostChip.lean` |
| host-aware checker (`checkModuleH`, import calls, import-domain conditions) | `wasm-base-lean/WasmBase/HostCheck.lean` |
| spec step under an abstract response oracle (`step_host_ok`, `step_host_abort`) | `wasm-base-lean/WasmBase/StepHost.lean` |
| HOST row lemma (constraints + STATE messages) | `wasm-base-lean/WasmBase/Main/RowHost.lean` |
| Lean tool: `airH`, `evalH`, `prep` records host responses | `wasm-base-lean/Tool.lean` |
| trace generation for HOST/HOSTO/HOSTT, HOST tamper cases | `native/wasm-base/src/tracegen.rs`, `src/main.rs` |
| import-capable assembler + 4 host KAT programs | `native/wasm-base/programs/{wasmasm,refinterp,gen}.py` |
| HOST KATs wired into the harness | `native/wasm-base/run_kat.sh` |

Domain of this slice: import calls with `np ≤ 2`, `ar ≤ 1`, arguments/results i64, from a fixed
table of 8 host functions (`block_index`, `block_timestamp`, `epoch_height`, `storage_usage`,
`prepaid_gas`, `used_gas`, `register_len`, `panic`).  The table is a cached trace bound like FUNC.
`wasmBaseAir` is untouched: `wasmBaseHostAir = wasmBaseAir ++ [HOST, HOSTO, HOSTT]`.

The buses:

| bus | name | message | role |
|---|---|---|---|
| 7 | HOSTQ | `[ts, hid, S, a0lo, a0hi, a1lo, a1hi, np]` | request, sent by HOST |
| 8 | HOSTR | `[ts, st, rlo, rhi, glo, ghi, ar, 0]` | response, received by HOST (`st = 0` ok, `1` abort) |
| 9 | HOSTT | `[hid, np, ar, 0,0,0,0,0]` | cached host-function table, like FUNC |

`HOSTO` is the response **oracle** in-trace: one row per call, receiving HOSTQ and sending HOSTR.
The soundness statement is therefore relative to those responses; joining with the state proof
(README §14.2) replaces `HOSTO` by the state tables on the same buses.

Gas: `S` advances by the instruction `fee` only; the host ext costs and `sync` are the state side's,
returned as `g_after` on HOSTR and as the budget register.  This is why the Wasm-only invariant
`R·S + g = g0` does **not** hold across a host call.

## 2. Commands and results (all run in this worktree)

Lean (heavy wrapper, cores 8-10/24-25):

```
HEAVY_MEM=16G taskset -c 8-10,24-25 /data/illia/nearproof-deps/bin/heavy lake build WasmBase
  -> Build completed successfully (86 jobs).
#print axioms WasmBase.host_rowfacts / step_host_ok / step_host_abort
  -> [propext, Classical.choice, Quot.sound]
grep -rn 'sorry|native_decide|implemented_by' (new files) -> CLEAN
```

KAT harness (77 programs; 73 previous + `hostkat8`, `hostkat64`, `hostarg`, `hosttrap`):

```
bash run_kat.sh /tmp/katrun 8 64
  -> KAT: 77 passed, 0 failed (python ref = Lean spec = Rust trace + AIR pre-check)
```
`logs/kat.log`.  Each host program's `check` ends in `CHECK OK`: e.g. `hostarg -> CHECK OK result
Some((1, 18446744073709551615))`, `hosttrap -> CHECK OK result None` (the imported `panic` aborts).

Native proofs (seg-v1 small shape, 268.2-bit soundness):

```
nearproof-wasm-base prove airH .../hostarg.prep.json small
  -> PROVE OK steps 7 result Some((1, 18446744073709551615))
nearproof-wasm-base prove airH .../hostkat8.prep.json small
  -> PROVE OK steps 126 result Some((1, 416))
nearproof-wasm-base prove airH .../hosttrap.prep.json small
  -> PROVE OK steps 3 result None
```
`logs/prove-hostarg.log`, `logs/prove-hostkat8.log`, `logs/prove-hosttrap.log`.

Lean/Rust AIR difftest on `wasmBaseHostAir` (25 tables):

```
WASMBASE_AIRH=1 python3 difftest.py 0 0 /tmp/dt-host 16
  -> DIFFTEST OK: 400 points, 10224 constraint values and 7408 interactions agree
```
`logs/difftest-host.log`.

Tamper (native verifier; HOST-specific cases `HOST.*`, `HOSTO.*`, `HOSTT.*`):

```
hostkat8  59/.. -> TAMPER summary 66/66 rejected
hostarg         -> TAMPER summary 59/59 rejected
hosttrap        -> TAMPER summary 47/47 rejected
```
`logs/tamper-hostkat8.log`, `logs/tamper-hostarg.log`, `logs/tamper-hosttrap.log`.

The **pre-existing** F1 / memory / globals / calls tamper suites were re-run unchanged and still
pass: `callkat8 91/91`, `hashloop8 43/43`, `memkat 45/45`, `globkat8 53/53`, `fib10 73/73`,
`calltrap 74/74` (`logs/tamper-base-*.log`).

`make pin-check`: passes (exit 0); no pinned file, challenge, `oracle/` or signed relation was
modified.

## 3. What is not done, and the smallest next step

* **Full host-aware `wasm_base_sound`.**  The HOST row lemma gives the local semantics; the
  top-level gas invariant must be generalised because each host call resynchronises
  `g := remaining`.  The natural invariant is
  `R·(S_final − S_0) + Σ_k (g_after,k − g_before,k) + g_final = g0` restricted to host intervals, or
  equivalently "burnt instruction gas plus the last resynchronised budget".  Everything else
  (frames, stack, memory, calls, globals) is already in `RelW` and unchanged.  This is the next
  slice; the row lemma and step lemma are its inputs.
* **MEMIO byte movement / `HOSTB`.**  The HOST bus carries lengths and one result word; byte
  strings (keys, values, logs, return data) need the `HOSTB [ts, pos, byte]` bus and a MEMIO row
  family, as designed in README §14.2.  Not built here.
* **Register space (space 6)** and the state-side join (`HOSTO` → state tables).
* The semantics of each host function, storage, receipts, gas accounting: state side.

## 4. Files touched

New Lean: `HostChip.lean`, `HostCheck.lean`, `StepHost.lean`, `Main/RowHost.lean`; `WasmBase.lean`
and `Tool.lean` extended.  New Rust: host trace generation and tamper cases in `src/{tracegen,main}.rs`.
New test programs in `programs/{wasmasm,refinterp,gen}.py`, harness branch in `run_kat.sh`.
`wasmBaseAir` (the already-proved AIR) is unchanged; the host AIR is a separate value.
