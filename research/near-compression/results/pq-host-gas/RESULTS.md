# pq-host-gas: the per-segment gas invariant, and the host interface

Lane `lane/pq-host-gas` (from `main` @ `8412a9c2a`), 2026-10-20.
Implements the gas generalisation of `JOIN-INTERFACE.md` §4.2a: the simulation relation no longer
claims `R·S + g = g0` globally, but only **between host calls**.

## 1. The new invariant

`WasmBase.RelW` gains two segment fields (the rest of the relation is unchanged):

```
gas    : X.R * (S - S_seg) + s.gas.g = segb
segLt  : S_seg ≤ S
segbLt : segb < 2 ^ 64
```

`S_seg` is the instruction counter at the last host boundary and `segb` the budget the state side
fixed there.  A host call resynchronises `g := remaining` and **restarts** the segment at
`S_seg' := S + fee`, `segb' := g_after`: the invariant at the new segment is `0 + g_after = g_after`.

`Rel` takes `S_seg segb` as explicit arguments (it is a bare existential over the frame data).

### Recovery of the old form (mechanical updates stay small)

| lemma | statement |
|---|---|
| `RelW.gas_global` | `RelW … 0 X.g0 → X.R * S + s.gas.g = X.g0` |
| `Rel.gas_global` | the same for `Rel` |
| `RelW.of_global` | the converse packaging at segment `(0, g0)` |
| `RelW.charge_ok` | `R·(S+fee−S_seg) ≤ segb → R·fee ≤ s.gas.g` (the old `eligible` form) |
| `RelW.step_gas` | a step that keeps the segment and charges `R·fee` |
| `RelW.gas_call` / `seg_mul` | the `call` step (`fee + prologue`) |
| `RelW.gasSeg` / `GasSeg` | the triple as a standalone predicate |

Every step lemma keeps its old statement shape, with `R·(S+fee) ≤ g0` uniformly replaced by
`R·(S+fee−S_seg) ≤ segb` and the conclusion `R·(S+fee)+g' = g0` by `R·(S+fee−S_seg)+g' = segb`.
`wasm_base_sound` is **unchanged and still proved** (its `exec_of_rows` is instantiated at
`S_seg = 0`, `segb = g0`).

## 2. Host boundary

`StepHost.lean`:

* `step_host_ok / step_host_abort` (already present) — the spec step from the oracle.
* `step_host_ok_seg / step_host_abort_seg` — **the segment is re-established**: with `status` and
  `g_after` from the response, the successor triple is `(S + fee, g_after)` and the invariant is
  `0 + g_after = g_after`.
* `host_seg` — the pure gas fact `GasSeg R (S+fee) g_after (S+fee) g_after`.

`Main/Host.lean` (new): `HostAnswer` (`status`, `results`, `gAfter`, `bytes`), `HostResp`
(well-formed responses: `gAfter < 2^64`, `status ≤ 2`), `HostOK` (per-row binding of the response
to the HOST row's `st`, `g_after` limbs and `ar`), `runHost` (= the spec `run`, with the response
fixed), `HostOK.gAfter_lt` (the 64-bit side condition from `HostResp`), `host_next_seg`, and
`host_row_seg` (the HOST row's successor segment from `host_rowfacts` + `HostOK`).

## 3. What is not done

The **top-level** `wasm_base_sound_host` is not stated as a finished theorem.  Two pieces are
missing and both are `RowSpec`-level work, not gas work:

1. the HOST row's `RowSpec`: turning its `stkRecv`/`stkSend` occurrences into "the consumed
   arguments are live stack messages" and "the produced result words are the response's";
2. the bus decomposition of `Exec.lean` repeated for `wasmBaseHostAir` (tables 22/23/24, outside the
   proved `1..14` chip range and the `0/15..21` fixed range), plus threading `S_seg`/`segb` through
   the induction (each HOST row changes the segment; every other row keeps it).

`Main/Host.lean`'s header records the exact statements so the composition (JOIN-INTERFACE §4.3) can
be written against them.

## 4. Verification

```
HEAVY_MEM=16G taskset -c 8-10,24-25 heavy lake build WasmBase wasmbase-tool
  -> Build completed successfully (120 jobs)
#print axioms wasm_base_sound / wasm_base_exec / exec_of_rows / RelW.gas_global / Rel.gas_global
  / step_host_ok / step_host_ok_seg / step_host_abort_seg / host_rowfacts / host_row_seg
  -> [propext, Classical.choice, Quot.sound]   (host_seg / host_next_seg: [propext])
grep sorry|native_decide|implemented_by WasmBase/  -> CLEAN
make pin-check  -> passes
bash native/wasm-base/run_kat.sh /tmp/katrun_pqhg2 8 64
  -> KAT: 77 passed, 0 failed
```
