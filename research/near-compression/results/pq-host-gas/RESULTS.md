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

`wasm_base_sound_host` is not yet a finished theorem.  The two pieces named in the previous version
of this section are now **proved** (lane `lane/wasm-hostrow`):

### 3.1 Piece 1 — the HOST row's `RowSpec` (`WasmBase/Main/RowHostSpec.lean`)

* `host_inters_state` / `host_inters_stk` — the HOST table's STATE and CH interactions, by direction.
* `argMsg` / `wordMsg` / `argRaw` / `wordRaw` — the row's argument and result messages;
  `host_rawCons` / `host_rawProd` / `host_row_cons` / `host_row_prod` — the row's CH receive/send
  contents (`rowCons`, `rowProd`).
* `RelW.size_bound` / `RelW.size_lt` — the stack of a `RelW`-related state is `< 2^28 + 2^16 < p`.
* `host_arg_slot` — the `j`-th argument sits at stack slot `size − np + j`.
* **`host_arg_view`** — piece 1(a): a live argument message is the live stack message the Wasm side
  sent (one of `stackView`).
* **`host_word_is_resp`** — piece 1(b): the produced message is `enc 0 (size − np) (.i64 w) ts`,
  where `w` is the response's result word (`HostOK.word`), using `host_rb_limb`.
* `HostRowSpec` / `host_rowspec` — the trace-level packed predicate (activity, `np`/`nres` fields,
  `cons`/`prod`, and the response binding of `st`/`ar`/`g_after`/word).
* `nres_from` — `nres = (1−st)·ar` from the field equation for bit `st`, `ar`.

### 3.2 Piece 2 — the bus decomposition (`WasmBase/Main/ExecHost.lean`)

* `host_air_len`, `host_air_append`, `host_air_get`, `host_air_22/23/24` — the table layout.
* `host_msgs_air` / `host_occs_air` — every bus and the occurrence list split as
  `wasmBaseAir ++ (HOST ++ HOSTO ++ HOSTT)`.
* `msgs_state_host` / `msgs_ch_host` — the STATE and CH decompositions in the shape of
  `Exec.msgs_state` / `Exec.msgs_ch`.
* `rowMsgs_host_state`, `host_part_state_T/F` — the HOST rows' STATE send/receive.
* `host_part_nil_env` — the oracle (23) and cached host table (24) carry no STATE/CH interaction.
* `host_part_ch_recv` / `host_part_ch_send` — the decoded HOST CH messages are `rowCons`/`rowProd`.
* `HostTraceOK`, `host_part_ch_recv_active`, `host_part_ch_send_active` — the same restricted to
  **active** HOST rows under the trace-level side condition that inactive rows carry no CH message.
* `host_arg_stack` / `host_word_stack` — piece 1 at the trace/`RelW` boundary.

### 3.3 The remaining step: the segmented induction

`exec_of_rows` (and hence `wasm_base_exec`) has **not** been re-run for `wasmBaseHostAir`.  Doing so
requires (i) `HostChipFacts`, the `ChipFacts` analogue with table 22's row facts given by
`host_rowspec`, and (ii) threading `S_seg`/`segb` through the induction: each base row keeps the
segment, each HOST row restarts it via `StepHost.host_seg` / `Main.Host.host_row_seg`.  The final
statement then reports the last segment rather than the global `R·S_final + g = g0`, exactly as
`exec_of_rows` already does for one fixed segment.

**A real constraint gap found while doing piece 2 — since CLOSED.**  The HOST row's CH receives
are counted with `pf j`, not `act·pf j`, and `Host.constraints` had no `act`–`pf` link, so an
**inactive** HOST row (`act = 0`, `pf 0 = 1`) still emitted count-1 CH receives.  The base
`ChipFacts.inactive` premise therefore did not hold for table 22.  Fixed by commit
`edae7a53d` (option 1 below), which adds to `Host.constraints`:

```
(1 − act) · pf j = 0   (j = 0, 1)        (1 − act) · nres = 0
```

so an inactive row emits nothing and `HostTraceOK` follows from `Holds` alone.  Note the
direction: `act·(1 − pf j)` is **wrong** (it would force active rows to have `pf j = 1`, but an
argument may be absent and an aborting call has `nres = 0`); that form failed the KAT on 4 host
programs before being corrected.

`wasm_base_sound` is unaffected by this (it uses `wasmBaseAir`, whose tables are untouched).

### 3.4 The consequence of the gating is now proved

`Main/HostChipFacts.lean` proves `host_row_inactive_emits_nothing`: on an inactive HOST row the
row's `cons` and `prod` are both empty, so every CH interaction of that row has count 0.  That is
the **table-22 instance of `ChipFacts.inactive`**, i.e. the premise `Exec`'s bus decomposition
needs, and it now follows from `Holds` plus the gating constraints rather than being carried as a
hypothesis.  Axioms: `[propext, Classical.choice, Quot.sound]`.

What is still not done for `wasm_base_sound_host` is only the segmented induction itself:
`HostChipFacts` now has its inactivity field, but the `Exec` re-run still has to thread
`(S_seg, segb)` through `IH` (each base row keeps the segment; each HOST row restarts it).

## 4. Verification

```
HEAVY_MEM=16G taskset -c 8-11 lake build WasmBase wasmbase-tool
  -> Build completed successfully (123 jobs)
#print axioms wasm_base_sound / wasm_base_exec / exec_of_rows / host_row_seg / host_rowspec
  / host_arg_view / host_word_is_resp / host_r16_sound / host_rb_limb / host_msgs_air
  / msgs_state_host / msgs_ch_host / host_part_ch_recv / host_part_ch_send / host_arg_stack
  / host_word_stack
  -> ⊆ [propext, Classical.choice, Quot.sound]
grep -rn '\bsorry\b' WasmBase/                      -> empty
grep -rn 'native_decide|implemented_by|^axiom' WasmBase/  -> empty
make pin-check  -> passes (exit 0)
bash research/near-compression/native/wasm-base/run_kat.sh /tmp/katrun_hostrow 8 64
  -> KAT: 77 passed, 0 failed
```

