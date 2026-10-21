# pq-hch: the CH-bus permutation for the host AIR is proved

Lane `lane/pq-hch` (from `main` @ `f51c8563c`), 2026-10-21.  ~1 day.

**This closes the last gap of the Wasm join's bus side** (`docs/HANDOVER.md` §"The segmented induction
and `wasm_base_exec_host`", row `hch`).  `wasm_base_exec_host` (`Main/SegHarness.lean`) takes its two
bus premises `hst`/`hch` as hypotheses; both are now theorems about `Holds`.

## 1. What was actually open

The HANDOVER said "~30 lines", and the *reasoning* was indeed small, but two things were missing that
the estimate did not account for:

1. **`HostTraceOK` had no derivation from `Holds`.**  `Main/ExecHost.lean` defined the predicate and
   used it in `host_part_ch_recv_active`/`_send_active`, but nothing supplied it; the gating
   consequence existed only as `host_row_inactive_emits_nothing` (which gives `rowCons`/`rowProd`,
   not the raw `pf j`/`nres` counts `HostTraceOK` quantifies over).
2. **The CH bus is not the STATE bus.**  On the true side `msgs_ch` places the memory block **after**
   the instruction rows and the HOST block after that; on the false side the drain block sits between
   the instruction rows and the HOST block.  So even with the HOST block in active-row form, reaching
   `actListHost`'s `flatMap` needs one association swap per side.  `List.flatMap_map` does not relate
   these shapes; `perm_mid` (a private `perm_append_comm` + `append_right`) does.

## 2. What landed

`WasmBase/Main/HostChipFacts.lean`:

| theorem | meaning |
|---|---|
| `host_row_inactive_counts` | the raw form of the gating consequence: inactive HOST row ⇒ `pf j = 0` (all `j < nArgs`) and `nres = 0` |
| `host_row_inactive_emits_nothing` | renamed body on top of the above (`rowCons`/`rowProd` empty) — statement unchanged |
| `host_trace_ok` | **`HostTraceOK tr pub` from `Holds (wasmBaseHostAir …) pub tr`** — no extra premise |

`WasmBase/Main/HostBus.lean`:

| theorem | meaning |
|---|---|
| `hostActRows_flatMap` | `hostActRows.flatMap f = range(height 22).flatMap (if rowAct then f else [])` (generic in `f`) |
| `hostActRows_prod` / `hostActRows_cons` | the HOST CH block in active-row form (`wordMsg`/`argMsg`), derived from `host_row_prod`/`host_row_cons` |
| `actListHost_flatMap_prod` / `_cons` | `actListHost`'s CH block splits into instruction rows ++ HOST rows |
| `perm_mid` | `(P ++ (M ++ S)).Perm (M ++ (P ++ S))` |
| `perm_ch_host` | the association step: raw CH order ⇒ `actListHost` order, one swap per side |
| `ch_raw_host` | the host AIR's CH bus, decoded, in the right-associated `I G B A M H` / `R F A D H` shape (`I` = initRaw, `G` = glob, `B` = budget, `A` = instruction rows, `M` = memRaw, `H` = active HOST rows, `R` = result, `F` = finRaw, `D` = drain) |
| **`host_hch`** | **`hch` for `wasm_base_exec_host`**, discharged from `Holds` + `ChipFacts` + `PubOK` (plus the base AIR's `Holds` for the classic decomposition) |
| `host_buses` | `hst ∧ hch` as one corollary (`host_hst` + `host_hch`) |

The free `init`/`fin` blocks are the boundary's, which is the canonical and the only choice that
keeps the statement honest: `init = initRaw ++ globRaw ++ budRaw ++ memRaw`,
`fin = (result ++ finRaw) ++ drainRaw`.

## 3. Axioms and checks

* `#print axioms`: `host_hch`, `host_buses`, `host_trace_ok`, `host_row_inactive_counts`,
  `ch_raw_host` — all `[propext, Classical.choice, Quot.sound]`; `perm_ch_host` and `perm_mid` are
  `[propext]` only.  No `sorry`, `axiom`, `native_decide`, `implemented_by` in either file.
* `lake build` (whole `WasmBase` + `wasmbase-tool`, 138 jobs): green.
* KAT: **88/88** (`research/near-compression/native/wasm-base/run_kat.sh`), python ref = Lean spec =
  Rust trace + AIR pre-check.  The tool was rebuilt (the lane changes no table, but the rule stands).
* A standalone `example` restating `wasm_base_exec_host`'s `hch` parameter and proving it with
  `host_hch` typechecks, so the statement shape is verified against the consumer, not just by eye.

## 4. What this does *not* close

`wasm_base_exec_host` is still parameterised by

* `hrows`/`hrows2` (`RowFactsSegMap`/`RowFacts2` per action row) — per-row assembly from
  `ChipFacts.rows` and `host_rowspec`, plus the per-row `hstepgas` supply from `HostOK`/`HostResp`;
* `hlen` (`actListHost tr pub).length < 2 ^ 28`), `hfee`, `hinit`, `h0`.

None of those is a bus fact, and none is changed here.  The remaining work before a
`Holds`-only `wasm_base_exec_host` is the instantiation layer, which is `Exec.lean:wasm_base_exec`'s
~160-line body re-done for the interleaved list (`Host=`/`hstepgas` per HOST row).  `hch` was the
only item in the HANDOVER's `hch` row and is now proved.
