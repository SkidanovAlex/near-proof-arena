# Lane `lane/v3-elab-budget` — elaboration budget of the D0a certificate closure, log

Worktree `/data/illia/nearproof-wt/v3-elab-budget`, branch `lane/v3-elab-budget` from main `69ae7bc2`,
merged with main `ef23e4b3` (= `50f26055` for every formal file: lane/v3-model-split, closure 4,004
modules).  Goal: cut the judge-style serial elaboration of the certificate closure
(`nearV3_admission_final`, `zk-formal/scripts/judge-time.py`) by ≥ 30 % and reduce the lean4lean peak,
by proof-only changes (statements unchanged, `TypeHashes` 0 missing / 0 changed). CPUs 10-15, 26-31.

## 2026-10-14

### Where the time went (profiles, single core)

`codec_int` (`Render/CodecDefs.lean`), used by every row case of `CodecHeader` (4 cases),
`CodecRecInt` (21) and `CodecEndInt` (23) — 38 % of the closure.  Profile of one header case
(`hdr_int`, p = 1; 96 s): `simp` 60 s, kernel 20.5 s.  The macro

1. runs one `simp only` (~200 lemmas) per constraint (239 per case): each call rebuilds the simp set,
   re-unfolds the row table (`hdrA`/`recA`/…) and re-evaluates `lookup` (a `foldl` over ~110 pairs) for
   every cell occurrence;
2. tries `simp [modE, isZ]; done` (full default simp set) on every constraint to detect the 8 `modE`
   ones — ~11 s per case of failed `simp`;
3. unfolds `zev` with its `rfl` equations (`zev_c`, `zev_mul`, …, `zev`): the kernel then re-checks each
   rewrite by unfolding the structural recursion of `zev`.

### `codec_fast` (new `Render/CodecFast.lean`, `Render/CodecIntList.lean`)

Same theorems, same statements; `CodecHeader`/`CodecRecInt`/`CodecEndInt` call `codec_fast` instead of
`codec_int` (which stays in `CodecDefs`, unchanged).

* `CodecIntList`: `cIntT`, the 231 non-`modE` constraints with their index in `constraints`, written
  with the column builders evaluated (`.col 2 false` for `c kR`; `sub` and `MA` kept so the residual
  goals have `codec_int`'s shapes).  Generated from `constraints` by a `#eval` printer (scratch) and tied
  to it by `int_of_cInt : AllI Z cIntT → ∀ e ∈ constraints, e ∉ modE → zev Z e = 0`, proved once (the
  239 goals of `constraints` by `AllE` unfolding; the 8 `modE` ones by `mem_modE`, the others by
  `List.mem_of_getElem? rfl` into `cIntT` — so a wrong table cannot type-check).  `AllI` tags each
  conjunct with its index (`IdxP i _`, a structure so tags never unify across indices).
* `cdc_rows`: the row tables of `hcur`/`hnxt` are unfolded once (one `simp … at hcur hnxt`), then each
  of the 91 + 91 cells is read once into `hc_i : Z.cur i = vᵢ` / `hn_i`, by `lookup_of_lastFind0` with a
  kernel-evaluated `rfl` on `lastFind` — it compares column literals only (`Nat.beq` on literals); the
  cell values are carried as data and never reduced (no `Nat` literal against free variables: the
  lean4lean/nanoda pitfall of v3-recheck is avoided).
* `cdc_allsimp`: ONE `simp` over the whole conjunction `AllI Z cIntT` with the cells and non-`rfl`
  `zev` equations `zq_*` (`(rfl : _).trans rfl`, so simp uses them as propositional rewrites and the
  kernel checks rewrites, not `zev` unfolding); constraints that vanish identically disappear.
* `cdc_dispatch`: each residual `IdxP i Q` is closed by `codec_int`'s cascade (`cdc_cascade`, same 19
  alternatives in the same order), trying first the alternatives recorded for index `i` (`cdcPref`,
  recorded with a scratch-instrumented run of all 48 cases; each must close the goal, else the whole
  cascade follows — the table only orders the search).

Single-core, same CPU, sequential (`lake env lean`, user s):

| module | `codec_int` | per-goal facts (v1) | + indexed cascade (v2) | `codec_fast` |
|---|---|---|---|---|
| `CodecHeader` | ≈ 380 | 61 | 56 | **26** |
| `CodecRecInt` | ≈ 1,350 † | 430 | 400 | **118** |
| `CodecEndInt` | ≈ 1,620 † | 460 | 408 | **108** |

† judge-time baseline (`69ae7bc2`, contended).  Instrumented split of v2 (`CodecRecInt`, serial):
per-goal `simp` 167 s of 292 (34 ms × 4,851 calls — mostly simp-set construction), row reading 32 s,
cascade 14 s; hence the single-pass `cdc_allsimp`.  Peak RSS of one `lean` run: `CodecRecInt` 7.4 GB →
3.3 GB, `CodecEndInt` 7.7 → 3.6 GB, `CodecHeader` 2.3 → 1.5 GB.

### `NearAirCheck` (g = 2 only on the certificate path)

New `Assembly/NearAirCheckG2.lean`: `nearAirV3_wf`, `nearAirV3_air_wf` (moved verbatim) and the new
`nearAirV3_npOkPg_g2` (the `g = 2` case).  `NearAirCheck` imports it and keeps `nearAirV3_npOkPg`
(∀ g ∈ [1, 3]; the g = 2 case by the lemma); `NearAdmission.nearAirV3_npOkPg_2 := nearAirV3_npOkPg_g2`;
`NearAdmission` and `ExtractV3` import `NearAirCheckG2` instead of `NearAirCheck`, which leaves the
certificate closure (still built: `V3.Integration`, tests).

### `Render.Ups.GWalk`, `Render.Ups.GRows`

* Both ran `ups_ev [hC, hD] <;> cellsimp <;> …` per constraint (≈ 45 per theorem): ~250-lemma simp
  set rebuilt per goal, each cell `WC`/`VC`/`QC` re-evaluated per goal (`cellsimp` 313 ms per call in
  `GWalk`).  New macros `walk_all` / `rows_all`: unfold the constraint list into a conjunction, run
  `ups_ev`, `cellsimp` (and `wred`) once over it, split, then the original closing tactics per goal.
* `GWalk.wclose`: the cascade is reordered by measured cost — `(apply cast0; with_reducible rfl)` first
  (the full `rfl` failed in 83 ms on 179 goals; kept as a late fallback), `(wmode t', hm2 <;> wfin)`
  last (it closed none of the 330 goals and failed in 312 ms each).
* `GWalk` 288 → 122 s, `GRows` 118 → 33 s (user, single core).

### Not done (measured, left for later)

* `Render.Node.Links` (≈ 200 s): the cost is spread over the per-goal structural case split
  (`rcases nv` after the 56-way constraint split, 6,272 goals) and the `try simp … at hf` eliminations
  (S11–S14 ≈ 75 s serial); the fix is to split on the node shape once per theorem before the
  constraint split — a larger restructuring of `lnk3_tac`.
* `GFields`, `GFieldSucc`, `GWindowFlow`, `GDig`, `GMemRow` use the same per-constraint `ups_ev`
  pattern as `GWalk`/`GRows` (≈ 120 s together); `walk_all`-style macros would apply.
* `GPlan` (`decide +kernel` table checks), `FourWalk`.

### Final measurement (judge-style, `judge-time.py`, single core, concurrent runs)

Both runs at the same time, each serial `lean -o` per module, baseline on CPU 12 and after on CPU 13
(HT siblings 28/29 idle), same warm trusted `.olean`s; sources from snapshots (`JT_SRC`): baseline
= main `ef23e4b3` (formal files identical to `50f26055`, 4,004 modules), after = this branch at
`fdde7d77` (4,006 modules: + `CodecFast`, `CodecIntList`, `NearAirCheckG2`, − `NearAirCheck`).  The
last module, `NpUdrStarkV2.Certificate`, now imports the judge-generated `ArenaExpectedInst` (native
route, model-split) and cannot be elaborated by `judge-time.py`; it is excluded from both (≈ 1 s).

| | modules | seconds (single-core) | ≥ 10 s modules |
|---|---|---|---|
| main `ef23e4b3` | 4,003 | **9,100** | 90 (5,822 s) |
| `lane/v3-elab-budget` | 4,005 | **5,953** (−3,147 s, **−34.6 %**) | 92 (2,585 s) |

The 3,995 modules common to both and unchanged: 5,354 s vs 5,488 s (+2.5 %: the after run was
slightly more contended — builds/rechecks ran on 10-11, 14-15, 26-27, 30-31 meanwhile), so the
saving is, if anything, understated.  (The first baseline, main `69ae7bc2` on CPU 10 next to my
prototypes on its sibling, gave 10,564 s over 3,964 modules; not comparable, not used.)

| module | baseline s | after s |
|---|---|---|
| `Render.CodecEndInt` | 1,536 | 87 |
| `Render.CodecRecInt` | 1,390 | 105 |
| `Render.CodecHeader` | 393 | 27 |
| `Render.CodecFast` + `CodecIntList` (new) | — | 4.5 |
| `Render.Ups.GWalk` | 253 | 167 |
| `Render.Ups.GRows` | 101 | 33 |
| `Assembly.NearAirCheck` → `NearAirCheckG2` | 63 | 32 |

Top 10 after: `Node.Links` 184 · `Ups.GWalk` 167 · `CodecRecInt` 105 · `CodecEndInt` 87 ·
`Ups.GPlan` 80 · `MerkleRender.Local2` 56 · `Ups.FourWalk` 54 · `Node.FieldsB` 48 ·
`ProcPriorCodecAccumulatorRows` 48 · `Qv.Candidates.RawLocal` 48.  No module above 200 s (was 1,536).

### Rechecks (judge argv/env: `env -i PATH=<tc>/bin:… HOME=/tmp LEAN_PATH=<replay> LEAN_ABORT_ON_PANIC=1`, cwd `/tmp`, regular-file replay dir of the lake `.olean`s; pinned binaries `lean4lean` `bab5916d…`, `lean4export` `8c5d64ba…`, `nanoda_bin` `25906eb2…`)

| check | result | changed codec modules (after) | baseline |
|---|---|---|---|
| leanchecker, the 11 changed modules | all rc 0 | `CodecRecInt` 20 s, `CodecEndInt` 9 s, `CodecHeader` 6 s | `CodecRecInt` 232–260 s (v3-recheck) |
| lean4lean, all 4,002 zk/ReexecV3D0 modules (6 shards) | **4,002/4,002 accepted**, Σ 3,256 s | `CodecHeader` 5.9 s / **0.8 GB**; `CodecRecInt` 38 s / 0.66 GB (1,091 decls); `CodecEndInt` 18 s / 0.68 GB | `CodecHeader` 160 s / **13.6 GB** (re-measured on the baseline `.olean`s); `CodecRecInt` 589–705 s |
| lean4lean peak RSS over the closure | **6.9 GB** (`Extract.Ups.PlanDefs`, unchanged module) | | 13.6 GB (`CodecHeader`) |
| lean4export (`AdmissionV3 -- nearV3_admission_final`) | rc 0, 155 s, 6.9 GB, NDJSON 2.71 GB | | 107–141 s, 7.9 GB |
| nanoda (judge config) | **PASS**, `Checked 87031 declarations with no typechecker errors`, 604 s, 5.1 GB | | 1,148–1,485 s, 12.8 GB |

The kernel work shrank with the elaboration: the `zq_*` rewrites replace the kernel's unfolding of
`zev`, and the cell facts replace thousands of `lookup` evaluations.  No new `Nat` literal folding
against free variables was introduced (the cell reads compare column literals only; the `simp` sets
are `codec_int`'s minus the row/`zev` unfoldings); lean4lean and nanoda accept everything.

### Verification

* `lake build ZkFormal.V3.Integration` (all 4,106 targets) and every module imported by a test: ok.
* `TypeHashes` (main's script, type + definition-body fingerprints) over the certificate closure of
  main vs this branch (+ `NearAirCheck` from the `V3.Integration` build): 41,484 named constants
  (auxiliary `_proof_`/`_simp_`/`match_`/`eq_`/`_f` excluded), **0 missing, 0 changed**, 44 new
  (helpers: `zq_*`, `lastFind`, `lookup_*`, `AllE`, `AllI`, `IdxP`, `cIntT`, `int_of_cInt`,
  `cdcPref`, `cdcModE`, `mem_modE`, `nearAirV3_npOkPg_g2`, the macro declarations).
* `zk-formal/test`: 2,551/2,554 pass; the 3 failures fail on main too (`AuditHonestBalanceRcpt`,
  `AuditRenderV3RcptTables`, `AuditPackedPublic`, see v3-prune).  `AuditNearV3Admission` now imports
  `Assembly.NearAirCheck` (no longer reached through `NearAdmission`); its `#print axioms` outputs are
  unchanged.  `AuditAdmissionV3`, `AuditCodecRows`, `AuditUnfoldA7`, `AuditRcptRoutingQ` pass.
* No `sorry`/`axiom`/`native_decide`/`implemented_by`; no `import Lean` (the new tactics are
  `Init`-level macros).  The verifier-model closure (`NpUdrStarkV2.Model`, 90 modules) contains none
  of the changed modules (its native binary is unaffected).
* np-udr-stark-v2 re-vendored (`sync-lean.sh`): `dependency-locks/zk-formal.sha256` updated
  (4,002 candidate files), `lean-vendor` unchanged.  `make pin-check` ok.

### Notes

* `cIntT` is generated (scratch `#eval` printer over `constraints`); `int_of_cInt` re-proves its
  relation to `constraints`, so a stale table fails to build rather than weakening anything.
  `cdcPref` only orders the search.
* Judge-time measurements need otherwise-idle HT siblings: next to my prototypes on CPU 26, the
  first baseline ran 1.6× slower than the v3-prune numbers.
