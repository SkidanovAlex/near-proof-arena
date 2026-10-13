# lane/v3-prover-schedqv — honest scheduler / ChaCha / qv entries (np-udr-stark-v2, v3 D0a)

Base: `integration/prover-20261013b` (main + lane/v3-prover-trie).  Scope: `nearAirV3` tables
8 chacha, 9 rng, 10 shuf, 11 codec, 12 scandist, 13 proc, 14 mem, 15 cmp and 22 qv from a real
claim + witness (until now only from samplers).

## Entry format (stable; consumed by lane/v3-prover-prove `v3prove`)

`np-lean-sched-v3 <case_dir> <out_dir>` (Lean ground truth) and `npudr v3sched <case_dir>
<out_dir>` (Rust) write one file per table into `<out_dir>`, named as in `v3::TABLES` /
`v3prove`'s `<entries-dir>/<table>.json`:

| file | table | content |
|---|---|---|
| `codec.json`, `scandist.json`, `proc.json`, `mem.json`, `cmp.json` | 11–15 | the same JSON list of blocks, one per scheduler instance `τ = 0, 1, …` (main chunk, then one per implicit step), each a `sched::SchedIn` / Lean `NpSched.SchedInJ` object `{run, ids, allowed, params, present, vid, gb, fwd, ash, a0, prev_hash}` (`run` = `Gen.Run` with Lean field names) |
| `chacha.json` | 8 | `ChachaBus.laneReqs (bs.map run)` — list of `Chacha.Gen.Req` |
| `rng.json` | 9 | `ChachaBus.laneCalls (bs.map run)` — list of `Rng.Gen.Call` `{key, kstart, n}` |
| `shuf.json` | 10 | `ChachaBus.laneInsts (bs.map run)` — list of `Shuffle.Gen.SInst` |
| `qv.json` | 22 | `{walks, records}` (`qv::QvIn`, the `np-lean-render-v3 qv` input) |
| `summary.json` | — | counts and self-checks (Lean); not a table |

All of them are read by `npudr v3render <table> <file>` / `npudr v3check` unchanged (the
scheduler tables accept the block list, chacha/rng/shuf their lane lists, qv the object).

## 2026-10-13 — Lean ground truth `np-lean-sched-v3` (`conformance/SchedEntriesV3.lean`)

* Evaluates the `PriorCore` block construction of the completeness proof
  (`native_allocated_blocks_run` → `native_ordered_blocks_run` → `native_main_block` /
  `implicit_blocks_run`): per block `schedulerUpsertWitness ctx pre`, `pub = p.sched[τ]`
  (checked = `schedPub ctx`), `prior = readKey pre keyBwState`, `old = decodePrevious prior`,
  `run = ActualRun.run (input pub old) τ`, grants = `distributeEv` on `ProcActualInput.process`'s
  state, `vid = nativePriorIds (m.pre :: steps.pre) τ`, `fwd = fwdLinks (m.ctx k) out.outgoing`
  (main) / `[]`, `output = ProcPriorCodecGen.codecRows …`.  qv: `qvNativeWalks` /
  `qvNativeRecords` of `(m.pre, mainValues, steps.pre)`.
* `render <table> <case>` renders tables 8–15, 22 from the native blocks with the proof's trace
  definitions (`codecCell (bs.map blkOf)`, `ProcScanDistPhases.trace`, `procTraceV3`,
  `MemConcatCells.trace`, `cmpTraceAligned (requests bs)`, `mixedTrace`), row lists tabulated
  once; equality lemmas `codec_twin`, `ssd_twin`, `proc_twin`, `mem_twin`, `cmp_twin`, `qv_twin`.
* `Conformance/SchedJson.lean`: the JSON mirrors / twins of `RenderV3Sched.lean` moved into a
  library module (shared by both exes; `np-lean-render-v3-sched` unchanged in behaviour).
* `summary.json` self-checks per block: the canonical prior-state rebuild of `SchedInJ` has the
  same `allowances` / `a0Canon` / sanity hash as the real prior state, grants = `distRows` gb,
  view codec comparisons = `output.cmps`.  All pass on the 81 fixtures (64 public-d0a + 17
  fixtures-extra).
* Fixture coverage: 70 fixtures 1 block / 0 requests, 8 with 2 blocks (implicit steps), 3 with
  one bandwidth request (no round shuffles beyond 1 element); n = 4 or 5 shards; prior state
  always present.  qv: 3–7 walks, 0–4 records.
