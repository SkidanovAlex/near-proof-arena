# lane/v3-perf-design — performance-first design + CPU spike #1 (2026-10-14)

Deliverable: `docs/zk-formal/V3-PERF-DESIGN.md`; model `tools/perf-design/model.py`; spike
`tools/perf-design/wasmchip/` (standalone cargo workspace, path dependency on
`examples/np-udr-stark-v2/source`, read-only; lockfile copied from it; `--offline`).

CPU discipline: every build/benchmark under `nice -n 19 taskset -c 9,25`, `RAYON_NUM_THREADS=2`,
`CARGO_BUILD_JOBS=2`, `RUSTFLAGS="-C target-cpu=x86-64-v3 -C target-feature=+sha,+aes"` (the host cargo
config drops `.cargo/config.toml` rustflags, see `v3-prover-perf-2026-10.md`). CPUs 9,25 are shared with
the refreeze lane: **all timings contended, indicative only**.

## Inputs read
V3-D3A-STUDY (all), V3-D1-DESIGN, V3-D0-DESIGN (§5.5, §9), recursion-r1-cost §3–4, v3-prover-perf log,
np-udr-stark-v2 sources (air, aux, protocol, field, hash, lde, prover API), NearSpecV3 Wasm
(`FiniteWasm` gas analysis, `Prepare` PV86 config, `Machine` host costs), D3a workload raw data
(per-opcode aggregation below), research/hash-recursion README (git show, read only).

## Per-opcode mix (all 19,179 accepted D3 cases; aggregated from the study's raw JSONL)
489,090,891 WASM instructions + 74,839,024 charge points. local.get 22.04 %, i64.const 19.65 %,
local.set 13.32 %, br 6.85 %, br_if 6.84 %, i64.add 6.82 %, i64.sub 6.37 %, i64.mul 6.37 %,
i64.eqz 6.37 %, i32.const 1.05 %, i32.add 0.56 %, i64.extend_i32_u 0.48 %, i32.store8 0.47 %,
i32.wrap_i64 0.45 %, i64.ne 0.45 %, block 0.43 % (excluded from counts elsewhere), global.get 0.30 %,
call 0.27 %, i32.eq 0.25 %, rest < 0.15 % each.

## Spike #1 / #2 runs (raw: docs/e2e-results/v3-perf-design/spike1.log)
* `wasmchip run measured 65536 --prove --tamper`: 917,507 ops, 3.50 ops/row, 10.6 main cells + 5.1
  fractions per op; prove 17.8 s (104 M W_eq, Fp8/blowup 16/SHA-256 WH), verify ACCEPT; T1/T2 refused
  by the prover's AIR/bus checks; T3 16/16 bit flips rejected by the verifier. wall 66 s, RSS 1.0 GB.
* `run loadchain 16384`: 425,987 ops, 1.44 ops/row, 21.3 / 11.9 per op; prove 16.5 s; same checks.
* `run mem 65536`: 1,179,651 ops, 3.60 ops/row, 9.3 / 4.3 per op; prove 16.6 s; same checks.
* `bench-hash 256`: SHA-512 compression 9.0 M/s/thread; SHA-256 (SHA-NI) 38 M/s.
* `bench-commit 20 64 {1,2,4}` (2 threads): 21.7 / 40.0 / 151.6 ns per trace cell, hashing 68–78 %;
  1 thread at rate 1/2: 27.5 ns, hashing 62 %.
* `bench-ext` (1 thread): ext mul generic E=8/10/12 61/87/200 ns, Plonky3 Fp8 8.6 ns; fraction compute
  532/633/1391 ns.
* An earlier bench-ext run compared against Plonky3 with a base-embedded multiplier (unfair); fixed and
  re-run (second line in the raw log is authoritative).

## Model
`python3 tools/perf-design/model.py` — results quoted in the design §0/§7. Two corrections during the
lane: per-cell cost now scales with blowup; the in-circuit verifier of the distributed proof uses global
row-digest trees (one path per tree per query) — with per-GPU trees the compression tail was 1.1–1.5 s
and recursion exceeded base work for typical chunks.

## Round 2 (after user decisions P-PERF-6/7, P-RT-1' declined, P-PERF-1..5 adopted)
* Merged main 440655fa, later 86fab5fd (D1 phase 1).
* Spike 4 (`wasmchip run1`, `src/v1.rs`): v1 typed-operand chips, stack-temporary channels, timestamps `8·ts+k`
  with one RANGE-T (2^21) lookup per access, unaligned ld/st, call/ret (frame records in memory space 3), i64.div_u,
  memory.copy (bulk16), public binding of code / non-zero initial words / io. Six programs, all differential-equal
  to the reference interpreter (locals, full memory, gas), channel discipline asserted, honest proofs verify.
  Raw: docs/e2e-results/v3-perf-design/spike4.log (CPUs 9,25, contended).
* Forging prover `tools/perf-design/forge`: gen.sh copies the deployed prover source, patches env-gated hooks
  into prover.rs (skip global check and the final-FRI degree check; rewrite OOD quotient; balance finals) and
  checks verifier.rs byte-identical. F1–F5 and the SHA forgeries are all rejected by the verifier. The first
  forge pass hit the prover's final-FRI self-check (F2/F4 "refused"); the patch was extended and re-run.
* A first full run was stopped (by PID) to rebuild with the extended forge patch; spike4-run0 discarded.
* Spike 3 (`wasmchip sha 256|384`): two-round-per-row SHA-2 compression chips. First SHA-384 layout (σ as
  degree-3 bus messages, table degree 6) failed the honest ALI identity although the row and bus checks passed
  (SHA-256 passed); σ as committed limbs (degree 4) fixed it. Flag for the prover lane: possible completeness bug
  for wide high-degree interaction messages.
* Clean runs (CPUs 9-15,25-31, given by the coordinator after the D1 lane): docs/e2e-results/v3-perf-design/clean.log.
* Model: measured chip forms; SHA from measured layouts; adversarial = max-latency candidate (incl. contract
  loading, register copies, memory.copy); early PREP sub-proof; distributed L2/L3; L3 at rate 1/16; final at 1/32.
  Worst case 32 H200: 1.75 s after execution at 35 % of peak; ≥ 30 % needed for ≤ 2 s.
