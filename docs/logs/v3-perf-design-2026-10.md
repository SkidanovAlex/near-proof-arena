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
