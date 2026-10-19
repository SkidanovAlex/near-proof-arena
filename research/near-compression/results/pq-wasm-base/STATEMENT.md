# pq-wasm-base: the CODE table and its statement binding (decision (a), 2026-10-19)

This implements checkpoint decision (a). The CODE table is a **cached** trace. Its commitment
`code_root` is a statement component, and V_d recomputes it from the contract code. This closes the
code side of e2e gaps G3/G4: which code did the base proof execute?

## 1. What changed in the AIR (`wasm-base-v2`)

| | v1 | v2 |
|---|---|---|
| code records | public values (8 per record) + one BOUNDARY interaction and one multiplicity column per record | AIR `CODE` (table 12): columns `pc, op, h, fee, x0..x3` are a **cached** main trace; `mult` is in the common main; one FETCH receive `[pc, op, h, fee, x0..x3]` with count `mult` |
| public values | `8 + nloc + 8·ncode` | `8 + nloc` (`N, S, nres, rtag, r0..r3`, local tags) |
| vk | changes with every program (BOUNDARY width and interactions grow with `ncode`) | depends only on `nloc ≤ 64`; the CODE height is a proof value (`log_height`), not a vk constant |
| BOUNDARY | `3 + 2 nloc + ncode` interactions | `3 + 2 nloc` |

The Lean model (`WasmBase/Chips.lean`) is still the single source of truth. The exporter marks
CODE's first 8 columns as `"cached": 8`. The Rust `JsonAir` declares them through
`PartitionedBaseAir::cached_main_widths` and reads them with `PartitionedAirBuilder::cached_mains`.
The prover commits them with the device committer (`k_first`, ×15 domain, coset leaves) and passes
them as `CommittedTraceData`. The difftest accounts for the partition: the DAG's `part_index` 1
columns follow the cached ones. It passes with 416 points: 7,296 constraint values and 5,088
interactions agree.

## 2. The statement and V_d's check

Statement components of a base segment, as exposed by L1 in the statement digest:

* `code_root`: the base proof's cached commitment for CODE (`trace_vdata[CODE].cached_commitments[0]`);
* the public values `N, S, nres, rtag, result limbs, local tags`;
* `code_hash`: the receipt's contract code hash (sha256 of the code), bound to the receipt by the
  chunk/receipt side of the pipeline (outside this lane).

**`code_root` is a deterministic function of the code.** The canonical CODE matrix is computed as
follows:
1. Take `records = check(cfg, prepare(cfg, code), fn).records`; `wasmbase-tool prep` computes them
   with the same Lean definitions the proof uses.
2. Place the records in pc order.
3. Pad to the power of two `≥ max(4, ncode)` by repeating the last record (`tracegen::code_rows`).

`code_root` is the stacked commitment (`stacked_commit_odd`) of that 8-column matrix under the base
shape's parameters: `l_skip = 2`, the base `n_stack`, `log_blowup = 1`, `k_first = 1`, the ×15 odd
domain, 42-byte SHA-384 with coset leaves. It is computed by `code_root` in `native/wasm-base/src/main.rs`.

**V_d** (or the chain) does the following:
1. Gets the code for `code_hash` and checks `sha256(code) = code_hash`.
2. Computes `code_root(code)` once per contract and caches it by `code_hash`.
3. Checks it against the statement's `code_root`.

Nothing in the base or L1 programs depends on the contract.

`prove` performs this check after native verification and prints
`STATEMENT code_root <hex> code_hash <hex>`. Set `WASMBASE_WASM` to the code file so that `code_hash`
is computed.

## 3. Soundness: what the proof assumes, and the evidence

* **Lean.** The theorem `wasm_base_sound` takes one new hypothesis, `CodeOK X tr`. It says that every
  CODE row's record columns equal some record of the checked code. This hypothesis is exactly what
  V_d's root check gives under the binding of the commitment: an opening of a different matrix
  against the same root would be a collision. The rest of the proof, FETCH soundness
  (`Main.Lookups.looks_of`), is derived from `CodeOK` and `Holds`. The public-values hypothesis
  `PubOK` no longer contains records.
* **Tamper.** `logs/tamper-hashloop8.log` has 30/30 rejected. The new cases are:
  * `CODE.mult[0]+1`, `CODE.op[0]+1` and `CODE.h[0]+1`, rejected by the bus;
  * `CODE[pad row 54].x0+1`, a record no instruction fetches. The AIR holds and the base proof
    verifies, so only the `code_root` check rejects it. This shows the statement check is necessary.

## 4. Cost

* **Base proof.** At the small shape it grows from about 746 KB to about 972 KB, because of the extra
  round-0 tree openings (`logs/prove-*.log`). Base proofs are not sent to V_d.
* **Base per-op cost.** No change: the CODE table has one row per instruction of the code, not per
  executed op.
* **L1.** One more round-0 tree: about +80k program rows and +15.5k compressions at b = 1
  (pq-nv-preprocessed §4.2). This replaces the public-value design's ≈85–105 rows per record, so it
  pays for itself above about 800 instructions and removes the per-program vk.

## 5. Open

* The receipt → `code_hash` binding (chunk side of G3/G4) is assumed here.
* Code larger than one CODE trace (> 2^24 records) is outside D5 (`code < 2^20`).
* The tight-heights lever must stay off for the CODE commitment (pq-nv-preprocessed risk R5). The
  seg-v1 shape does not use it.
