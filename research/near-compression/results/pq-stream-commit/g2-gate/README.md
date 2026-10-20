# G2 gate — real-settings chain + FINAL + V_d

Lane `lane/pq-stream-commit`. Circuit `lane/pq-recursion-sha384` @ `9159123be`; fast CPU prover
`lane/pq-cpu-prover` @ `6134476fc`; streamed commitments from this lane's overlay.

Run: 2026-10-19 15:01–15:47 UTC, 24 threads, peak RSS 17.15 GB. Log: `run.log`. Proofs:
`L1..L5.proof`, `FINAL.proof`. Hashes and gate markers: `MANIFEST.json`.

## Gate criteria (user-defined 2026-10-19)

| # | criterion | result |
|---|---|---|
| 1 | real-settings FINAL bytes ≤ ~296 KB | **293,077 B** — PASS (+6,923 B under 300 KB) |
| 2 | V_d accepts the FINAL under the pinned program | PASS (level 6, program 125,550 rows) |
| 3 | forged verify-nothing FINAL rejected with the program check (and accepted without it) | PASS, control live |
| 4 | the chain reproduces on a clean deps setup with identical proof sha256s | `reproduce.sh` + `MANIFEST.json`; independent re-run outstanding |

## Settings

* 268-bit target = 236 query bits + z = 32 wide-PoW; 42-byte digests; coset leaves; ×15; every
  lever; `m = 64` with kernel-proved O-2 certificates only (`NEARPROOF_DKT_EXCLUDE`).
* Parent (penultimate) shape: `n_stack 18`, `k 4`, `log_blowup 7`, `k1 2`, `log_final 6`,
  queries `[44, 35, 27, 23]`.
* FINAL shape: `n_stack 18`, `k 4`, `log_blowup 7`, `k1 1`, `log_final 7`, queries `[41, 38, 29, 23]`.
* NvAir: 72 columns, 48 interactions/row, degree 9, committed heights
  `[262144, 1048576, 128, 65536]`.

## Chain and convergence

```
L1_PROOF_BYTES total=288297   program_rows=7634
NV_G2_ANCHOR L2: anchor level M = 1 (child bound by its root = C_M)
L2_PROOF_BYTES total=357805   program_rows=112994
NV_G2_ANCHOR L3: anchor level M = 2 (child bound by its root = C_M)
L3_PROOF_BYTES total=364283   program_rows=129966
NV_G2_ANCHOR L4: anchor level M = 3 (child bound by its root = C_M)
L4_PROOF_BYTES total=362939   program_rows=125550
NV_G2_ANCHOR L5: anchor level M = 3 (child bound by BIND)
L5_PROOF_BYTES total=364577   program_rows=125550
NV_G2 converged: 5 levels, 1 bound by BIND, anchor M = 3
```

The tight-height floor did its job: L2 and L3 were raised (`natural -> floor`), L4 and L5 fit the
same floor, so the program converged at 125,550 rows and L5 switched from anchor to BIND. Only the
FINAL proof is transmitted (293,077 B); L1–L5 are intermediate.

## FINAL

```
FINAL_SUMMARY cols=173 opened=291 interactions=30474496 L=25 cells=107283584
FINAL_PROOF_BYTES total=293077 gkr=32408 relations=24292 stacking=6832 whir=229346
FINAL_SOUNDNESS total=268.2 logup=323.4 proximity=281.6 query=268.2
FINAL_VK_REGIMES rounds all O2, q=[41,38,29,23]
FINAL_RESOURCES wall_s=441.4 peak_rss_gb=13.98 program_rows=125550
```

## V_d

```
NV_VD final accepted: level 6, pinned program 125550 rows
NV_VD claimed statement digest [17732126303648949035, ...] (app public values [[0, 1, 2178309]])
NV_VD wrong claim rejected: statement digest differs from the claim
NV_VD wrong level (5) rejected: level 6 != pinned 5
NV_VD check_final_program accepts the honest final
NV_VD forged final (776 rows) accepted without the program check, rejected with it:
      final program openings differ from the pinned program
```

## What this does and does not establish

**Establishes:** the G2 binding design works at real PQ settings end-to-end — cached program
commitment, anchors while heights change, BIND once converged, a single-commitment FINAL pinned by
V_d, and a live forgery control. 293,077 B is a **measured** final, not a model.

**Does not establish:**
* 1 Pgas or a NEAR chunk. The app is the fib fixture; this measures the recursion tail only.
* The interaction-count path: `max_interaction_count` stays 2^28 here, and the NV circuit's own
  AIRs fit it. The D1-class base needs 2^30 (see `tools/d1-pq-envelope`).
* Byte-identity from a clean rebuild. That is criterion 4 and needs an independent run.

## Known risks

1. **The NvAir 2^18 margin is thin and real.** This run needed 125,550 program rows; a paired
   run (`pq-cpu2/ckpt/chainA`) failed with `NvAir: 262572 rows exceed 2^18`. The model predicted
   256,031 with 2.3 % headroom, so model-vs-measured is ~2.5 %, not the 0.2 % previously claimed.
   Any added program rows (a wider app table, extra checks) can push it over and cost L 24 -> 25.
2. **293,077 B is 5,600 B above the earlier 287,477 B** provisional measurement (that one ran with
   `bind = false`). The margin to 300 KB is 6,923 B, i.e. 2.3 %.
3. **Cost:** the chain is 46 min wall on 24 threads; the FINAL alone is 441 s and 14 GB.

## Reproduce

```sh
research/near-compression/results/pq-stream-commit/g2-gate/reproduce.sh <fresh-deps-dir>
```

Needs network for the pinned upstreams, the DKT certificate files of `lane/pq-dkt-verify`
@ `fb0efdb11` (or `CERTS=`/`EXCL=` copies with the recorded hashes), ~60 GB RAM, 24 threads.
It sets up the trees, builds, runs the chain, then compares every proof SHA-256 and every
required log line against `MANIFEST.json`.
