# pq-nv-tape: the TAPE root to V_d, per-table height caps, the 2^30 LogUp budget

Lane `lane/pq-nv-tape`, from `main` @ `8412a9c2a`.  This is the Rust/recursion half of the join
(`results/pq-state-port/README.md` §2.2/§P4 and `JOIN-INTERFACE.md` §5 step 5).

Everything here is in the recursion patch stack
(`native/recursion/patches/openvm-recursion-*.patch`, `stark-backend-*.patch`).  No `spec/`,
`challenges/`, `oracle/` or pinned file changed; `make pin-check` passes.

## 1. The cached TAPE root reaches V_d  [measured]

**The gap.**  A cached table's root is bound to the base proof's transcript but is *not* one of
its public values.  The G1 statement digest hashed only `proof.public_values`, and V_d pins only
the vk, the program, the level and that digest.  So a final proof over a base whose TAPE (or CODE,
or a host-wire) table was anything at all verified.  That is exactly the hole
`pq-state-port`'s `tapeNet_canon` is written against.

**The change.**

| site | change |
|---|---|
| `nv/verifier.rs` | every cached commitment is loaded once in the preamble and, after the G1 statement digest, folded in with one Merkle-node compression (`Builder::node`, 8 + 2·42 B, one SHA compression).  With no cached commitment the chain is empty, so the statement is the G1 one unchanged. |
| `nv/circuit.rs` | `StatementClaim { public_values, cached_roots }`: the statement V_d checks, and `check_statement_claim`.  `check_statement` is `StatementClaim::new(..)` (the pre-P4 form). |
| `nv/vd.rs` | `verify_final_claim(setup, engine, &StatementClaim, proof, skip_program)`; `verify_final` is the empty-root form. |

**Why a node fold, not more statement bytes.**  An NV leaf job hashes exactly one block, and the
statement message is already close to 128 bytes (`[n_vecs, len.., flat..]`).  Appending an 18-limb
root made it 205 bytes = two blocks, which the SHA glue does not support (the second block's
padding is not modelled) — measured: `LogUp multiset equality check failed` on the statement job.
The node compression is the existing, tested single-block path, and it is a collision-resistant
binding: `d' = H(node_prefix || d || root)`.

**Order.**  The roots are folded in preamble order (AIR order, cached mains in proof order), which
is the order the program observes them, so there is no second place to get it wrong.

**V_d's claim.**  `cached_roots` is what the claim *says* the roots are.  For TAPE the state-port
side recomputes it from the claim's public messages (`tapeCanon`); the chain only ever carries a
root the base proof actually committed to, so a claim root that differs is rejected.

### Test `nv_tape_root_passthrough` (real chain: base → L1 → L2 → FINAL → V_d)

A `PreprocessedAndCachedFixture` child (one cached main — the TAPE shape):

* L1's in-circuit statement == `StatementClaim::digest()` ==
  `[4465200641357224649, …]`; it differs from the public-values-only digest;
* L2 re-exposes the same digest unchanged (passthrough), FINAL likewise;
* V_d accepts the chain with the TAPE root in the claim;
* V_d **rejects** a different TAPE root and the pre-P4 (public-values-only) claim, both with
  `statement digest differs from the claim`;
* a cached root tampered in the base proof is caught by the Merkle checks (127 failures).

### Inertness (the G2 gate's shape)  [measured]

For a child with no cached table and no height cap, the generated program is unchanged: the cap
check emits no instruction, and the root fold is a loop over an empty list, so the statement cells,
the SHA job and every later instruction are the ones the G1 code emitted.  `nv_statement_inert_without_cached_roots`
asserts the emitted program (8,018 rows for the small Fib fixture) exposes exactly
`statement_digest(public_values)`, with `StatementClaim::new(..).digest()` equal to it — the pre-P4
statement.  That, plus the gate pinning 2^28 (§3), is why the recorded G2 proofs stay valid (§4).

## 2. Per-AIR height cap `log_height <= maxLog_t`  [measured]

**The change.**  Three layers, all static (no rows):

| layer | change |
|---|---|
| vk | `PartitionedBaseAir::max_log_trace_height()` (default `None`) → `StarkVerifyingParams::max_log_trace_height`, so the cap is in the vk pre-hash.  `None` serialises as absent: upstream-shaped vks keep their bytes. |
| native verifier | `verify_proof_shape` rejects with `ProofShapeVDataError::LogHeightExceedsTableCap` — every backend user gets it, not just NV. |
| NV | `build_verifier` records the failure and refuses to generate the program, exactly like the existing LogUp count check (B2); both `log_height` and `maxLog` are vk constants. |
| V_d | `vd::check_height_caps`, called by `verify_final_claim`, against the pinned final vk. |

**Test `nv_air_height_cap`** (a `FibonacciAir` with a configurable cap):

```
NV_HEIGHT_CAP honest log_height=5 cap=5 accepted
NV_HEIGHT_CAP native rejected: Proof shape verification failed: Invalid VData: AIR 0 should have log_height <= 4 (its maxLog), but has 5
NV_HEIGHT_CAP cap is in the vk pre-hash; without it the same proof verifies
NV_HEIGHT_CAP NV program rejected: AIR 0: log_height 5 exceeds its maxLog 4
NV_HEIGHT_CAP NV program for the honest child: 8018 rows, identical with and without a cap
NV_HEIGHT_CAP V_d rejected: AIR 0: log_height 5 exceeds its maxLog 4
NV_HEIGHT_CAP uncapped Fib unchanged (8018 program rows)
```

The cap adds no rows and does not change the program (`instrs` equal with and without).

**Wiring `maxLog` into the ported tables** is the next step and is *not* done here: the
`pq-state-port` driver has `TableSpec::max_log`, and each table's AIR must return it from
`max_log_trace_height()`.  Until then the cap is `None` everywhere in the shipped programs.

## 3. `max_interaction_count` 2^28 → 2^30  [measured]

`params_from_env` (the production shape for every lane's proofs) now defaults to `1 << 30`;
`*_INTERACTION_LOG=28` reproduces the old value.  Test `nv_production_interaction_budget`:

```
NV_LOGUP default max_interaction_count = 2^30
NV_LOGUP logup_soundness 2^28=312.88 2^30=310.88 (delta 2.00)
NV_LOGUP queries unchanged: [77, 60, 49, 42, 36, 32]
```

`logup_soundness(2^30, 7, |Ext12|, 22) = 310.88` bits — **2 bits** below the 2^28 figure, and the
WHIR per-round query counts are identical.  This matches `tools/d1-pq-envelope/check.py` and
`docs/logs/d1-pq-envelope-2026-10-19.md`.  D1's N = 2^29.59 and D0a's 2^29.55 now fit.

`run_g2_chain.sh` / `run_stream_chain.sh` pin `INTERACTION_LOG=28` (their recorded setting), so the
G2 gate's keys and proofs are unchanged.

## 4. Tests and the G2 gate  [measured]

* Full fast NV suite: **70 passed, 0 failed, 4 ignored** (`cargo test --release -p
  openvm-recursion-circuit --lib nv::`, `--test-threads 8`, 700 s).  The 66 pre-existing tests pass
  unchanged; new: `nv_air_height_cap`, `nv_tape_root_passthrough`,
  `nv_production_interaction_budget`, `nv_statement_inert_without_cached_roots`.
* `g2-gate/MANIFEST.json` still verifies: all six proof SHA-256s and all ten required log lines,
  **0 mismatches** (checked by re-running the manifest comparison over the committed artifacts).
  The artifacts themselves were not regenerated — the changes are inert for that shape (§1
  inertness, §2 no cap, §3 gate pins 2^28), so their bytes legitimately stay the same.

## 5. Incidental fix: a fast-prover degree bound

`cpu-backend/src/fast/zc.rs` (the `pq-cpu-prover` overlay) sized its per-round scratch at 10 while
enabling the degree-aware path for `sp_deg <= 10`, and indexing `used_m[f][m]`/`tot[x]` for `m, x`
up to `d`.  A degree-10 AIR therefore panicked (`index out of bounds: the len is 10 but the index is
10`) on this machine.  NvAir's degree grows past 10 as the program part grows, so the TAPE chain
hit it.  Fixed by sizing the scratch arrays at `MAX_DEG = 32`; the values are unchanged (it is the
same finite-difference / Horner evaluation with room to run).

## 6. What remains

* **Wire `maxLog` from the ported tables**: `pq-state-port`'s `TableSpec::max_log` →
  `JsonAir::max_log_trace_height`.  This worktree's deps tree is the recursion one; the port's own
  driver tree is `native/pq-state-port`.
* **Host-wire commitments**: they are cached mains like TAPE, so this lane's mechanism carries
  them with no further change — but they do not exist yet (`JOIN-INTERFACE.md` step 1–3).
* **Re-pin the G2 gate** only if a future change is not inert; `reproduce.sh` compares the hashes.
