# Lane `lane/v3-d0a-challenge` — finish the D0a challenge, add the D0a tier to `near-chunk-v3`

Worktree `/data/illia/nearproof-wt/v3-d0a-challenge`, branch `lane/v3-d0a-challenge` from main
`216d9f04`. CPUs 8-9,24-25 only. User approval 2026-10-14: (1) finish `near-chunk-validation-d0-stark`
so it can be frozen and signed, (2) add a D0a tier to `near-chunk-v3`. Nothing signed, frozen,
registered or deployed; `examples/np-udr-stark-v2` (owned by the package lane) is not edited.

## Part 1 — `near-chunk-validation-d0-stark` (2026-10-14)

### params.bin

`spec/tools/params_bin_v3.py OUT D0a` (new `CONFIGS` key `D0a` → the D0 runtime configuration
`spec/challenge-inputs/runtime-config-pv86-v3.json`): 100 bytes, sha256
`ab13c19970996ebe01bc3d9234f64a1a6a989715f8da8dd7f92e5ab5eac8957f`, **byte-identical to
`NpUdrStarkV2.publicBin`** (`examples/np-udr-stark-v2/formal/NpUdrStarkV2/PublicBin.lean`, the
tape the certificate pins with `publicDigest_eq`). Written to
`oracle/fixtures/v3/arena-public-d0a/params.bin` (what the judge reads: `NearV3Oracle::approved_params`
reads `<public fixtures>/params.bin` and checks it against the request pin, domain = `#D0a`) and
`oracle/fixtures/v3/public-d0a/params.bin` (difftest set; the difftest only walks `d0/ ood/ mutants/`).
`spec/claim-v3.md` §4 lists the domain ids but is pinned by the signed challenges' `spec_digest`,
so the D0a wiring is documented in `spec/near-chunk-validation-v0a.md` §4 instead.

### Public fixtures: `oracle/fixtures/v3/arena-public-d0a` (new)

The draft pinned `oracle/fixtures/v3/arena-public`, whose `params.bin` has domain `D0`: the judge's
request pin refuses it for a `#D0a` challenge (fail-closed before any case runs). New set,
`spec/tools/build_public_d0a_arena.sh` (no regeneration, bytes copied):

* `arena-public` verbatim: 78 positives, 121 rejections;
* from `public-d0a/mutants`, first two by name per family: positives `w.path_depth_at_bound` (2);
  rejections `w.path_depth_over` (2), `w.foreign_routed_receipt` (2), `c.dup_bw_request` (2),
  `w.empty_pre_state` (1, the only one);
* `params.bin` (D0a). Total **80 positives, 128 rejections**, TreeDigest `865949a6…`.

Checked: Lean `nearspec-v3-check-d0a` (binary of `v3-prune`, whose `spec/lean` + `formal-core` are
identical to this branch's) accepts 80/80 positives and 0/128 rejections (67 out_of_domain, 61
reject); `oracle/tools/spec_check_v3_d0a.py` the same (80 / 0; it labels two
`c.epoch_start_flip` cases `reject` where Lean says `out_of_domain` — both non-accepts).

### Workload classes (D0 generators, unchanged)

The draft keeps the three D0 generator specs (`spec/workloads/near-chunk-validation-d0`, oracle
`oracle/v3`, pinned by the signed D0 challenges); the builder now hashes the committed spec files
and refuses if they differ from what it would rebuild. Judge-style samples with the live D0 oracle
(`/data/illia/nearproof-live/bin/near-arena-oracle-v3`, the spec args + `--seed S --d0-target 24`,
seeds 9101–9112, 12 runs per class):

| class | positives | in D0a (Lean) | in D0a (Python) | max unfoldBytes | max ChaCha words | max path depth |
|---|---|---|---|---|---|---|
| d0-quiet | 288 | 288 | 288 | 3,850 | 3 | 3 |
| d0-transfers | 288 | 288 | 288 | 9,350 | 2 | 3 |
| d0-missing | 288 | 288 | 288 | 14,834 | 5 | 3 |

Lean and Python agree on verdict, unfold, ChaCha words and path depth for all 864. Generation
takes 5–70 s per run. Public positives by class (features of `arena-public`): quiet 16, transfers
43, missing 5, accepted mutants 14 — all 78 in D0a. Why it holds by construction: A1 (generator
chains use 10 / 1000 Tgas), A2 / Canon0f / A8 / A10 / A12 are nearcore invariants on honest chains
(spec v0a §2), A7 / A9 have ≥ 100× headroom on every measured corpus.

### Draft and judge config

* `spec/tools/build_challenge_draft_v3_stark.py`: restriction `c.layout_wf` (A12) added and the A7
  text updated to the native-post-trie measure (the previous draft still said `B0 = 3,000,000` and
  lacked A8–A10); public fixtures `arena-public-d0a`; `--freeze-commit` now refuses unless
  `spec/lean` + `formal-core` equal that commit (as the chunk builder) and resolves the full SHA
  for `allowed_packages`; the non-schema `draft_notes` field is gone (the strict parser rejects it).
* `runners/formal-checker/challenges/near-chunk-validation-d0-stark.json` (new; found by name by
  the worker): the D0 config's trusted lists plus `NearSpec.TrieUpsertProofs`,
  `NearSpecV3.ChunkValidationV0a`, `NearSpecV3.PrepD0`, `NearSpecV3.ChallengeD0a` = exactly the 48
  trusted modules `np-udr-stark-v2` vendors (`dependency-locks/lean-vendor.sha256`).
* Templates `spec/lean/judge/ExpectedV3D0a{,.native-lean}.lean.template`:
  `params := { spec := NearSpecV3.challengeSpecD0a, profile := profileOf …, verifyFuel, maxProofBytes,
  maxReductionFuel }` (no trusted Lean module changed). Rendered at the draft's values and compiled
  (scratch, `lean -o`): `ArenaExpected.params = NearSpecV3.challengeParamsD0a := rfl` and
  `expectedTypeFor m = AdmissionStatement challengeParamsD0a {…} := rfl`.
* Runner unit tests: `every_config_trusted_closure_is_import_closed` (every config's included
  trusted modules import only included or toolchain modules) — it found that
  `near-chunk-v3.json` lacks `NearSpecV3.ChunkValidationV0a`, which `ChallengeChunkV3` imports since
  `77b844e0` (Tier.d0a); added. `near_chunk_d0a_config_renders`. Worker:
  `near_v3_d0a_draft_fixtures_and_params_pin` (fixtures digest = draft pin, 80 cases + 128
  rejections pass the D0a request pin, the D0 `params.bin` is refused, 100-byte params accepted,
  generator specs resolve to the D0 tool).
* `oracle/scripts/gen-heldout-v3.sh`: `DOMAIN=D0a` writes D0a `params.bin` per class and requires
  the D0a Lean checker (fails unless 72/72 positives accepted and 0 rejections).

### Candidate certificate shape (finding for the package lane)

The judge's audit (`ArenaAudit.check`) compares the certificate's type *syntactically* with
`ArenaExpectedInst.expectedType` / `ArenaExpected.expectedTypeFor <model>`. The current
`NpUdrStarkV2.certificate : ∀ bd tid, AdmissionStatement challengeParamsD0a {…}` is not that, so
the judge would report a type mismatch even after the HashMap fix. The reference candidate's form
works; checked in scratch against the rendered D0a template (zk-formal oleans of `v3-prune`):

```lean
import ArenaExpectedInst            -- judge-generated
import NpUdrStarkV2.PublicBin
import ZkFormal.NearV3.Assembly.AdmissionV3
set_option maxRecDepth 20000 in
theorem certificate : ArenaExpectedInst.expectedType :=
  ZkFormal.NearV3.Assembly.nearV3_admission_final _ NpUdrStarkV2.publicBin (by decide +kernel) rfl
-- axioms: propext, Classical.choice, Quot.sound
```

### Staging dry run (judge `formal-check`, dev bwrap, `Limits::default`)

Package = this branch's `examples/np-udr-stark-v2/formal/NpUdrStarkV2` + `sync-lean.sh` closure
(scratch; 3,960 candidate modules, byte-identical to `dependency-locks/zk-formal.sha256`; no
lakefile), `--challenge` the regenerated draft, `--challenge-config` the new config,
`--repo-root` this worktree (tree digest accepted), `--native-model
NpUdrStarkV2.Model.verifier@NpUdrStarkV2.Model`, public digest `ab13c199…`. Result after 46 s:
staging and the trusted build pass (no MANIFEST_INVALID); the only finding is the known
`ARTIFACT_BINDING_FAILED` (`ZkFormal.Near.Render.Common imports Std.Data.HashMap`), which the
model-split lane is fixing.

### Validation

`make pin-check` ok; `cargo test -p arena-formal-checker --lib` 16/16; `cargo test -p arena-worker
--lib near_v3` 9/9; fmt + clippy `-D warnings` on both crates; `arena-admin check` on the D0a draft:
the only error is the all-zero `heldout_commitment` (the held-out set is generated from a secret
seed at freeze time, below).
