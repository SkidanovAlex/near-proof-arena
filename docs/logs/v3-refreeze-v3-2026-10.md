# Lane `lane/v3-refreeze-v3` — re-freeze `near-chunk-v3` with tier D1a (2026-10-14)

Worktree `/data/illia/nearproof-wt/v3-refreeze-v3`, branch `lane/v3-refreeze-v3` from main
`0b4c499d` (D1a spec merge + the DRAFT PATCH `76bb8d84`). CPUs 9,25 only (`heavy`, 24 GiB).
User decisions (2026-10-14): accept the rank renumbering (D0a 0, D0 1, D1a 2, D1 3, D2 4, D3a 5);
add both `spec/near-chunk-validation-v0a.md` and `spec/near-chunk-validation-d1a.md` to the
spec-doc digest; no nearcore-judged (online-injected) T1 mutants for now. The signed D0a challenge
(`chl_56077279…`, tree `b890e835…`) is untouched. Nothing was signed, published into the live
trusted-tree store, registered or deployed.

Evidence directory: `/data/illia/nearproof-deps/validation/v3-refreeze-v3-20261014/`.

## 1. Spec-doc digest and freeze commit

* `spec/tools/build_challenge_draft_v3_chunk.py`: `SPEC_DOCS` = v0, **v0a**, d1, **d1a**, d2, d3
  (each tier's amendment right after its base domain); docstring and checklist updated (the
  retired hostile package `adversarial/retired/near-v3-d3-lenient-codes` keeps its old pin).
* **Freeze commit `85adc6c005aa6833c2f71efecd51d27444aa549c`** (that commit; `spec/lean` +
  `formal-core` = main `0b4c499d`). Trusted-tree changes since the previous freeze `3c2a4563`:
  `ChallengeChunkV3` (Tier.d1a), new `ChunkValidationD1a`, `ChallengeD1a`, `HintCompact`, and
  comment-only lines in the two `ExpectedChunkV3` templates.

## 2. Draft regeneration

`python3 spec/tools/build_challenge_draft_v3_chunk.py --freeze-commit 85adc6c0 --heldout-commitment
sha256:eeeb27a45a70691de0b2785ad4a11c10c4edd378594c0248639416202a8b3696`. The held-out set is
unchanged. The generator also rewrites `spec/challenge-inputs/near-chunk-v3-weights.json`
(`spec_docs` += v0a, d1a). Diff against the `3c2a4563` draft (nothing else changed; no hand edits):

| field | before | after |
|---|---|---|
| `formal_spec.tree_digest` | `b890e835…` | `sha256:66bba27ef4c8772d8e4fba0258fc504bcc9d59b5bdfd66f073ff9c50751ec150` |
| `spec_doc_digest` | `cbc793c3…` | `sha256:b68420e35a81c52a1dacf03b865e599dcf0a76ecc836235f8b3d2db765e33e94` |
| `allowed_packages` (ArenaCore, NearSpec, NearSpecV3) | `3c2a4563…` | `85adc6c0…` |
| coverage | D0a 0, D0 1, D1 2, D2 3, D3a 4 | D0a 0, D0 1, **D1a 2** (d0-*, d1-*), D1 3, D2 4, D3a 5 |

`arena-admin check` (built here): **OK `chl_497bbbf1a6a5abc5b3448e0bc1a56997`**. Its one warning,
"no baseline yet", is the same as before. `arena-admin freeze-trusted --commit 85adc6c0` into a
**scratch** store (`<evidence>/trusted-store`) recomputes `66bba27e…` = the pin, and `check-trusted`
reports OK.

## 3. Held-out tier checks (before the freeze)

`nearspec-v3-check-d0a` / `nearspec-v3-check-d1a` were built in this worktree at the freeze tree
(`lake build`, 110 jobs). They ran on `/data/illia/nearproof-deps/heldout/near-chunk-v3` through
symlinks in a scratch directory (claim.bin → request.bin, which is byte-equal to
`expected_claim.bin` on 96/96 cases). No case was copied or printed. Only aggregate counts follow:

| checker | classes | positives | accept |
|---|---|---|---|
| D0a | d0-quiet, d0-transfers, d0-missing | 48 | **48** |
| D1a | d0-* and d1-transfers, d1-mixed, d1-receipts | 96 | **96** |
| D1a | 64 rejections | 64 | 0 (9 reject, 55 out of domain) |
| D0a | 64 rejections | 64 | 0 (3 reject, 61 out of domain) |

So there is no `COVERAGE_GAP_IN_TIER` exposure for D0a or D1a candidates on the committed
held-out set. The D1a maxima on the positives are far inside the bounds: unfold 9,450, ChaCha
words 0, path depth 3, transactions 13. Total time 40 s.

## 4. Formal-checker config

`runners/formal-checker/challenges/near-chunk-v3.json` already lists `NearSpecV3.ChunkValidationD1a`
(from `76bb8d84`; `ChallengeChunkV3` imports it). `NearSpecV3.ChallengeD1a` is **not** imported by
`ChallengeChunkV3` and is not added. Adding it would also need `ChallengeD1` and would change every
candidate's linked trusted set. The config is not part of the frozen tree, so it can be added
without a re-freeze when a D1a candidate needs it.
`cargo test -p arena-formal-checker --lib`: 16/16, including `every_config_trusted_closure_is_import_closed`
and `near_chunk_v3_splices_the_declared_tier`. `cargo test -p proof-mutators --test packages`: 4/4,
including `near_chunk_v3_packages_pin_the_challenge`.

## 5. `reexec-v3-d3` re-vendor and re-check

* `source/verifier/sync-vendor.sh 85adc6c0` (87 files): `ChallengeChunkV3` changed and
  `ChunkValidationD1a` was added; `lean-vendor.sha256` was regenerated. `build.sh` `TRUSTED_PREFIXES`
  now equals the config's 64 trusted modules. The judge-local Expected template was re-synced; the
  change is one comment line. `sync-logged.py 77b844e0 --check` passes (39 modules), and upstream
  `Logged` is unchanged. No candidate Lean source changed. `candidate.toml` is now pinned to
  `chl_497bbbf1…`.
* **Configured formal check** (`<evidence>/formal-check.sh`, identical to the `v3-d3-recheck`
  procedure: `formal-check` built here, near-chunk-v3 config, `--repo-root` = scratch store
  `66bba27e…`, public digest `b10e9585…`, `--declared-tier D3a`, default limits). **All six gates
  PASS**: FORMAL_SEMANTIC_SOUNDNESS, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_CRYPTO_SOUNDNESS,
  FORMAL_IMPL_CONNECTION, AXIOM_AUDIT and ARTIFACT_BINDING. There are no findings. Exit 0, wall
  time 13:34 on 2 CPUs, peak RSS 13.8 GiB.

  | stage | verdict | time |
  |---|---|---|
  | trusted elaboration | ok | 54.0 s |
  | candidate elaboration | ok | 556.6 s |
  | model elaboration | ok | 11.8 s |
  | leanchecker | accepted, 72 modules / 72 runs | 49.8 s |
  | arena-audit | accepted | 4.2 s |
  | nanoda (lean4export 7.3 s) | accepted | 16.7 s |
  | lean4lean | accepted, 72 modules / 72 runs | 53.2 s |
  | ndjson-audit | accepted, 12,831 decls | 2.6 s |

  The closure has 12,571 declarations, with axioms {propext, Classical.choice, Quot.sound}. The
  model closure digest `063b6c17…` is unchanged. The judge-built `verify` is `cda17614…`. The only
  warning is the old supplementary `partial` in `D3LSpec.lean:82`.
* Clean `build.sh` on a `git archive` copy with a fresh HOME took 1:53 (3.4 GiB). Outputs:
  `prepare 8341e9de…` (unchanged), `prove 8859b7d2…`, and `verify cda17614…`, which equals the
  judge build. `public.bin` = `b10e9585…`.
* Strict public gate (`<evidence>/strict.py`, 2 jobs, 3:06): **407/407 positives** were proved,
  verified and matched the expected claim. **244/244 rejections** were refused by `prove`. The
  maximum proof is 181,810 B, and all **407 proofs are byte-identical** to the `v3-d3-recheck` run.
* SDK `arena check-local` (`chl_497bbbf1…`, draft file, `public-chunk-v3`; 9:29, 3.4 GiB): exit 0.
  PKG_WELLFORMED, BUILD_REPRODUCIBLE, CONFORMANCE_DIFFERENTIAL, PROVER_RELIABILITY,
  ADVERSARIAL_PROOFS and RESOURCE_LIMITS pass. AXIOM_AUDIT is SKIPPED locally, as before. The
  package digest `a4a4fc1a…` is for the archive of `fec6de59`; the later README-only commit
  changes it.
* Not re-run: the worker mutation harness and the held-out strict split. The verifier logic is
  unchanged, and the proofs are byte-identical.

## Checks

`make pin-check` OK. No `challenges/chl_*.json`, `oracle/v3*`, pinned file, `spec/lean` or
`formal-core` file was modified. No sorry/axiom/native_decide/implemented_by was introduced (no
Lean source changed).

## To sign (user decision; not done here)

From a checkout of this branch (or main after merge, as long as `spec/lean` + `formal-core` still
equal `85adc6c0`):

```
arena-admin freeze-trusted --commit 85adc6c005aa6833c2f71efecd51d27444aa549c \
  --store /data/illia/nearproof-live/trusted-trees \
  --challenge challenges/drafts/near-chunk-v3.draft.json      # must print sha256:66bba27e…
arena-admin check-trusted --store /data/illia/nearproof-live/trusted-trees challenges/drafts/near-chunk-v3.draft.json
arena-admin check challenges/drafts/near-chunk-v3.draft.json  # OK chl_497bbbf1…
arena-admin sign challenges/drafts/near-chunk-v3.draft.json --key <governance key path>
```

After signing, re-pin `examples/reexec-v3-d3/candidate.toml` to the signed id. It equals
`chl_497bbbf1…` if the definition is signed unchanged. Then install the formal-checker config in
the workers' configs dir.
