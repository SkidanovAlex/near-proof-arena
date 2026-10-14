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

Freeze of the D0a draft: `allowed_packages` = (ArenaCore, NearSpec, NearSpecV3) at `3c2a4563`
(`build_challenge_draft_v3_stark.py --freeze-commit 3c2a4563`; `formal_spec.tree_digest`
`b890e835…` = `spec/lean` + `formal-core` of that commit, incl. the new templates; the 48 trusted
`.lean` modules are byte-identical to what `np-udr-stark-v2` vendors).

## Part 2 — tier D0a in `near-chunk-v3`

### What already existed

The trusted spec already has the tier (since `77b844e0`): `NearSpecV3.Tier.d0a` (rank 0),
`RelTier .d0a = RelD0a B0`, `rel_mono .d0a` via `relD0a_relD0` (so `sound_lift` covers it), and the
judge splices `declared_tier = "D0a"` as `NearSpecV3.Tier.d0a` (runner test
`near_chunk_v3_splices_the_declared_tier`). No trusted Lean module is changed by this lane.
Missing were the draft's coverage entry and the judge config's trusted modules.

### Changes

* `spec/tools/build_challenge_draft_v3_chunk.py`: tier `D0a`, rank 0, params
  `NearSpecV3.challengeParamsChunk .d0a`, classes `d0-quiet`, `d0-transfers`, `d0-missing`
  (explicit `D0A_CLASSES`; every other tier unchanged: D0 rank 1 … D3a rank 4, matching
  `Tier.rank` — the committed draft still had the pre-D0a ranks 0–3). Regenerated with
  `--freeze-commit 3c2a4563 --heldout-commitment sha256:eeeb27a4…` (the committed held-out set):
  the only changes are the coverage block, `tree_digest` `03fb64fd…` → `b890e835…` and
  `allowed_packages` `8926b431` → `3c2a4563`. New unsigned id `chl_3e63bc79c3150dce2620d72dbb028d5d`
  (`arena-admin check` OK); re-pinned in `examples/reexec-v3-d3/candidate.toml` and
  `adversarial/hostile-submissions/near-v3-d3-lenient-codes/candidate.toml` (the builder's checklist;
  `proof-mutators --test packages` passes).
* `runners/formal-checker/challenges/near-chunk-v3.json`: `NearSpecV3.ChunkValidationV0a` (Part 1),
  plus `NearSpecV3.PrepD0`, `NearSpecV3.ChallengeD0a`, `NearSpec.TrieUpsertProofs`, the trusted
  modules a D0a candidate (np-udr-stark-v2) imports; without them staging rejects it
  (MANIFEST_INVALID) exactly as the recheck lane saw with the D0 config.

### Workload classes and abstention

`d0-*` positives are D0a: 864/864 judge-style samples and the 78 public `d0-*` positives of
`public-chunk-v3` (= `arena-public`), Lean = Python (Part 1). A D0a candidate must answer
UNSUPPORTED (exit 3) on everything else: the 75 + 82 + 172 public d1/d2/d3 positives (public
fixtures carry no class, so this is never a gap), the d1-*/d2-*/d3-* samples (classes outside the
tier), and all rejections (a refusal). A `d0-*` positive outside D0a would be
`COVERAGE_GAP_IN_TIER`; none was seen, and the committed held-out `d0-*` positives must be checked
before signing (command below).

### Compatibility of np-udr-stark-v2 with tier D0a (needs a decision; nothing changed in the package)

| item | D0a challenge (as packaged) | near-chunk-v3 tier D0a |
|---|---|---|
| params.bin / public digest | domain `D0a`, D0 runtime config: 100 B, `ab13c199…` | domain `D3a`, D2 runtime config: 100 B, `b10e9585…` |
| Expected params | `{spec := challengeSpecD0a, …, maxProofBytes := 8 MiB}` (= `challengeParamsD0a`) | `challengeParamsChunkWith .d0a … 64 MiB …`: spec `challengeSpecChunk .d0a`, Domain = `DomainTier .d0a` (witness ≤ 64 MiB) ≠ `DomainD0a` |
| out-of-domain inputs | exit 2 (any failure) | must be exit 3 (UNSUPPORTED), fast, on every non-D0a input incl. witnesses up to 12 MiB |
| claim format, verify / prove / RAM limits | v3 claim; 10 s / 600 s / 16 GiB | same claim; 60 s / 600 s / 16 GiB |

So a near-chunk-v3 submission of the same prover is a second package variant (candidate.toml names
one challenge): `prepare` accepting the D3a tape, `PublicBin` = the D3a bytes, a certificate for the
tier statement, `declared_tier = "D0a"`, exit 3 outside D0a. The certificate does **not** need a
re-proved admission: `nearV3_admission_final` is generic in the public tape, and an admission of
`challengeParamsD0a` lifts to the tier statement. Proved in scratch (not committed; 45 lines,
axioms propext / Classical.choice / Quot.sound), and applied to the *rendered* near-chunk-v3
`ExpectedChunkV3.native-lean` template at tier D0a and 64 MiB:

```lean
theorem romImpl_eq (P : OracleProver challengeSpecD0a) (pub : Bytes) :
    Security.romImpl (challengeSpecChunk .d0a) ⟨P.run⟩ pub = Security.romImpl challengeSpecD0a P pub := by
  funext q s
  cases q with
  | hash x => rfl
  | prove cb w =>
    simp only [Security.romImpl]
    have hd : (challengeSpecChunk .d0a).decodeClaim cb = challengeSpecD0a.decodeClaim cb := rfl
    rw [hd]
    cases challengeSpecD0a.decodeClaim cb with
    | none => rfl
    | some c => rfl

theorem admission_d0a_tier {art : ArtifactDescription} {M : Nat} (hM : maxProofBytesD0a ≤ M)
    (h : AdmissionStatement challengeParamsD0a art) :
    AdmissionStatement (challengeParamsChunkWith .d0a NearSpec.TransferV1.profileValidityClassical128
      verifyFuelV3 M maxReductionFuelV3) art := by
  obtain ⟨pub, v, hpub, hconn, bk, ob⟩ := h
  refine ⟨pub, v, hpub, hconn, ⟨bk.Aux, bk.B⟩, ?_, ?_, ?_, ?_⟩
  · exact ob.semSound
  · rintro c w ⟨w', hw', -⟩ hr
    exact ob.semComplete c w ⟨w', hw'⟩ hr
  · rintro c w ⟨w', hw', -⟩ hr
    obtain ⟨pb, hl, hacc⟩ := ob.verifierComplete c w ⟨w', hw'⟩ hr
    exact ⟨pb, Nat.le_trans hl hM, hacc⟩
  · rcases ob.cryptoSound with hdet | hrom
    · exact Or.inl hdet
    · refine Or.inr ?_
      obtain ⟨hA, P, hP, n, num, den, hb, hs⟩ := hrom
      refine ⟨hA, ⟨P.run⟩, ?_, n, num, den, hb, ?_⟩
      · intro H c w hd hr
        obtain ⟨w', hw', -⟩ := hd
        obtain ⟨hl, hacc⟩ := hP H c w ⟨w', hw'⟩ hr
        exact ⟨Nat.le_trans hl hM, hacc⟩
      · intro A hH hP'
        have := hs A hH hP'
        unfold Security.romWins at this ⊢
        erw [romImpl_eq]
        exact this
-- tier certificate: admission_d0a_tier (by decide)
--   (nearV3_admission_final _ publicBinD3a (by decide +kernel) rfl) : ArenaExpectedInst.expectedType
```

Decision: put this lift in the candidate (no trusted change) or in `NearSpecV3.ChallengeChunkV3`
(trusted, helps every D0a candidate; changes the frozen tree again, so both drafts would be
re-frozen).

### Consequences of re-freezing near-chunk-v3

The tier needs `Tier.d0a`, which the old freeze (`8926b431`, tree `03fb64fd`) predates. The D3α
reference (`reexec-v3-d3`) was admitted against `03fb64fd`; before signing it must be re-vendored
at the new freeze commit (its trusted closure includes `ChallengeChunkV3`, whose `Tier` changed)
and its configured formal check re-run (`docs/logs/d3-lean4lean-2026-10.md` procedure).

## Remaining steps (user actions; nothing here was signed, frozen in a store, registered or deployed)

1. Merge `lane/v3-d0a-challenge` to main (the freeze commit `3c2a4563` stays reachable; if
   `spec/lean` or `formal-core` change on main before signing, re-run both builders with
   `--freeze-commit <new main commit>`).
2. D0a held-out set (secret seed, off-repo): `DOMAIN=D0a oracle/scripts/gen-heldout-v3.sh SEED DIR
   zk-formal/.lake/build/bin/nearspec-v3-check-d0a`, `arena-admin tree-digest DIR`, record it like
   `spec/challenge-inputs/heldout-commitment-v3-d0.json`, then
   `python3 spec/tools/build_challenge_draft_v3_stark.py --freeze-commit 3c2a4563
   --heldout-commitment sha256:<digest>` and `arena-admin check` (must print OK).
3. near-chunk-v3: run the D0a checker on the committed held-out `d0-*` positives (request.bin as
   claim.bin) — all must be accepted; re-vendor and re-check `reexec-v3-d3` at the new freeze.
4. `arena-admin freeze-trusted --commit 3c2a4563 --store $ARENA_TRUSTED_TREES --challenge
   challenges/drafts/near-chunk-validation-d0-stark.draft.json --challenge
   challenges/drafts/near-chunk-v3.draft.json`, then `arena-admin sign <draft> --key <governance key>`
   (or `supersede`), register, deploy; install `oracle/fixtures/v3/arena-public-d0a` in the workers'
   `ARENA_FIXTURES_DIRS` and the new formal-checker config in the configs dir.
5. Candidate: `challenge = "<signed chl_… of near-chunk-validation-d0-stark>"` in
   `examples/np-udr-stark-v2/candidate.toml` (draft id now `arena-admin id` of the draft) after the
   HashMap fix and the judge-shaped certificate.
