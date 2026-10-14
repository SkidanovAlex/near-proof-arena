# Pre-signing check of `reexec-v3-d3` against `near-chunk-v3` draft `chl_497bbbf1…` (lane `lane/v3-d3-presign`, 2026-10-14)

Goal: before the user signs the re-frozen `near-chunk-v3` draft (`chl_497bbbf1a6a5abc5b3448e0bc1a56997`,
freeze `85adc6c0`, trusted tree `66bba27e…`), re-run on the re-vendored D3α reference
`examples/reexec-v3-d3` (main `7e133b7d`) the two checks that `docs/logs/v3-refreeze-v3-2026-10.md`
did not repeat: (1) the worker mutation harness, and (2) the strict held-out run. The procedure is the
same as in `docs/logs/v3-d3-recheck-2026-10.md`. The 64 held-out rejection inputs are now also
run, from the off-repo held-out set. Only aggregate held-out counts are recorded. No held-out
case was copied into the repo or printed.

Nothing was signed, frozen into the live store, registered or deployed. No candidate, spec,
`formal-core`, `oracle`, `challenges` or `runners` file changed. Evidence directory:
`/data/illia/nearproof-deps/validation/v3-d3-presign-20261014/`. CPUs 8-9,24-25 (`heavy`, 24 GiB).

## 1. Build

`git archive 7e133b7d examples/reexec-v3-d3` was unpacked into a fresh directory, and a clean
`build-recipe/build.sh` ran there with a fresh HOME (`<evidence>/build.sh`, the same as the
refreeze lane's). It took 2:00, with peak RSS 3.2 GiB (3,398,032 KiB).

| output | sha256 | vs `v3-refreeze-v3` |
|---|---|---|
| prepare | `8341e9deeb0579bc38bd8d8868727be816e9ca31e2bff23d78487cda7bc61236` | identical (unchanged) |
| prove | `8859b7d2a9983a44c97eceeb4dcf0579b2e69ce278236f89cb99b137bfd76f44` | identical |
| verify | `cda17614a149340c06bffd7d3baa2b61341363cec8f2c2d5a46121395392766b` | identical (= judge-built verify) |

`prepare` on the public `params.bin` gives `public.bin` `b10e9585…`, which is byte-equal to the
previous run's. All 14 off-repo held-out `params.bin` files have the same digest. The harness
`runners/worker/examples/v3_reference_mutations` was built at `7e133b7d`
(`cargo build --release -p arena-worker --example v3_reference_mutations`). Its source sha256 is
`d2672446…` and the mutators source sha256 is `cbea667a…`; both are unchanged.

## 2. Public strict gate and worker mutations

* `<evidence>/strict.py`, the same script as before, ran with 4 jobs in 1:34. Result:
  **407/407 positives** were proved and verified, with claim = `expected_claim.bin`. **244/244
  rejections** were refused by `prove`. The maximum proof is 181,810 B. `strict/cases` and
  `strict/honest` are **byte-identical** to the `v3-refreeze-v3` run.
* Rejection reasons (`<evidence>/reasons.py`): every public rejection gives `prove` exit 2, and
  raw `verify` (claim = request, proof = witness) exits 1. That is 244/244, and each case has the
  same exit codes as in `v3-read-reference-20261007/public-strict-split`, matched by
  (request, witness) digest.
* Worker mutations (`v3_reference_mutations <verify cda17614> pub strict/honest mutations 4`):
  **pass**. There were 3,062 mutants and all were rejected with exit 1, including 458
  values/inject-unread and 79 codes/inject-unread. The run took 6:21. Every per-label count is
  identical to the recheck run. The full mutant set, as (case, label, base, mutant, claim digest,
  exit code), is **identical** to `v3-d3-recheck-20261014/mutations`.

## 3. Held-out strict run

* **Split fixtures** (the 208 digest-named positives kept in
  `v3-read-reference-20261007/heldout-strict-split/fixtures`, run with `strict.py`, 0:30):
  **208/208** were proved and verified with the expected claim. The maximum proof is 122,776 B.
  The proofs are **byte-identical** to the recheck run. Worker mutations: **1,433 mutants, all
  rejected (exit 1)**, including 201 values/inject-unread and 3 codes/inject-unread (2:01). The
  mutant set is identical to the recheck run.
* **Full off-repo set** `/data/illia/nearproof-deps/heldout/near-chunk-v3` (13 classes × 16
  positives plus 64 rejections). It ran with the original driver `oracle/tools/validate_read_reference.py`
  (sha256 `d0ef5984…`, unchanged), with `--jobs 4` and the save directory in the evidence
  directory (off-repo), in 2:35:
  * Positives: **208/208** were proved, verified and had the expected claim. **208/208 proofs are
    byte-identical** to the original `v3-read-reference-20261007/heldout-strict-split` run, matched by
    (request, witness) digest. The case order is also the same.
  * Rejections: **64/64 refused**. All 64 give `prove` exit 2 and raw `verify` exit 1, the same
    exit codes as the 20261007 run. This is the first re-run of the held-out rejections since that run.
  * Mutations on these honest proofs: 1,433 mutants, all rejected. The set is identical to the 20261007 run.

## Verdict

**PASS.** The build is reproducible and matches the refreeze and judge digests. Every public and
held-out positive was proved and verified with proofs byte-identical to the previous runs. Every mutant
(3,062 public and 1,433 held-out) and every rejection (244 public and 64 held-out) was refused,
with the same exit codes as before. The two pre-signing checks hold for `chl_497bbbf1…`. The signing steps
are listed in `docs/logs/v3-refreeze-v3-2026-10.md` ("To sign").

Results entry: `docs/e2e-results/v3-d3-read-reference/report.json` → `presign_check_refreeze_v3`.
