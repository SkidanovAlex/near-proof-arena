# Independence of the clean-room Python checkers (HANDOVER §8)

Status 2026-10-16. The HANDOVER records: *"Independence of the clean-room
Python VM: it was tuned against nearcore black-box runs."* This note states
precisely what that means, what evidence constrains the Python checkers
today, and what full independence would require. **Independence is not
achieved**; nothing here relaxes a measurement rule or a domain condition.

## What the Python side is

`oracle/tools/spec_check_v3{,_d0a,_d1,_d1a,_d2,_d3}.py` (plus the difftest
drivers `difftest*.py`) are independent Python transcriptions of the domain
relations. They are the third leg of the three-way difftest used to check the
Lean transcriptions (`spec/lean/v3/NearSpecV3/…`) against nearcore itself:

* nearcore (pinned `44f7ae6c`, PV 86) executes the corpus and gives validator
  verdicts — the ground truth, not a peer;
* Lean decides the formalized relation;
* Python decides its own transcription of the same relation.

A disagreement between any two legs is a finding; the recorded corpora all
reproduce with 0 disagreements (`spec/difftest-report-v3*.json`,
`-d0a`, `-d1`, `-d2`, `-d3`, and the v1 `-v2`/`.json` reports).

## What "tuned against nearcore" means here

The Python checkers were written while iterating against nearcore's
observable behaviour (black-box runs of `Runtime::apply` /
`validate_chunk_state_witness` on generated corpora), not derived from
`spec/lean` alone. Consequences, stated honestly:

* Where nearcore's verdict and the written spec disagreed during development,
  the *spec* was amended to match nearcore (that is the intended direction:
  the spec transcribes nearcore). The Python checker therefore shares this
  bias with the Lean transcription — both were validated *against* nearcore,
  and nearcore's own quirks (e.g. the cold-cache contract-code verdicts,
  STATUS-V3-D3 §6) are baked into all three legs as "correct".
* Shared-author risk: the same people wrote near, Lean and Python sides in
  the same direction of iteration. A misreading of nearcore could
  plausibly be replicated in both transcriptions and then be invisible to
  the difftest, because nearcore — the oracle both transcriptions were tuned
  to — would agree with itself.
* The Python checkers are **tests, not proofs**: they add runtime evidence
  and mutation sensitivity (hundreds of thousands of rejected mutants across
  the corpora), but no theorem rests on them.

## What the difftests do constrain

* Every relation rung (D0/D0a, D1, D2, D3α) is difftested three ways over
  large corpora (tens of thousands of cases; see the `-report-*.json`
  files), including adversarial mutants and out-of-domain rejections.
* The Python side has independently reproduced specific contested results,
  e.g. the A9/A10/A11/A7 domain-bound measurements and the empty-pre-state
  rejection (HANDOVER §5, oracle-d0a).
* Where Python and Lean disagreed historically, the disagreements were
  resolved *before* freeze and recorded in the difftest reports.

## What full independence would require (follow-up options)

1. **Fresh transcription from the spec only**: a new implementation of one
   relation (recommend D0a — smallest) written from
   `spec/near-chunk-validation-v0a.md` alone, by an author who does not read
   the existing Python/Lean transcriptions or nearcore internals first, with
   the working log kept as provenance.
2. **Adversarial differential review**: a reviewer actively hunting for
   shared misreadings (the failure mode above), especially around the
   documented ambiguities (STATUS-V3-D3 §6: cache-dependent verdicts,
   delayed-receipt boundaries, refund forwarding).
3. **Provenance discipline**: record, for each Python checker, its commit,
   the spec revision it transcribes, and the nearcore pin it was tuned
   against, so later spec changes cannot silently drift it.
4. **Eventually**: replace the Python leg's authority with a second formal
   transcription in a different proof assistant, so "independence" is a
   theorem-checking statement rather than a testing statement.

Until then, the honest claim remains: three implementations agree on all
recorded corpora, two of them are formalized/tested transcriptions of one
ground truth to which both were tuned.
