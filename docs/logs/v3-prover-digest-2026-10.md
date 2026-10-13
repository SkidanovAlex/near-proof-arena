# lane/v3-prover-digest — DIGEST recheck (2026-10-13)

**Base.** main `d6725367`.  Question (HANDOVER §5 "To recheck"): the schedqv lane, assembling the
25 tables itself, saw bus 1 DIGEST unbalanced on fixtures with outcomes — table 23 (`mrk`)
receives `MRK(root)` with a zero digest (00-h10016-s0, 00-h10024-s0) — while `npudr v3prove
--check-only` reports all 51 buses balanced on all 81 fixtures.  Which assembly is right?

## Verdict: v3prove is right; the per-table path's `npudr v3bus` used zero publics

**Root cause.** Table 23's interaction 2 (`MerkleEmpty`, the root row, `mult = (1 − empty)·RT`) is
the only interaction of `nearAirV3` that reads public inputs:

    bus 1 (DIGEST) receive  [CID, CLEN, p146, …, p177]

i.e. `DIGEST(rootId, rootLen, outcome root)` with the root digest taken from the public inputs —
the prepared tape's bytes 146..178.  `npudr v3bus` (`src/bin/npudr.rs`) rendered the tables and
evaluated every interaction with `pubs = vec![F::ZERO; num_pub]`, so the root row received
`DIGEST(MRK(0), 64, 0^32)` while the SHA bin job `MRK(0)` sends the true digest: one message
unmatched on each side exactly when mrk n > 0.  `v3prove` uses `verifier::public_inputs(air,
cb')` (= Lean `Udr.pubOf`: the bytes of `cb' = preparedBytes (prepD0 cb h) 0`), as does the
Lean side: `mrkAcc : TableRenderV3 A.pub 23` and `receipt_sha` (`Assembly/RenderV3RcptSha.lean`)
state the receipt-side DIGEST balance with `A.mrkAcc.tf.recvs B_DIGEST` under
`A.pub = pubOf (preparedBytes …)`.  The entries were never wrong.

**Reproduction (00-h10016-s0, mrk n = 2).** Per-table assembly (`v3trie` ×7, `v3sched`,
`v3rcptfam`, `v3sha`; collector bus check 0 unmatched) + old `v3bus 0,1` over all 25 tables:
bus 0 balanced; bus 1 `sent 0 recv 1 [6, 64, 0…0]` and `sent 1 recv 0 [6, 64, 188, 120, 226, …]`.
`v3prove --check-only`: bus 0 6,115/6,115, bus 1 67/67 balanced.  Tape bytes [146,178) =
`188, 120, 226, 161, …, 51, 170` = the digest of bin job `MRK(0)` (64-byte preimage).

**Against Lean (same fixture).** `np-lean-rcptfam-v3` mrk `(n, levels)` == Rust `v3rcptfam`
(root level `{id 6, len 64, dig 188,120,…}`); `np-lean-shabins-v3` bins b0/b1 == Rust `v3sha`
bins (JSON-equal); the Lean `MRK(0)` job digest == tape root bytes.  So the honest render
balances with the real publics, as `rcpt_trie_vbytes` / `receipt_sha` / `balancedAt_mpos` say;
nothing contradicts the completeness proof.

Additional evidence: two of the three real proofs already accepted by `np-lean-verify-v3`
(00-h10035-s3 mrk n = 814, 01-h10009-s1 n = 5) have outcomes, so the root row's public-input
DIGEST receive was already checked by the deployed Lean verifier; v3prove is unchanged, so no new
real proof was needed.

## Fix

* `npudr v3bus`: public inputs from the tape (`verifier::public_inputs(&air, &tape)`), as in
  `v3prove`.  All existing callers (trie.sh, schedqv.sh, extra.sh) already pass the prepared tape;
  no other interaction reads publics, so their results are unaffected.  After the fix the
  per-table assembly balances buses 0 and 1 on 00-h10016-s0.
* **Regression section `run-v2.d/digest.sh`** (all 81 fixtures): (1) `v3prove --check-only`,
  report buses 0/1 balanced, its `prepared.bin` == `v3prepare`+`v3public`; (2) the per-table
  assembly + `v3bus 0,1` over all 25 tables balanced; (3) fixtures with outcomes: Lean mrk
  `(n, levels)` and Lean bins == Rust, tape root == Lean top-level digest == digest of a Lean bin
  job, buses 0/1 balanced with the Lean bins substituted; (4) negatives on 3 fixtures with a
  hashed root: flipped tape root byte, zeroed tape root (= the old zero-publics evaluation),
  flipped child digest of the mrk root node, MRK root job dropped from the bins — each unbalances
  bus 1.

## Results

(see below)
