# lane/v3-prover-cover — fixture coverage for the D0a prover (np-udr-stark-v2)

Base: main d6725367.  Gaps (HANDOVER §5 "Fixture coverage"): no fixture made the bandwidth
scheduler draw a ChaCha20 word (tables 8 chacha / 9 rng with the A9 counter / 10 shuf only ran
empty on real data), and the scheduler's `0x0f` upsert (ups table) only ever took the in-place
leaf replace.

## 2026-10-13 — generator ops, 22 new accepted fixtures

* `fixtures-extra/gen_extra_d0a.py`: new `--bw BLK:SLOT=TO/BITMAP,...` (a chunk header's
  `BandwidthRequests`; edited where the chunk is new and in its copies in newer blocks, so the
  claim stays consistent and no receipt-shuffle seed changes; `BLK:*` = the slots new in BLK)
  and `--state OP` (main pre-state surgery, new `fixtures-extra/trie_edit.py`: canonical
  insert/delete (nearcore `insert_delete.rs` + `squash_node`, exact `memory_usage`, re-verified on
  every fully revealed node), `keep:` rebuild from the revealed keys, non-canonical `ext0:`).
  Entries of edited source chunks are re-keyed generally.  `meta.json` now records the Python
  D0a verdict and `chacha_words` per scheduler run (existing cases: meta only; their
  claim/witness bytes regenerate identically).
* Two generator bugs found on the way (both caught by the Python fixed point, fixed before any
  fixture was kept): editing only an old (missed) slot copy re-keyed its source chunk's proof
  (`missing source receipt proof`); propagating an edit back into an older source block changed
  the receipt-shuffle seed (`applied_receipts_hash mismatch`).
* Fixtures (`fixtures-extra/d0`, README table): **(e) ChaCha** x-bw-pair (1 word), x-bw-16 /
  x-bw-64 / x-bw-65 (ChaCha20 block boundaries), x-bw-all (156), x-bw-implicit (195 + 160, 2 runs,
  5 receipts), x-bw-implicit-only (0 + 158), x-bw-n5 (n = 5, 329 + 268), x-bw-noprior (absent prior
  state + requests, 195 + 190).  **(f) ups**: x-ups-bi, -bi-ext, -br, -bv, -lsa, -lsb, -lsc,
  -lsc-wex, -esl0, -esl1, -esn0, -esn1, -pt.  With the public fixtures' `LP` they cover all 11
  `UCase` terminal cases and all 12 `UKind` part kinds (checked with `npudr v3native`, field `us`).
* Unreachable / restricted (README "Reachability in D0a"): no deletions in D0 (writes = `0x0f`
  upsert + same-length account set, `RuntimeD0.lean`); implicit runs only `LP`/`BR`
  (`find_upsert_self`); value-length change at `LP`/`BR` excluded by Canon0f (n² links before
  and after); `LSa` only for the trie {""}; W0 = 770,000 unreachable from small fixtures (A8:
  ≤ n² requests per run; bases n ≤ 5, ≤ 2 runs → max 597 words).
* **Lean/Python disagreement (spec decision, not changed):** an empty main pre-state (root
  `0^32`, `--base 00-h10004-s3 --state keep:`) is accepted by the Python reference (and would be
  by nearcore: empty root = `Hash::default()`), rejected by Lean `checkD0`
  (`invalid: MissingTrieValue (BufferedReceiptIndices)`: the zero root is an unrevealed `.hash`;
  `PTrie.upsert (.hash _) = none`).  Not kept as a fixture.
* **Python reference bug fixed** (`oracle/tools/spec_check_v3_d0a.py`, not pinned): A7's native
  post-trie term recorded created nodes in a dict keyed by nibble position; an empty-key
  extension shares its position with its child, so the new extension counted as unrevealed and
  its subtree dropped out (x-ups-pt: Python 6144 vs Lean 7178 = 2 × (46 + 50 + 421)).  Now a set
  of (position, hash).  Lean's structural `unfoldBytes` is the definition; it was right.
* Acceptance: D0a difftest on fixtures-extra (39 d0 + 3 mutants) 0 disagreements (39/39 accepted
  by Lean `checkD0a B0` and Python, 3/3 mutants rejected); public-d0a re-run with the fixed
  Python checker: 0 disagreements (64 + 298 mutants + 59 ood).  Lean `nearspec-v3-check-d0a`
  rebuilt first (was Oct 9).
* `npudr v3prove --check-only` on all 22: 25 tables' constraints hold, 51/51 buses balanced
  (bus 50 SCHACHA carries one message per drawn word: x-bw-pair 1, x-bw-implicit 355, x-bw-n5
  597).  No Rust divergence.

## 2026-10-13 — differentials on the 22 new fixtures (`run-v2-section.sh`, CPUs 28–31)

`FX`/`EXTRA_FX`/`TRIE_FX`/`SCHEDQV_FX` = a directory of the 22 new cases, `A7_CASES=22`; the
conformance Lean exes rebuilt from the tree first (8,081 jobs; `np-lean-sched-v3`,
`-rcptfam-v3`, `-bundle-v3`, `-verify-v3` were missing in this worktree).
**931 PASS, 1 FAIL** (the FAIL is a test artifact, fixed below):

* extra 331: acceptance (22 accepted by Lean/Python, 0 disagreements), public tape / Prep.encode /
  Hint / d0-prep / v3prepare byte-identical to Lean, node/val/head, SHA families + bins, srcp/acct.
* trie 57: Rust `v3trie` == Lean `np-lean-trie-v3` on 22/22 (native objects incl. every ups
  run: all 11 terminal cases, 12 part kinds), v3check 7 tables, renders identical, 13 trie
  buses (incl. UPB, RPL, RPLV) balanced, negatives rejected.
* a7 202: node/val A7 on real entries, Rust == Lean renders, 22 cases.
* schedqv 83: Rust `v3sched` == Lean `np-lean-sched-v3` (9 files) on 22/22, v3check tables 8–15,
  22, renders identical (18 with full 2^22 dumps), 25 scheduler/ChaCha buses balanced; sampler;
  negatives.  First real-data runs with non-empty chacha/rng/shuf lanes (requests up to 25 per
  run, absent prior state).
* collect 35: SHA families + bins identical 22/22.  rcptfam 223: 61 fixtures (22 + the 39 of
  fixtures-extra/d0), 0 failures.
* FAIL `v3sched accepts x-bw-16's claim with x-bw-64's witness`: the schedqv wrong-witness
  negative paired the first two fixtures of FX; these two share their base and their witnesses
  differ only in the witness's copy of the endorsed header (`prev_block_hash`).  Lean rejects
  the pair (`witness chunk header differs from the claim`), but the claim is true and the rest
  of that witness is a valid witness for it, so proceeding is no soundness issue.  Test fixed:
  first vs last fixture (x-bw-16 + x-ups-pt witness: rejected, `missing buffered index`).
* No Rust divergence on any table.

Wiring: the new cases live in `fixtures-extra/d0`, so extra / trie / schedqv / rcptfam run them
by default; `collect.sh` now iterates `COLLECT_FX` (default `$fx fixtures-extra/d0`) and `a7.sh`
adds `A7_EXTRA` (default x-ups-pt, x-ups-esn0, x-ups-lsa, x-bw-noprior).
