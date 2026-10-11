# Lane `v3-trie-complete` — log (2026-10)

Trie side of `CompleteV3Stmt`: honest native entries, `TableRenderV3` of tables 0–7, trie bus
balances, A7 (a)/(b).  Worktree `/data/illia/nearproof-wt/v3-trie-complete`, branch
`lane/v3-trie-complete` (from main `4b5e8209`).

## 2026-10-11 — start

* `origin/lane/v3-link` (A7 tables) does not merge cleanly into main: it predates the
  2026-10-11 evening merge (conflicts in `NearAir.lean` — rcpt `tableR`, srcp `tableD`, size cap 4,
  ChaCha `table22` vs. the A7 replacements — and in `ExtractV3`, `LinkV3`, `NearAdmission`,
  `NearAirSize`, whose size bound must be recomputed).  That merge is the lead's integration
  step; this lane works on main's `nearAirV3` (base tables at 2, 4, 7) and keeps the A7 work
  separable.
* `Assembly/RenderV3Trie.lean`: `shaRenderV3` (t = 0, 1), `nodeRenderTrie`, `headRenderTrie`,
  `valRenderTrie`, `walkRenderTrie` (fixed height `2^22`, Walk22 `WalkOk`), `uniqRenderTrie`,
  `upsRenderTrie` : `TableRenderV3 pub t _`, each with `tf` definitionally the entry lists'
  traffic (`*_tf`).  Audit `test/AuditRenderV3Trie.lean`.
* `Assembly/UniqNative.lean` — **the `UEnt` producer**: `rawEnts vs hs` = one entry per `DIGS`
  window (node revealed kids `NPRE(c)`, node values `VPRE(i)`, head roots `NPRE(rid)`), sorted by
  `(τ, le256 digest, rk eid)` (`uniqOf rk`, `List.mergeSort`).  `uniqOf_digsBal`: `Link3.DigsBal`
  for any node/head lists (no hypothesis).  `uniqOf_ok`: `UOk` from `RawOk` (32 digest bytes
  `< 256`, `eid < P`, `τ+1 < P`, `≤ 2^17` windows, a head, τ-coverage).
* `Assembly/TrieNative.lean` — the honest entries as functions of the native objects
  (`forest`, `seedNodes`, `seedVals`, `chain`, `nodes … q`, `vals`, `heads … keys`, `uniqs rk …`);
  `accepted_ok` (NodeOk/ValOk/HeadOk from acceptance at `B0`, any `q`/`keys` of length `< P`),
  `accepted_native` (the native objects incl. the `SizedAccountRun` replay exist for every
  accepted witness), `accepted_bundle_parts` (the node/head/val `TableRenderV3` components with
  `tf` = the native traffic), `uniqs_digsBal`.
