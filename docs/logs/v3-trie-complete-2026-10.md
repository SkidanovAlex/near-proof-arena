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
* `Assembly/TrieBusBalance.lean` — per-bus reduction of `R.Balanced`: `BalancedAt b`,
  `balanced_iff`, `cnt_tf` (a component's count = its table's bus count), `cnt_tf_off`,
  `sum_tables` (restrict the 25-table sum to a table filter `p` with the kernel check
  `Covers b s p`), `pub_off`.  **`balancedAt_digs`**: `DIGS` balance of any bundle whose
  node/head/uniq components carry record lists with `Link3.DigsBal` — with `uniqs_digsBal` this
  closes `DIGS` for the honest bundle.  Bus/table survey (kernel `#eval` of `nearAirV3`):
  trie-only buses PARENT(2) node/head; EDGE(4) node/head/walk/ups; BMAP(11) node/walk/ups;
  DIGS(17) node,head→uniq; DUP(19) uniq→node,val; ENT(20) node/val; VPARENT(22) node→val;
  MEMD(23) ups; MIDROOT(24) head→ups; UPB(25) node/ups; ROOT(10) ups→head + public both sides.
  Shared: BYTES(0) senders node,val,ups,codec,rcpt,acct,srcp,mrk → sha (+ public recv);
  DIGEST(1) sha → node,head,ups,codec,rcpt,srcp,mrk; VSLOT(3) acct→node; KEYNIB(5) rcpt,qv→walk;
  FINAL(6) walk→rcpt,qv; VBYTES(21) codec,acct,akey,qv→val; SIZE(18) node,val,srcp→size;
  S0F(59) ups→codec, SPOST(60)/SPLEN(61) codec→ups.
* `Assembly/TrieVParent.lean` — **`VPARENT` closed**: `forestNodes_vpar` (the node value windows
  of the seeded forest are, in DFS order, exactly `seedValuesFrom 0 (forestBytes ts)`'s
  `(vid, len)`), the metadata passes keep them, `vparentBal_native` (`Link3.VParentBal` of
  `TrieNative.nodes … q` / `vals`, every `q`), `balancedAt_vparent` (bundle level).
* `Assembly/TrieParent.lean` — **`PARENT` closed**: `seedNodesT_parent`/`seedKidsT_parent`
  (mutual: a seeded tree's receives ~ its root message ++ its kid-window sends),
  `forestNodes_parent`, `forestWalkHeads_parent` (heads send exactly the forest's root
  messages when every tree is revealed), metadata passes keep the messages,
  `parentBal_native`, `accepted_forest_isNode` (every pre tree is a node: its scheduler upsert
  `traceUpsert` succeeds; main pre via `SizedAccountRun`), **`parentBal_accepted`**,
  `balancedAt_parent`.
* `Assembly/TrieEnt.lean` — **`ENT` closed**: `chain_ent` (chain metadata sends ~ receives over
  any occurrence list with distinct ids, via `class_sends`/`class_recvs` + `total_ent`),
  `node_sends_shift` / `val_sends` (the honest node/value `ENT` traffic is the chain traffic of
  their occurrences), `entBal_of`, **`entBal_accepted`**, `balancedAt_ent`.
