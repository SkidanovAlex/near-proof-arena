# lane/v3-prover-trie — honest trie-side entries (np-udr-stark-v2, v3 D0a prover)

## 2026-10-13 — Lean ground truth (`np-lean-trie-v3`) and fast A7 renders

* Merged origin/lane/v3-prover-prep (a9bf42a5), then origin/main bb37a433 and 99f99e76
  (extra fixtures).
* `conformance/TrieEntriesV3.lean` → `np-lean-trie-v3 <case> [<table>|native]`: evaluates the
  entry lists of `TrieSide.trie_side_exact` on the native objects of an accepted witness
  (`nativeOf` as ShaBinsV3): honest ups instances `honestInst` (the construction inside
  `scheduler_instance_origin_inputs`, `baseI/base := default`; `Qs` = `encodeNativeParts`
  payload, terminal address by `tsize`), `ws = nativeQueryWalks pairs (allLookupQueries …)`
  with `v` read from `m.pre` (`mainValues_unique`), `Js = upsRanked ws insts`,
  `q = useReq ws insts (PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS)`, node
  `TrieNative.nodes … q`, head `heads … q.edges`, val, uniq `uniqNative`, walk `rankWalks [] ws`,
  A7 selectors `S n = [n] ∈ insts.flatMap upsRplMsgs` / `SV` (the `perm_of_singletons`
  witnesses of `a7_perm_native`), size `honestSizeV ns es sizeBlocks` + `ovhNat` + `yN`.
  Self-checks (rpl/rplv singletons distinct and in range, A7 total ≤ B0). `native` mode dumps
  the intermediates (tries, account replay, scheduler upsert runs, queries, ws, insts, q).
* `conformance/Conformance/FastTrie.lean`: executable twins with equality lemmas (no sorry):
  `nodeTraceFast = nodeTraceAligned`, `valTraceFast = valTraceAligned`, `upsTraceFast =
  upsTraceAligned` (record lists / `uU` use counts / `szAt` prefix sums hoisted out of the
  per-cell functions), `nodeA7Fast/valA7Fast/upsA7Fast = nodeA7Trace/valA7Trace/upsA7Trace`
  (running sums `prefixF` from a table, `prefixGet_tab`).  `np-lean-render-v3-a7` uses them;
  a fixture node A7 render now takes ~0.25 s (the quadratic version timed out at >100 s).
* Results: all 64 public + 17 extra fixtures dump (0.2–3 s; three cases with ~1,000–1,600
  lookup walks take 25–77 s in `rankWalks`, which is quadratic in Lean). On honest entries all 7
  tables pass `npudr v3check` (first honest ups table ever), Rust renders == Lean renders, and
  the 13 trie-internal buses (PARENT EDGE ROOT BMAP DIGS DUP ENT VPARENT MEMD MIDROOT UPB RPL
  RPLV) balance against the public tape (`npudr v3bus`).
* `run-v2.d/trie.sh` (new section) and `run-v2.d/a7.sh` (`A7_NODE_MAX` default lifted from 3
  to 100000: Lean node renders on every fixture; 455 PASS with A7_CASES=64).
