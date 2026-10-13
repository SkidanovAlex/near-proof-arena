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

## 2026-10-13 — Rust derivation from claim + witness (`npudr v3trie`)

* Staged port, each stage differential-tested against `np-lean-trie-v3 <case> native` dumps
  (81/81 each): `src/v3/native.rs` (+ `native/sched.rs`, `native/trace.rs`): `applyNewChunk` /
  `applyMissingChunk` trie effects, `schedStep` with the bandwidth scheduler's `runCore` new
  state (`State` codec, `processRequests`, ChaCha shuffle), account-write replay with the post
  root check, `traceUpsert`/`traceKids` and `PTrie.upsert`; `walks.rs`: `mainValuesOf`,
  `allLookupQueries` (account/access-key/queue), `nativeQueryWalks`, `rankWalks` (counters);
  `upsnat.rs`: `honestInst` (forest root, `pathRecordId`, `encodeNativeParts`,
  `nativeWalkBase`, `positionedInstance`, `signedInstance`), `physicalPrefixUps`, window keys,
  `useReq`; `forest.rs`: `TrieNative.nodes` / `vals` / `heads`, `uniqNative` (seeded views,
  duplicate chain, old-record replay, use counts); `trie.rs`: assembly, A7 selectors/totals,
  size entry (`srcpSize` of `sizeBlocks`, `ovhNat`).
* Deliberate simplifications in `native.rs` (no trie effect; acceptance is a precondition):
  the scheduler's `distribute` / link grants are not computed (they do not change the new
  state), and refund forwarding limits (`tryForward`, only an out-of-domain error) are not
  re-checked. Upsert paths other than the in-place leaf replace are covered by unit tests
  only (no fixture exercises them).
* `walkTraceFast = walkTraceAligned` added (fixture walk renders >10 min → 1 s).
* `run-v2.d/trie.sh` on all 81 fixtures: **116 PASS, 0 FAIL** — Rust v3trie == Lean on 81/81,
  v3check 81/81 (7 tables), Rust == Lean renders 81/81 (sha256), 13 buses balanced 81/81,
  33 negatives (rpl/rplv flags, ups mid/post root and memory, dropped walk, node use count, uniq
  bytes, head root, val id, A7 over B0) rejected. `cargo test --release --lib` 102 passed (needs
  `conformance/out-v2/nearAirV3.json`), `make pin-check` ok, FastTrie lemmas use only
  propext/Quot.sound/Classical.choice.
* Open: Lean `rankWalks` in `np-lean-trie-v3` is quadratic (≤77 s on the 3 largest
  fixtures); Rust `ups::uu` recomputes a quadratic count per part-row column (fine on fixtures).
