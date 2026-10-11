# Lane `v3-a11` (spec) — A7 on the native post trie, A11 retired (2026-10)

User decision 2026-10-12: A7's post term counts the native post trie the execution returns (no
`rebuildPost`); A11 `w.post_rebuild` is retired (it only controlled the rebuild). Reason: the
AIR's A7 running sums count the native post trie; the rebuilt trie can differ under a SHA-256
collision between a pre blob and a written node, which made the honest A7 identity unprovable.
Worktree `/data/illia/nearproof-wt/v3-a11`, branch `lane/v3-a11`, merged
`origin/integration/v3-20261012` (`bbba829c`; `integration/v3-20261012b` did not exist on
origin at start).

## 2026-10-11/12

* Spec `NearSpecV3.ChunkValidationV0a`: `triesD0` yields `(pre_τ, post_τ)` with `post_τ` =
  `out.trie` / `applyMissingChunk` result; `unfoldBytes` unchanged in form. Removed
  `revealedStore`, `triesD0N`, `unfoldBytesN`, `a11` and the A11 conjunct of
  `RelD0a`/`checkD0a`/`inD0a`/`InD0a`; `relD0a_iff`, `relD0a_mono_all` re-proved. `diffT` and
  `rebuildPost` kept as legacy (difftest measures `unfold_diff`, `unfold_rebuilt`; zk-formal
  store lemmas still state facts about `rebuildPost`). `schedInsD0` reads only the pre tries
  (unchanged); no other spec module uses `triesD0`.
* Difference native vs rebuilt (absent collisions): an insert of `0x0f` that splits a leaf or an
  extension creates a node (shortened old leaf / extension tail) off the read keys; the native
  trie reveals it, the rebuild along the keys does not. Requires `0x0f` absent in the pre-state:
  0 splits on public D0a, d1run, d2corpus.v2.
* Python `spec_check_v3_d0a.py`: `RecTrie` records, per insert, the absolute positions of the
  nodes it creates (the new path, plus the split-off node computed on the pre-insert trie) and the
  written values; `unfold_native` walks the post root: a node is revealed iff created at that
  position or a read key passes through it (then read from the pre store), a value iff written
  there or wanted and in the pre store — Lean's `unfoldedBytesT out.trie`. Position-based, not
  hash-based (a hash test would misfire on an unread sibling identical to a created node).
  Fields: `unfold` (native), `unfold_rebuilt` (2026-10-11), `unfold_diff` (pre-2026-10-11);
  `unfold_n`/A11 dropped. `difftest_v3_d0a.py` MEASURES/AMENDMENTS updated;
  `a11_measure_v3_d0a.py` deleted.
* Lean tool `CheckD0a`: local `triesD0Rebuilt` for the legacy measures; prints `unfold_rebuilt`
  instead of `unfold_n`.
* Split vectors (`docs/e2e-results/v3-a7-native/split_vectors.py`): 7 synthetic tries (leaf
  split, ext split, moved child, branch new leaf, overwrite; read/unread): Lean
  `unfoldedBytesT (t.upsert …)` = Python `unfold_native` on all 7, incl. 3 where native ≠ rebuilt.
* zk-formal: `GoodV3`/`ExtFieldsV3` drop `postRebuild`; `GoodV3.amendments`, `GoodV3.checkD0a`,
  `good_of_native` (two premises now), `NativeUnfold` (`unfoldedPairs` = `(s.pre, s.post)`,
  `triesD0_native_result` with `m.result.trie`), `UnfoldStoreEq` (`unfoldStep`), `SrcpDepth`
  (positional `.2…` back to 7). `FactorComplete` simplified: `tries_reconstructed : triesD0
  (rec.) = triesD0 (orig.)` — same pre tries, same execution, hence the same native posts; the
  `triesD0N`/`unfoldStepN`/`revealedStore` machinery is gone.
