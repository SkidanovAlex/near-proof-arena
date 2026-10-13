# Lane `oracle-d0a` — D0a nearcore oracle on the current RelD0a (2026-10)

Worktree `/data/illia/nearproof-wt/oracle-d0a`, branch `lane/oracle-d0a` from main `d6725367`.
Task (HANDOVER §5 "Oracle"): `oracle/v3-d0a/src/d0a.rs` still computed the pre-2026-10-11 A7
measure (`diffT`); bring it to the current relation (A7 = unfolded pre trie + **native** post
trie ≤ B0, A11 retired, A12 `c.layout_wf`), regenerate the D0a fixtures, re-run the 3-way
difftest. Frozen `oracle/v3`, signed challenges and pinned files untouched; `public-d0a` and
`oracle/v3-d0a` are not pinned (`spec/tools/check_oracle_pins.py`).

## 2026-10-13

### Oracle changes (`oracle/v3-d0a/src/d0a.rs`, `chaingen.rs`)

* **A7 native measure** (`unfold_native`), on nearcore's `RawTrieNodeWithSize`, independent of
  the Lean/Python code: walk the post trie from the tracking node's State column; a post node is
  *created* iff the pre trie (witness values) does not hold the same node hash at the same
  absolute nibble position (`pre_at`: child reference read from the parent, so the node itself
  need not be recorded) — position-based, as Lean's `upsert` result, not a hash-set test. A
  created node is revealed with all its children; an untouched one only along the read keys. A
  value counts iff it is in a created node and differs from the pre trie's value at the same
  key (`pre_value`: written; length from the post store) or a read key ends at it and the
  witness holds it. This reveals the split-off node of an insertion (`splitLeaf`/`splitExt`)
  that the rebuild along the read keys misses.
* Legacy measures kept for the difftest: `unfold_rebuilt` (post trie rebuilt from the State
  column along the read keys) and `unfold_diff` (the old `unfold_diff`, unchanged code).
  `meta.json`: `unfold_bytes` = native (was diffT), new `unfold_rebuilt`, `unfold_diff`.
* **A12** `c.layout_wf`: `layout_wf` on nearcore's `ShardLayout` of every epoch of the claim
  (blocks + witness epoch): `boundary_accounts().len() + 1 == shard_ids().count()` (V0 → false).
* `extra` now takes the A7 value and lists violations in Lean `checkD0a` order (A1, A2,
  Canon0f, A7, A8, A9, A10, A12); `w.unfolded` was appended last before. Ood family keys are
  per violation set, so the ood selection is unchanged.
* Rest checked against Lean `checkD0a`/Python: A1 (B2 own slot `gas_limit`), A2 (every receipt
  of every proof; honest witness = used proofs), Canon0f, A8 (every chunk of every claim block),
  A9 (scheduler replica, words), A10 (max path length) unchanged and matching.

### Difftest tool (`oracle/tools/difftest_v3_d0a.py`)

* Oracle fields: `unfold_bytes` ↔ Lean/Python `unfold`, `unfold_rebuilt` ↔ `unfold_rebuilt`,
  `unfold_diff` ↔ `unfold_diff` (was: oracle `unfold_bytes` ↔ `unfold_diff`).
* Corpora without nearcore D0a metadata (no `expected_rel_d0a`, i.e. D1/D2 corpora; subdirs
  `d1`/`d2` now scanned): Lean and Python must give the same verdict, and Lean's (first)
  amendment family must be the first of Python's.
* Sanity: on the *old* public metadata the new comparison reports 48/64 `unfold_bytes`
  mismatches (stale diffT values vs native) — the check is live.

### Build

* `oracle/v3-d0a`: fresh target (no reusable one existed), `cargo build -j 4` on CPUs 8-11,
  ≈ 35 min. (The crate has never been `cargo fmt`-clean, incl. the frozen shared `oracle/v3`
  modules; not reformatted.)
* `nearspec-v3-check-d0a`: deleted `ChunkValidationV0a` and `CheckD0a` build products and the
  exe, rebuilt (91 jobs) — no stale binary.

### Regeneration of `oracle/fixtures/v3/public-d0a`

Command (reconstructed and confirmed byte-for-byte): `near-arena-oracle-v3-d0a gen --seed 4243
--chains 2 --blocks 40 --mutate-every 25 --ood-cap 1`.

* Same file set (64 d0 / 59 ood / 298 mutants); **every `claim.bin` and `witness.bin` is
  byte-identical** to the committed one (842 files); `summary.json` identical.
* Changed: `meta.json` of the 123 honest cases (64 d0 + 59 ood) only — `unfold_bytes` now the
  native measure, plus `unfold_rebuilt`, `unfold_diff`. Mutant metas unchanged. The new
  `unfold_diff` equals the old stored `unfold_bytes` on all 123 (legacy code path reproduces).
* So no prover-facing bytes change; metadata replaced in place (fixtures-extra unaffected: it
  reads only `d0/*/claim.bin`/`witness.bin`).
* d0: native = rebuilt on all 64 (max 7,996, case `01-h10025-s1`; diffT max 6,500). ood: native
  > rebuilt on 35 of 59 — those runs are outside D0 and write keys D0 never reads (outgoing
  receipts, tx effects), so created subtrees off the D0 read keys count; Lean/Python do not
  measure them (`checkD0` fails first); max 192,343 ≪ B0.

### Difftests (Lean `nearspec-v3-check-d0a` vs Python `spec_check_v3_d0a.py` vs oracle)

| corpus | cases | disagreements | `unfold` L=P / =oracle | `unfold_rebuilt` | `unfold_diff` | A9 / A10 =oracle |
|---|---|---|---|---|---|---|
| public-d0a (committed, regenerated meta) | 421 | **0** | 300 / 64, 0 mismatches | 300 / 64, 0 | 300 / 64, 0 | 300 / 300, 0 |
| fixtures-extra (np-udr-stark-v2 conformance) | 20 | **0** | 17 / – (no oracle), 0 | 17, 0 | 17, 0 | – |

Report: `oracle/fixtures/v3/public-d0a/difftest.json`. Amendments on 290 honest witnesses
(oracle): all 0 incl. `c.layout_wf`. Full / heavy-request / D1 / D2 corpora: below.
