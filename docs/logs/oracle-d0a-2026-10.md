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
| fixtures-extra (old, 17 + 3) | 20 | **0** | 17 / – (no oracle), 0 | 17, 0 | 17, 0 | – |

Report: `oracle/fixtures/v3/public-d0a/difftest.json`. Amendments on 290 honest witnesses
(oracle): all 0 incl. `c.layout_wf`. Full / heavy-request / D1 / D2 corpora: below.

### Checkpoint 2 (after merging origin/main `92c9dc08`; coordinator messages)

**Python A7 fix on main (`75818749`, lane v3-prover-cover):** created nodes keyed by
(position, hash), since a non-canonical empty-key extension shares its position with its child
(x-ups-pt: Python 6,144 vs Lean 7,178). The oracle had the same blind spot: `pre_at` returned
one node per position and stopped at an empty-key extension. Now `pre_at` returns every pre node
starting at the position (the node and, below empty-key extensions, their children);
`pre_value` descends through empty-key extensions.

**Offline oracle A7 for constructed cases** (nearcore cannot judge them: their blocks are in no
store). `near-arena-oracle-v3-d0a unfold-case --dump F` (`d0a::unfold_offline`): witness decoded
with nearcore borsh; read keys from nearcore types (all source-proof receipts — = used ones,
all own-shard under A2 — and `BufferedReceiptIndices` read with nearcore's
`Trie::from_recorded_storage`); post nodes/values from preimage blobs dumped by
`oracle/tools/dump_a7_store_v3_d0a.py` (stored under their own SHA-256; the walk starts at the
witness's post roots, so the blobs cannot steer the count); the counting is the oracle's own
code (same `measure` as the online path). External input besides preimages: the main pre root
(the claim's B2 own-slot `prev_state_root`). Cross-checks: offline = online on all 64 public
d0 cases (3 measures, 0 mismatches); oracle read keys = Python's on all 103 measured cases.
`difftest_v3_d0a.py --oracle-jsonl` uses it where `meta.json` has no oracle measures.

**Empty main pre-state (user decision 2026-10-13: not in RelD0; Lean already rejects).**
* Python `spec_check_v3_d0a.py`: if the D0 checker built its main pre trie (i.e. passed its
  claim-level checks) on root `0^32` and did not already reject, verdict `reject`, reason
  `invalid: MissingTrieValue (BufferedReceiptIndices): empty main pre-state` (Lean: `invalid:
  MissingTrieValue (BufferedReceiptIndices)`, same place: after the claim-level checks, before
  any runtime check). The pinned D0 checker is unmodified.
* Oracle: `d0a::main_pre_empty` (chaingen: `expected_rel_d0`/`expected_rel_d0a` false; never
  triggers on chaingen data) and `unfold_offline` → `reject`.
* Difftest case `oracle/fixtures/v3/public-d0a/mutants/00-h10004-s3-w.empty_pre_state`:
  `gen_extra_d0a.py --base …/d0/00-h10004-s3 --state keep:` (sha256 claim `61cccc29…`, witness
  `c4a55200…`), meta `expected_rel_d0a = false`, `expected_verdict = reject`,
  `expected_reason = MissingTrieValue (BufferedReceiptIndices)`, provenance in meta. Not
  produced by chaingen: a chaingen regeneration must re-add it (command in its meta).
  Prover conformance reads only `public-d0a/d0`, so nothing it uses changes.
* Spec v0a §1: clarification paragraph (no change to the Lean relation).
* Re-check: `gen --seed 4243 --chains 2 --blocks 40 --mutate-every 25 --ood-cap 1` with the
  final binary reproduces `public-d0a` exactly (`diff -r`: only `difftest.json` and the
  hand-added mutant differ).

| corpus | cases | disagreements | `unfold` L=P / =oracle | `unfold_rebuilt` / `unfold_diff` | A9 =oracle | notes |
|---|---|---|---|---|---|---|
| public-d0a | 422 | **0** | 300 / 64, 0 | 300 / 64, 0 each | 300, 0 | empty-pre-state mutant: Lean reject, Python reject, oracle offline reject |
| fixtures-extra (39 d0 + 3 mutants) | 42 | **0** | 39 / 39 (offline), 0 | 39 / 39, 0 each | 39, 0 | incl. x-ups-pt 7,178; x-bw-* up to 597 words |

Reports: `oracle/fixtures/v3/public-d0a/difftest.json`,
`docs/e2e-results/v3-oracle-d0a/fixtures-extra.json`.

### Larger corpora (scratch, not committed; reports in `docs/e2e-results/v3-oracle-d0a/`)

Generated with the final oracle binary; Lean (rebuilt `nearspec-v3-check-d0a`) and the final
Python on every case unless noted.

| corpus | cases | disagreements | `unfold` L=P / =oracle | `unfold_rebuilt`, `unfold_diff` | A9 =oracle | honest amendments (oracle) |
|---|---|---|---|---|---|---|
| full: `gen --seed 4243 --chains 9 --blocks 120` (= the earlier full set: 907 / 2,131 / 10,268) | 13,306 | **0** | 5,230 / 927, 0 | same, 0 | 5,230, 0 | 4,597 honest: c.gas_limit 599 (chain 8), all others 0 incl. c.layout_wf |
| heavy requests: `gen --seed 4243 --chains 6 --blocks 120 --heavy-requests` | 9,997 | **0** | 3,829 / 724, 0 | same, 0 | 3,829, 0 (max 12 words) | 2,703 honest: all 0 |
| d1run (nearproof-deps/corpora, D1 oracle) | 9,734 of 53,048 | **0** | 3,977 / –, 0 | same, 0 | – | – |
| d2corpus.v2 | 10,943 of 67,384 | **0** | 38 / –, 0 | same, 0 | – | – |

d1run / d2corpus.v2 have no D0a oracle metadata (generated by the D1/D2 oracle): Lean vs Python
only (`difftest_v3_d0a.py --case-list`, verdict + amendment family). Python ran on all 120,432
dirs; Lean on every honest dir (d1/d2/ood) and every mutant on which Python passes RelD0
(i.e. the D0a part is reached); mutants Python rejects inside D0 are a D0-checker question and
were not re-run. A7 maxima in RelD0a: full 9,998, heavy 21,436, d1run 12,402, d2 9,624 (B0 =
2,000,000); native = rebuilt on every accepted case of every corpus.

Wall (CPUs 8-11 shared): Lean ≈ 4 cases/s with 4 processes; Python ≈ 350 cases/s.
