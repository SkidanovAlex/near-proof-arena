# lane/v3-prover-prep — native preprocessing for the np-udr-stark-v2 prover (2026-10)

## 2026-10-12

**Base.** `lane/v3-prover` `a097ce09`, then merged `origin/main` `c2bd648b` (A12 in `prepClaim`,
SRC34 public source rows). Conflict in `src/v3/mod.rs` resolved to the lane's render dispatch,
as `lane/v3-prover`'s own merge `37784327` does.

**State found.** `src/v3/d0.rs` already had `prep_claim`/`prep_body`/`prep` (commit `77e0486f`); the
README row "prepClaim/prepBody not ported" was stale. Review against main's `PrepD0.lean` found:
* A8 (`c.bw_requests`, distinct `to_shard` per chunk) was **missing** in Rust `prep_claim` — added.
* A12 (`c.layout_wf`, `|boundaries| + 1 = |shardIds|`, main `c2bd648b`) — added after `allowed`, as Lean.
* `prep_body` computed `(n - 1)·G` and `n·G` in `u64`: `n < 2^32`, `G ≈ 2^37.7`, so the product can wrap
  (a wrapped `n·G` could equal `prev_gas_used`). Now `u128` (Lean `Nat`).
* the `allowed_shard` index `(height + idx) % numShards` now in `u128`.

**Ported: `hintOf`** (`src/v3/hint.rs`), the Rust twin of `NearSpecV3.hintOf`:
`decodeWitnessFile`/`decodeStateWitness` (`decodeW`), `pReceipt`, `lookupLast`,
`appliedReceipts` (shuffle with `.getD` fallback), `partialTrie` = `buildFor (mkStore values) 400`
(`hpDecode`, `mkSlot`, `branchWith`/`kidHashes`), `PTrie.find`/`get`/`set` (set in place),
`bufferedShards`, `mainKeys`, `keyAccessKey`/`keyGroupsData`, `TransferV1.applyReceipt`,
`applySystemReceipt`, `refundsUpTo`, `hintOfE`/`hintOf`.

`hintOfE` takes `out.outgoing` of `applyNewChunk` on success and `refundsUpTo` on failure. The Rust
port computes `refundsUpTo` in both cases, without the scheduler `runCore`: the two differ only in
the trie (applyNewChunk upserts `[0,15]` first); receipts touch only `[0,0,…]` (accounts) and
`[0,2,…]` (access keys); `get = (find ·).join` and `set` succeeds iff `find = some (some _)` by the
definitions; `PTrie.find_upsert_other` (proved, `NearSpec.TrieUpsertProofs`, for wf tries) keeps
`find` on every other key. Not mechanised (documented in the module docs); covered by the
differential below.

**CLI.** `npudr v3prepare <claim.bin> <witness.bin> <out_dir> [--hint <hint.bin>]`: `hint.bin`
(always), `prep.bin` + `prep.json` and exit 0 on acceptance, `reject.txt` and exit 1 on rejection.

**Lean side.** `conformance/PrepV3.lean` gains `np-lean-prep-v3 --any <claim> <witness> [<hint>]`:
`checkD0a B0` verdict, `Hint.encode (hintOf cb wb)`, and `prepD0 cb h` (h = hintOf, or the given
hint) without requiring acceptance. No `sorry`/axioms; built in 384 jobs after the main merge.

**Differential** (`run-v2.sh` §"prover preprocessing", run standalone with the D0-prep section):
* 64/64 `public-d0a/d0` fixtures: Rust hint bytes == Lean `hintOf`, Rust `Prep.encode` == Lean
  (refund counts 0/1/2/3/4/6 over the set; `n` up to 814).
* the existing "D0 native preprocessing" section (Rust prep from the Lean hint): 64/64.
* mutations on 8 fixtures, 120/120 agree:
  * claim (pv, A12 surplus boundary, tx flags, genesis extra, epoch start, chunk-inner
    `prev_gas_used`, `prev_outgoing_receipts_root`, RS params, truncation): Lean `checkD0a B0`
    rejects and Rust `v3prepare` rejects, with the same `prepD0` verdict as Lean; the A12
    mutation is rejected by Rust with `out of domain (c.layout_wf)`;
  * hint (`n+1`, trailing body byte, `Hint.empty`): Rust and Lean `prepD0` agree (reject, or accept
    when `Hint.empty` is the honest hint);
  * witness (byte flips, truncation): Rust hint == Lean `hintOf` (incl. the `Hint.empty` decode
    failure path) and the `prepD0` verdicts agree.

**Checks.** `cargo test --release`: `v3::hint` 3/3; the 7 `v3::{mrksort,rcpt,sha}` failures are
pre-existing (they read `conformance/out-v2/nearAirV3.json`, which only a full `run-v2.sh` writes).
clippy finding count unchanged by this lane (111 before/after); rustfmt clean on the touched files
(`mod.rs`/`public.rs`/`prove.rs` already differ from rustfmt on the lane — left to the sibling).
`make pin-check` OK.

**Not done / for the merge.** README line 24 (status paragraph) still says `hintOf` needs D0
execution — left untouched to avoid conflicting with `lane/v3-prover`; the part-3 row is updated.
The "prepared public tape" section of `run-v2.sh` needs `public.rs`'s SRC34 update (sibling lane).
