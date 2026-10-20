# P4: the cached TAPE root in the statement V_d checks

Lane `pq-stream-commit`, from `lane/pq-state-port`'s P4 finding.  Patch:
`native/recursion/patches/p4-tape-statement.patch` (72 lines, one file).

## The finding, verified

`lane/pq-state-port` proved `tapeNet_canon`: the canonical TAPE carries the net public
multiplicity, so **under commitment binding** `VdChecks.tape` holds.  The remaining question was
whether that binding actually reaches V_d.

It does **not**, and the reason is precise.  Three facts, each checked in the tree:

1. The base verifier *does* observe cached commitments into its transcript
   (`stark-backend-unified/crates/stark-backend/src/verifier/mod.rs:165`), and the NV circuit
   re-derives that transcript (`transcript/merkle_verify/trace.rs:553` puts each
   `cached_commitments` entry into the stacking-commit list).  So a cached table's root **is**
   bound to the base proof.
2. But `nv/verifier.rs:940` computes the statement as
   `statement_digest(&proof.public_values)` — the base proof's **public values only**.
3. `VdSetup` pins the final vk, the NV program and the level (`vd.rs:109` `check_final_program`,
   `vd.rs:126` `verify_final`).  A cached commitment is never among those.

So the TAPE root is bound to the *base* proof but is invisible to the statement V_d checks.  A
final proof over a base whose TAPE table was anything at all would pass every check we have.

This is exactly the pattern `pq-wasm-base` used for CODE (`results/pq-wasm-base/STATEMENT.md`
§2: "`code_root`: the base proof's cached commitment for CODE"), and the same gap applies to it.

## The patch

In `nv/verifier.rs`, in the app (non-`child_nv`) statement branch, append every cached commitment
to the hashed statement:

* collect `cached_cells` (the `DigestCells` the preamble already loaded for the stacked PCS) and
  `cached_limbs` (`fmt::digest_limbs`, 18 field limbs per digest);
* append the limbs to the host-side `stmt` vector, and the corresponding 12 + 6 limbs to the
  in-circuit `cells` vector, in the same order;
* the length list gains one `NV_DIGEST` entry per commitment.

`statement_values` is `[#vecs, len_0.., flat..]`, so the length list and the flat list must both
grow or the in-circuit SHA job and the host-side digest diverge — and then *every* proof fails.

The extra work is 18 ALU ops per cached commitment, once per statement.

## What it costs, and what it does not touch

* **Program rows.**  The probe reports 133,516 rows for the Fib child, which already needs
  `NV_PROG_LOG=18` (the default 17 overflows at 2^17 = 131,072).  With no cached mains in the
  probe's child the row count is unchanged; each cached commitment adds ~18 rows.
* **Recorded artifacts.**  This **changes the statement format**, so the recorded G2 gate proofs
  (`results/pq-stream-commit/g2-gate/`, sha256-pinned in `MANIFEST.json`) no longer match.  They
  must be re-run after this lands.  That is why the patch is committed as a patch rather than
  applied to the shared deps tree: the gate is a signed artifact.
* **No cryptographic change.**  The digest is still SHA-384 tag 8 over `statement_values`; only
  the list hashed is longer.

## Status: typed, not yet exercised

Applied to `/data/illia/nearproof-deps/pq-stream-g2/openvm-sha384` and **type-checked**
(`cargo check -p openvm-recursion-circuit` passes), then **reverted**, because the patch changes
the statement format and would invalidate the sha256-pinned G2 gate artifacts.

**Not yet run end to end.**  The existing NV tests use a `FibFixture` child, which has no cached
mains, so the new branch is dead code there and the probe row count is unchanged (133,516).  To
exercise it a test needs a base proof with a TAPE-like cached table — the tree already has
`PreprocessedCachedAir` (`stark-backend/src/test_utils/dummy_airs/preprocessed_cached_air/`),
which is the right fixture, but wiring it as an NV *child* (rather than a preprocessed parent) is
the remaining work.  Until then the patch is "compiles, semantically argued, unexercised".

The gap itself is certainly real: `statement_digest(&proof.public_values)` at `nv/verifier.rs:940`
cannot see a cached commitment, and `VdSetup` pins only vk/program/level.

## Next three steps

1. Build `nv_cached_statement` (test size): `PreprocessedCachedAir` as the child, NV over it, and
   assert (a) the honest chain verifies, (b) a child whose cached root is swapped is rejected by
   `check_statement`.  That is the proof the patch works, and the negative case is the one that
   matters.
2. Re-run the G2 gate with the patch (`run_g2_chain.sh`) and re-pin `MANIFEST.json`.
3. Port the same change to `lane/pq-host-chip`'s base driver: its `check_statement` compares the
   TAPE root against the recomputed one in-process, which is the same check V_d now performs from
   the statement.
