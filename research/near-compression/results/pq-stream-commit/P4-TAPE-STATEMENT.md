# P4: the cached TAPE root must enter V_d's statement

Two pieces:

1. `p4-tape-statement.patch` — `crates/recursion/src/nv/verifier.rs`: append every cached
   commitment to the hashed statement, in both the host-side `statement_values` and the in-circuit
   SHA job.
2. `p4-statement-test.rs` — the test `nv_stmt_covers_cached_root`, appended to
   `crates/recursion/src/nv/tests.rs`.  It uses `PreprocessedAndCachedFixture` (a child with a real
   cached main, the shape TAPE has) and asserts:
   * the NV program exposes exactly `statement_digest(public_values ++ cached_limbs)`;
   * that differs from the public-values-only digest;
   * a swapped cached root gives a different statement.

## Measured

* **With the patch:** `nv_stmt_covers_cached_root` passes; `NV_STMT cached root in statement:
  [10140264729909534252, …]`.
* **Without the patch** (the same test, unpatched verifier): **fails** —
  `left: Some([7710059181541593952, …])` vs the expected P4 digest.  So the test is live, not
  vacuous: it detects the pre-P4 behaviour.
* **Regression:** `cargo test -p openvm-recursion-circuit --lib nv::` → **64 passed, 1 failed,
  4 ignored**.  The one failure is `nv::prep_tests::nv_prep_cached`, which **also fails on the
  unpatched tree** (verified by restoring the baseline and re-running), so it is pre-existing and
  unrelated.

## The G2 gate is NOT invalidated (measured, not assumed)

The gate's chain is `FibFixture` → `FibonacciAir`, which has **no cached main**, so the patched
branch is not reached and the statement digest is unchanged.  Measured directly: the Fib child's
statement digest is `[495754296698778413, …]` with **and** without the patch — identical.  So
`g2-gate/MANIFEST.json`'s proof hashes stay valid and no re-run is needed.

(A re-run would in any case not discriminate: it would reproduce the same bytes, which is why it is
the wrong check for this change.  The discriminating test is `nv_stmt_covers_cached_root`.)
## What P4 does NOT cover, and where it has to go next

`tapeNet_canon` + this patch answer "does the cached TAPE root reach V_d?" — yes.  They do not
answer "does a *real NEAR-shaped* base run through the NV chain?".  Today's harness is
`FibFixture`, which has no cached table; the discriminating test above uses
`PreprocessedAndCachedFixture`, which has one but is not NEAR.  Feeding `pq-state-port`'s 25/30-table
base proof into `nv_chain` is the remaining integration, and it is sized by the recursion harness,
not by the statement change.

## Payload

* `native/recursion/patches/p4-tape-statement.patch` — the verifier change (72 lines).
* `native/recursion/patches/p4-statement-test.rs` — the test (59 lines; append to
  `crates/recursion/src/nv/tests.rs`).

Apply with `patch -p1` from the `openvm-sha384` tree, then run
`cargo test --release -p openvm-recursion-circuit nv::tests::nv_stmt_covers_cached_root`.

## Reproduce the negative case

Restore the pristine `nv/verifier.rs` (`git checkout -- crates/recursion/src/nv/verifier.rs` in the
deps tree) and run the same test: it fails on the statement assertion, which is what shows the
test exercises the gap rather than passing trivially.

## Verification performed

Applied from a pristine deps tree with `patch -p1` (dry-run clean), test appended, then:

```
NV_STMT cached root in statement: [10140264729909534252, ...]
test nv::tests::nv_stmt_covers_cached_root ... ok
```

and the deps tree was restored to pristine afterwards, so the recorded G2 artifacts stay valid.
