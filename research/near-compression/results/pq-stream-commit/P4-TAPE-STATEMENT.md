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

## Still to do

* The patch changes the statement format, so the sha256-pinned G2 gate artifacts
  (`results/pq-stream-commit/g2-gate/`, `MANIFEST.json`) are stale.  Re-run `run_g2_chain.sh` and
  re-pin before treating the gate as closed.
* The same statement change must reach `lane/pq-host-chip`'s base driver (`check_statement` there
  compares the TAPE root in-process today).

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
