# lane/v3-prover-rcptfam — receipt-side tables from claim + witness (2026-10-13)

**Base.** `lane/v3-prover` `28e1c68f`; merged `origin/lane/v3-prover-prep` (hintOf / prep), then
`origin/main` (`bb37a433`, later `99f99e76`) and `origin/lane/v3-prover-fixtures` (`c0185a63`, the
extra fixtures). Lean sources untouched (only `conformance/`).

## Gap closed

The SHA collector's receipt family (`RC` + gated digests, `PEO`/`LEAF`/`RID`, account `VPOST`,
outcome Merkle) was fed from Lean (`np-lean-shabins-v3` → `sha_receipt.json`), and tables 16–20,
23, 24 had no real-witness input in Rust.

## Rust: `src/v3/rcptfam.rs`, `npudr v3rcptfam`, `npudr v3sha --native`

From `claim.bin` + `witness.bin` only: `walkD0`, `decodeW`, `appliedReceipts`, `m.pre`
(`partialTrie … mainKeys`), `hintOf` + `prepD0` (lane prep), `sourceInputLists`, then the receipt
ledger (`applyReceipt` / `applySystemReceipt` in order, the account each receipt reads), and:

* table 16: the `RcptIn` list view of `AcceptedV3.rcptInput` — every `RcptE` field from its
  native row constructor (`kslot` = `valueIndex` of the receiver account in `m.pre`, `tprev` =
  `latestReceiverVersion`, `bef/lk/st/aft` = `nativeDepositData` bytes, `ge/sys/ee`, `gv/gs/sx`
  = `systemAux`, `rfid` / `peoh` / `burnt` / `ramt` from `nativeOutcome`, `akf/akk` = `accessId`,
  `aku` = `rankAux`, `q`/`iv` = `nativeRoutingIndex` / bounded interval, `rlk` = the routing frame
  rows with `gBd`, `u = 0` = the native pre-`counterPatch` `uB`), `n0/n1`, `own/height/bgp`;
* 17 `nativeAccountViews` (distinct touched keys, closing versions, `valsOf` ordinals);
* 18 `NativeAccessKeyProviders.providers`; 19 `boundaryEntries (boundedIntervals …)` over the
  physical keys of the `rlk` rows; 20 `DedupCompile.blocks` + `sourceRepeated`;
* 23 `MrkV` of `levelTable (outcomePreimages os)`; 24 `NativeSortIds.sorted`.
* helpers `vals_of` / `value_index` (`NearSpecV3.valsOf`, `Assembly.ValueIndex`).

`npudr v3rcptfam <claim> <witness> <dir>` writes the entry files, `sha_receipt.json`
(`collect::receipt_family`) and `rcpt.prefix.bin` (planned + 8 rows of table 16).
`npudr v3sha … --native <claim> <witness>` computes `rcpt/acct/srcp/mrk` in-process and ignores
any `sha_receipt.json`: **the receipt family is built purely in Rust** (the trie/scheduler
families still read node/val/ups/codec entries; those dumpers belong to other lanes).

Not mechanised (covered by the differential): the ledger runs on `m.pre` rather than the
post-`schedStep` trie (only `[0,15]` differs; same argument as `hint.rs`); `valsOf oldPost` at an
account index = the receiver's final bytes.

## Lean: `conformance/RcptFamV3.lean` → `np-lean-rcptfam-v3 <case> <dir> [max_rows]`

Runs `checkD0a B0`, rebuilds the `AcceptedV3` objects (account-write replay root-checked as in
`np-lean-shabins-v3`) and evaluates the accepted-render definitions: `acceptedRcptInput …`
(exactly `AcceptedV3.rcptInput`), `rcptTraceNative` → view + prefix rows of
`patchTrace (counterPatch …)`, `boundaryEntries … (physicalBoundaryKeys)`, `nativeAccountViews`,
`providers`, `DedupCompile.blocks`/`sourceRepeated`, `mrkLevels` (through `levelTableFast`, a
linear-time twin with the proved equation `levelTableFast_eq`), `NativeSortIds.sorted`, and the
receipt family. No sorry/axiom/native_decide/implemented_by. Table-16 parts only when planned rows
≤ 4000 (each Lean cell walks the plan: 2,034 rows ≈ 60 s); the three fixtures with 496/711/814
receipts (95k–156k rows) are "untraced".

## Differential: `run-v2.d/rcptfam.sh` (283 PASS, 0 FAIL, ~10 min with cached Lean dumps)

* 81 fixtures (64 `public-d0a/d0` + 17 `fixtures-extra/d0`: repeated source keys, empty values):
  acct, akey, srcp (incl. dup/rep), sort, mrk (n + levels), the receipt SHA family identical on
  all 81; rcpt view (all fields + iv), bnd and the table-16 prefix rows byte-identical on the 78
  traced ones. Untraced 3: view checked indirectly (the Rust family built from the Rust view equals
  Lean's family built from native outcomes) + `v3check`.
* `npudr v3check` accepts the Rust table 16 on all 81 (incl. log 18 for 814 receipts).
* collector `v3sha --native` == `np-lean-shabins-v3` on all 81: four families, b0/b1, cap; bus
  check: no unmatched sends/receives, 0 bytes uncovered.
* Renders of the real Rust entries byte-identical Lean vs Rust (acct, srcp, mrk 2^19, sort, akey,
  bnd) on 3 public + 2 extra (duplicate-key) fixtures.
* Negatives (9): the 3 fixtures-extra mutants rejected by `checkD0a`; truncated witness rejected by
  `v3rcptfam`; tampered acct post / rcpt peoh / rcpt dep / srcp leaf / mrk node → bus check fails;
  tampered rcpt `bef` (a MEM-bus field) → caught by the differential.

Rust run time: ≤ 0.4 s / 500 MB per fixture (814 receipts incl. the 156k-row prefix).

## Checks

`cargo fmt --check` clean; clippy: no findings in the new code (total 112, all pre-existing);
`cargo test --release`: 122 passed, 0 failed, 2 ignored (incl. `v3::rcptfam` 3/3); `make pin-check` OK.

## Remaining for a real proof

* qv (22) needs the implicit-step pre-tries (`traceImplicit`) — not ported; size (21, A7) and
  the trie/scheduler entries (node/val/ups/codec/walk/uniq/head, scheduler blocks) still come
  from Lean dumpers (other lanes).
* the full table 16 is `2^22 × 263` cells (4.4 GB as u32) per proof.
* a v3 `prove` over all 25 tables (balanced bundle) is not wired.
