# v3-render-rcpt lane log (receipt-side completeness)

Branch `lane/v3-render-rcpt` from main `fb3dec71`.  Goal: honest aligned trace generators
(`*TraceAligned`, `*_aligned_complete`) for the receipt-side tables of `nearAirV3`
(16 rcpt, 17 acct, 20 srcp, 21 size, 22 qv), pattern `Render/Padded.lean`.

## 2026-10-11

* **acct (17), size (21): aligned renders done** — `NearV3/Render/PaddedRcpt.lean`:
  `acct_aligned_complete` (cap 19), `size_aligned_complete` (cap 4), `acctV3Ok_wf`.
  Audit `test/AuditPaddedRcpt.lean`.
* Both honest heights exceed the natural caps (acct: 16·4481 = 71,696 rows > 2^16, so
  logOf = 17 → padLog22 = 19; size: 4 rows, 2 → 4).  Views generalized to a cap:
  `AcctV3Proof.*` take `TableLocal {AcctV3.table with maxLog := cap}` (+ `hcap : cap ≤ 22`
  where `height < P` is needed); `acctV3_view_at cap` with `AcctV3WfAt cap`;
  `size_view_at cap` (rows ≥ 3 are padding at any height ≥ 4: `padF`, `runF`).
  The old `acctV3_view`/`size_view` are the cap-17/cap-2 instances.
* Renders: `acctV3_render_local_at`/`_traffic_at`, `size_render_local_at`/`_traffic_at`
  (any height ≥ rows); old statements derived.
* **CAP CHANGE (separate commit):** `nearAirV3` table 17 `acctV3` → `maxLog 19`, table 21
  `sizeV3` → `maxLog 4` (`NearAir.lean`, `ExtractV3.lean` literal/lookups/locals,
  `ViewsV3.acctView` now `AcctV3WfAt 19`, `sizeView` via `size_view_at 4`).
  `nearAirV3_wf`, `nearAirV3_npOkPg` re-checked by kernel (NearAirCheck rebuilds).
  **Aligned size bound `nearV3_size`: 6,276,897 → 6,315,201 B** (+38,304) at auxGroup 2;
  margin under 8 MiB after the 1,295,017 B hint: 778,390 B.  `v3MaxInner` updated
  (`4 + 2,000,000 + 6,315,201 ≤ 8 MiB` still holds).  Full `ZkFormal.V3.Integration` builds.
* **srcp (20): aligned render done** — `NearV3/Render/PaddedSrcp.lean`:
  `srcp_aligned_complete` (hypothesis = the view's `SrcpWf bs`; cap 22 unchanged),
  `srcp_proofs_aligned_complete` (from the used source proofs, `ProofInputsOk`),
  `SrcpGen.table_local_at`, `SrcpGen.cell_high`.  `Srcp/ProofComplete` now reaches
  Integration through it.  Audit `test/AuditPaddedSrcp.lean`.
* **qv (22): aligned render done** — `NearV3/Render/PaddedQv.lean`:
  `qv_aligned_complete` for `KeyTrafficRepair.table` (the actual `nearAirV3` table 22, cap 22)
  on the existing honest mixed queue rows (`mixedTrace (plan pre v pres resolve) vs`), at
  `padLog22 (logOf qvRows)`.  New: the repaired-`KEYNIB` row/word traffic
  (`Walk.repairedKeyMessages`, `Walk.repairedKeyWordMessages`: zero-based nibbles, no START,
  END at `2·len` — the shape of `Qv.Extract.repairedKeyTraffic`), `repairedTraffic`,
  `mixedTrace_repaired_traffic`, `placed_words_traffic_is` (any interaction list), and
  table-index reindexing (`tableLocal_reindex`, `tableTraffic_reindex`).
  Hypothesis `QvOk`: `v.Valid`, records valid, `qvRows ≤ 2^22`, and the public implicit
  count (`kPublic`, pub 26..29) = `pres.length`.
  **Caveat:** there is no `qvV3` soundness view statement yet (not among the eleven views), so
  `repairedTraffic` is the honest-side record format; the view lane must target it (or a
  bridge must be proved).
* **rcpt (16): NOT done — completeness for the frozen `RcptV3.table` is believed FALSE on the
  honest D0a domain.**  The rcpt render-candidate lane (`docs/zk-formal/RCPT-RENDER-CANDIDATE.md`,
  `Assembly/Rcpt*`, 832/881 original constraints covered on one physical trace) has two
  proved local obstructions in the active table:
  - `Assembly/RcptDepositContradiction.lean:old_deposit_initial_512_impossible`: the
    first-DEP-row constraint `r − tprev = bitsX 57 9` (`Rcpt/Tables/Rcpt/Arith.lean:310`) is a
    9-bit age, so receipt index `r ≥ 512` cannot read an account at initial version
    `tprev = 0`; A1 allows 4481 receipts.
  - `Assembly/RcptGasContradiction.lean:old_gas_surplus_top_zero`: the surplus overflow gate
    (gated by `ge`, not `gq`) rejects a decodable system receipt with gas price `u128Max`
    against block price 0 (`RcptSystemGasDomain`).
  Isolated repairs exist (`RcptDepositAgeCandidate`: 13-bit age in `xb53..65`;
  `RcptSystemGasCandidate`: gate surplus by `gq`), but they change the frozen AIR — a lead/user
  decision.  Open statement (unprovable as frozen without an honest-unsatisfiable premise):
  `rcpt_aligned_complete (ls : RcptV3Vs) (ok : RcptOk pub ls) (t) :
     TableLocal RcptV3.table (rcptTraceAligned pub ls) t pub ∧
     TableTraffic RcptV3.interactions (rcptTraceAligned pub ls) t pub (rcptTraffic3 pub ls) ∧
     (rcptTraceAligned pub ls).log t % 3 = 1`.
* Full `lake build ZkFormal.V3.Integration` passes with all four new modules; audits
  `AuditPaddedRcpt`, `AuditPaddedSrcp`, `AuditPaddedQv`, `AuditNearV3Admission` pass;
  `make pin-check` passes.

## 2026-10-11 (round 2: lead decisions — rcpt repairs adopted, A10 in srcpV3)

* Merged `origin/integration/v3-20261011b` (fast-forward).
* **A10 in `srcpV3` (table 20) — done.**  `Rcpt/Tables/SrcpD.lean`: `SrcpV3.tableD` = the base
  table + 6 slack-bit columns `db_0..5` (56..61, width 62) + root-row check
  `DP0 − (qe − q − 1) = Σ 2^e db_e` (`q` already counts the list's segments, so
  `qe − q − 1 = |path|` is the per-list counter); `local_base`/`local_of_base`.
  View `Rcpt/Extract/Srcp/Depth.lean:srcpD_view`: `SrcpWf bs ∧ (∀ B ∈ bs, |B.path| ≤ Dp0) ∧
  traffic` (`block_depth`, `BlockChain.depth`; `DP0_eq : SrcpV3.DP0 = NearSpecV3.Dp0`).
  `LinkV3.V3RecordsWf` gains `srcpDepth : ∀ B ∈ r.srcp, B.path.length ≤ NearSpecV3.Dp0`
  (link lane: relate blocks to `usedProofs` to get `GoodV3.pathDepth`).
  Render `Render/PaddedSrcp.lean:srcp_aligned_complete (h : SrcpWf bs) (hd : ∀ B ∈ bs,
  |B.path| ≤ Dp0)` for `tableD`; `srcp_proofs_aligned_complete` adds `hd` for the entries.
  New generic `Render/ColAgree.lean` (local/traffic invariant under agreement on the read
  columns).  **nearV3_size: 6,315,201 → 6,320,769 B** (margin 772,822 B after the hint).
* **rcptV3 (table 16) repaired — AIR + view done.**  `Rcpt/Tables/RcptR.lean:RcptV3.tableR`
  (gas surplus gated by `gq`; 13-bit deposit age `xb53..65`; same columns/interactions/
  maxLog; light module, verbatim copies) with `Assembly/RcptReceiptRepaired.lean:tableR_eq :
  tableR = receiptArithmeticCandidate` (`rfl`).  `nearAirV3` table 16 := `tableR`.
  View `Assembly/RcptViewV3.lean:rcptV3_view_nearAir (hp) (hsize) (hH : HoldsP nearAirV3 …)`:
  the **same** `RcptV3Wf` + exact `rcptTraffic3` as before (the candidate soundness
  migration `ReceiptCandidateProof.ListChain.view_wf/view_traffic`), with the 13-bit-age
  no-wrap premise `tprev ≤ 2^22` discharged from the global MEM balance (`mem_send_sources`:
  only tables 16/17 touch MEM, no public MEM; account opens version 0, receipt writes
  `r+1 ≤ 2^22`).  Signature change: it now takes `HoldsP` instead of the table-local
  premise (LinkV3 updated; the old one is removed from `ExtractV3.lean`).
  `nearV3_size` unchanged by this (6,320,769 B).  Integration builds (2,704 jobs — the
  candidate soundness chain is now in the closure; elaboration-budget note).
* **rcpt render (partial).**  `Render/PaddedRcptR.lean` (namespace `Assembly.RcptSkeleton`):
  `RcptInput` (native data), `RcptOk pub x` (prepD0/walkD0/witness decoding; lists =
  `appliedReceipts`, wf/named/native refund flags; `applyNewChunk` succeeds; gas limit ≤ D0;
  gas-price/final/owner public bytes), `rcptTraceAligned pub x` (the candidate native trace
  `booleanReceiptTrace … 22 …` pinned to index 0, `pinTrace` in `ColAgree.lean`), and
  `rcpt_aligned_complete : ∃ ls, TableLocal RcptV3.tableR … t pub ∧ TableTraffic
  RcptV3.interactions … (rcptTraffic3 pub ls) ∧ log t % 3 = 1`.
  **Open:** `ls` is the trace's own extracted list view, not yet a native function of `x`.
  Needed for render assembly (bus balance against acct/akey/bnd/srcp/sha/…):
  `ls = nativeRcptViews pub x` (the located-view identity `canonical_native_views` exists
  only for the routing-q-patched trace) and the digest streams `x.digests` instantiated with
  the native hashes (currently a free input; local constraints hold for any choice).

## 2026-10-11 (round 3)

* Merged `origin/lane/v3-a11` (f65d9ece); integration 11b already contained.  After the
  build-cache incident the full Integration build recompiled 642 modules: **passes** (2,705).
* **rcpt render now native (no existential).**  `Assembly/RcptUnpatchedViews.lean`: the
  located-view identity chain ported to the unpatched trace (`native_shape_cellsU`,
  `native_entity_headU`, `decoded_head_identityU`, `decoded_native_sequenceU`,
  `canonical_native_viewsU`).  `Render/PaddedRcptR.lean`: trace uses `nativeDigests ctx`
  (native refund-id / PEO hashes, `x.digests` only as fallback for other states);
  `nativeBlocks lists` (native header/receipt grouping, `blocksOfEntities`),
  `nativeRcptLists pub x`, `native_chain` (extracted chain = native blocks),
  `nativeRcptLists_flat : flatR (nativeRcptLists pub x) = locatedViews (rcptTraceNative pub x) x.lists`,
  and `rcpt_aligned_complete : TableLocal RcptV3.tableR ∧ TableTraffic … (rcptTraffic3 pub
  (nativeRcptLists pub x)) ∧ log % 3 = 1`.
* **qv over native inputs.**  `Render/PaddedQvNative.lean`: `qvNativeWalks`
  (`plan … (NativeQueueIds.resolve …)`), `qvNativeRecords`
  (`queueRecords (queueForestProviders 0 0 (queueInputs …))`), `qvNativeTraffic`,
  `QvNativeOk` (valid main values, accepted provider modes, Σ bytes ≤ B0, rows ≤ 2^22,
  public implicit count) and `qv_native_aligned_complete`.
* **Honest receipt-side bus balance** (`Render/HonestBalanceRcpt.lean`, trace-free):
  `qvNative_qvc_balance` (QVC, via `plan_qvc_balance` + `NativeQueueCounters.resolve_eq`),
  `qvNative_qsh_balance` (QSH, `plan_qsh_balance`), `honest_size_balance` (SIZE: node/val/srcp
  sends = size recvs of `honestSizeV`).  Bus users in `nearAirV3` (kernel #eval): QSH, QVC qv
  only; SIZE 2,4,20→21; SREC rcpt only; RCL 16→20; AKC 16↔18; BND 16↔19; RIDS 16→24;
  SRC public→20; MEM 16↔17.
* **Open (balance):** SREC, RCL, AKC, BND, RIDS, MEM all need field identities of the honest
  receipt views (`nativeRcptLists` reads the honest rows; its fields — `kslot`, `tprev`,
  `aft`/`bef`, `rlk`, `q`, `akk`/`aku`, `rid`, `enc`, `gv`/`gs` — must be shown equal to the
  native values the candidate balance lemmas speak about, e.g. `nativeLedgerMemWrites`,
  `NativeAccessKeyProviders`, `boundaryEntry`).  SRC needs the prepared public segment
  (`NativeSourceFour.balance`) bound to `srcpTraffic (blocksOfProofs xs)`.
* **RIDS balance** (`honest_rids_balance`): `(rcptTraffic3 pub (nativeRcptLists pub x)).sends
  B_RIDS = (sortTraffic (NativeSortIds.input applied)).recvs B_RIDS`, via the unpatched
  `located_idsU` (`native_rid_slice`) and `NativeReceiptIdBytes.view_ids`.
* Final: full Integration 2,933 jobs passes; audits pass; pin-check passes.

## 2026-10-11 (round 4)

* Merged `origin/lane/v3-link` (A7: node/val/ups/size → `nodeA7`/`valA7`/`upsA7`/`sizeA7`).
  Conflicts resolved keeping `RcptV3.tableR` (16) and `SrcpV3.tableD` (20) with link's A7
  tables.  **Combined `nearV3_size` = 6,399,329 B** (link 6,393,761 + srcp depth columns);
  margin 694,262 B after the 1,295,017 B hint.  **`v3MaxHintBytes` 1,990,000 → 1,989,000**
  (else `4 + hint + maxInner` exceeds 8 MiB by 725 B; the actual hint body is ≤ 1,295,017).
  Full Integration builds (2,935 jobs).
* **RCL balance** (`Render/HonestBalanceRcl.lean:honest_rcl_balance`): with the honest srcp
  input `xs` holding the same applied lists in order
  (`xs.map (·.entry.receipts) = x.lists.map (List.map Input.receipt)`),
  `(rcptTraffic3 pub (nativeRcptLists pub x)).sends B_RCL = (srcpTraffic (blocksOfProofs xs)).recvs B_RCL`.
  New: `grouped_encodingsU` / `nativeRcptLists_enc` (honest per-list encodings = native
  `Receipt.encode`), `patch_enc`.
* **SIZE after A7:** `honest_size_balance` covers the original tags 0–2 (unchanged senders
  `nodeTraffic3`/`valTraffic`/`srcpTraffic`).  **Open (link lane (a)/(b))** — tags 3–5:
  `sizeA7` receives `SIZE (t+3, y_t)` on its three active rows; `nodeA7` sends
  `SIZE (3, ra)`, `valA7` `SIZE (4, rb)` (both on the `sumr` row) and `upsA7` `SIZE (5, s)`
  (last row).  Needed: record-level A7 traffic `(sizeA7Traffic v y).recvs B_SIZE =
  [[3,y₀],[4,y₁],[5,y₂]]` and the honest senders' A7 totals, then
  `[[3, ra vs], [4, rb es], [5, s u]] = (sizeA7Traffic v ⟨ra vs, rb es, s u⟩).recvs B_SIZE`
  for the honest node/val/ups renders.
* **RIDS coordination:** the balance is stated against exactly
  `sortTraffic (NativeSortIds.input (x.lists.flatten.map Input.receipt))` (receives
  `[r, i, rid_r[i]]` for receipt `r` in applied order, `i < 32`); the sort render must emit
  that traffic.
* **SRC balance** (`Render/HonestBalanceSrc.lean:honest_src_balance`): with
  `xs.map (root, dup) = [(p.lists[j].root, sourceDup p.lists j)]_j`,
  `(srcpTraffic (blocksOfProofs xs)).recvs B_SRC = Public.preparedOn p B_SRC true`
  (the prepared public segment's sends, `prepared_source_records`).  Note:
  `NativeSourceFour.balance` is a SIZE lemma on an older four-partition source layout, not SRC.
* **SREC balance** (`Render/HonestBalanceSrec.lean:honest_srec_balance`):
  `((rcptTraffic3 pub (nativeRcptLists pub x)).sends B_SREC).map toFp ~ (… .recvs B_SREC).map toFp`.
  `rcptTraceNative` is definitionally an instance of
  `booleanReceiptTrace_native_systemBalance`'s trace (system/character/digest layers outermost),
  so the trace-level certificate lifts through the exact traffic.
* **Open — AKC, BND, MEM (precise).**  `RcptInput.accountId`/`accessId` and the deposit
  ledger are currently free/derived inputs of the honest trace; these buses need them pinned
  to the native allocations and the corresponding view fields identified:
  - AKC (16 ↔ 18): `(rcptTraffic3 pub (nativeRcptLists pub x)).sends/recvs B_AKC` =
    `eventMessages pre rs true/false` of `NativeAccessKeyBalance` (fields `ee`, `akf`, `akk`,
    `aku` of the honest views, from `keyAux accountId accessId`), with `akey` traffic
    `akeyTraffic (NativeAccessKeyProviders.providers pre rs)`; then `counter_balance`.
  - BND (16 ↔ 19): honest views' `q`, `rlk` (from `nativeRoutingConstants k`/`routingAux
    (nativeRoutingInterval k)`) equal the requests `requestRanks keys …`; with
    `bndTraffic (boundaryEntries …)`, `boundaryEntry_counter_balance` per entry.
  - MEM (16 ↔ 17): honest views' `kslot` (= `accountId`), `tprev` (= `depositPlanPrevious`),
    `bef`/`aft`/`lk`/`st` (= `depositPlanAccount steps`) give
    `rcptSends3 … B_MEM = nativeLedgerMemWrites original rs steps` and
    `rcptRecvs3 … B_MEM = nativeLedgerMemReads original rs steps`; with
    `acctV3Traffic as` for `nativeAccountViews original replay rs = some as`,
    `native_account_memory_balance`.
  Each identification is a `located_idsU`-style slice lemma over `locatedViews` (cells of the
  key/routing/deposit/account fields on the unpatched trace).
  **Route found for MEM and AKC (next round):**
  `Rcpt/Candidates/NativeReceiptMemAggregate.lean:native_receipt_mem_aggregate` gives
  `locatedMemSends/Recvs = nativeLedgerMemWrites/Reads original rs steps` and
  `Candidates/NativeAccessKeyPhysical.lean:physical_messages` gives the AKC rows
  `= eventMessages pre rs sd` — both on the routing-q-patched trace with
  `accountId := accountSlot original keys ·.receiptIndex`, `accessId :=
  NativeReceiptAccessIds.accessId pre`, `fallback := rankAux pre rs ·`.  Remaining: (i) pin
  these in `RcptOk`; (ii) patch-invariance of the MEM/AKC fields (as `patch_enc`);
  (iii) global-order lemma `rcptSends3 ls B_MEM = locatedMemSends` (as `view_ids` for RIDS);
  then `native_account_memory_balance` / `counter_balance`.  BND has no such native receipt
  lemma yet.

## 2026-10-11 (round 5)

* **MEM balance** (`Render/HonestBalanceMem.lean:honest_mem_balance`):
  `((rcptTraffic3 pub (nativeRcptLists pub x)).sends B_MEM ++ (acctV3Traffic as).sends B_MEM).Perm
   (… .recvs B_MEM ++ (acctV3Traffic as).recvs B_MEM)` under `RcptOk pub x` and
  `MemOk x replay as`: `accountId` pinned to `accountSlot x.t keys ·.receiptIndex`,
  `TrieShape x.t`, `WriteTreePair x.t replay`, `replay` agrees with `x.out.trie` on accounts,
  `nativeAccountViews x.t replay rs = some as`, `|valsOf x.t| < P`.  Pieces: patch invariance
  of the memory fields (`patch_mem_fields`, the q-patch touches only `xb12..18`), global
  order (`rcpt_mem_traffic`, `zipIdx_map_index`), `native_receipt_mem_aggregate`,
  `newchunk_mem_context` (the `applyReceipts` context derived from `RcptOk.run`),
  `native_account_memory_balance`.
* **AKC balance** (`Render/HonestBalanceAkc.lean:honest_akc_balance`), field messages:
  `(akeyTraffic P).sends B_AKC ++ rcpt sends B_AKC ~ rcpt recvs B_AKC ++ (akeyTraffic P).recvs B_AKC`
  with `P = NativeAccessKeyProviders.providers pre rs`, under `RcptOk` and `AkcOk x pre`
  (`accessId = NativeReceiptAccessIds.accessId pre`, `fallback = rankAux pre rs fb`).
  Route: the q-patched honest trace is `TableLocal` (`booleanReceiptTrace_native_repaired_tableLocal`,
  same premises as `RcptOk`), `physical_messages` gives its AKC rows = native events, the
  patch leaves the AKC columns (`gAK`, `kF`, `uak`) untouched (`patch_akc_rows`), and
  `counter_balance` closes the events against the providers.
* **BND balance + ranked honest receipt trace** (`Render/HonestBalanceBnd.lean`).  The
  honest rows must carry the physical boundary use ranks in `uB` (no constraint reads `uB`,
  `arith_counter_free`): `rcptTraceB := counterPatch (rcptTraceNative pub x) 0 ranks`,
  `rcptTrafficB pub x` (= `rcptTraffic3 pub (nativeRcptLists pub x)` on every bus but BND,
  `rcptTrafficB_other`; BND = `physicalCounterMessages`), and
  **`rcpt_aligned_completeB`** (TableLocal `tableR` ∧ TableTraffic `rcptTrafficB` ∧ log%3=1) —
  this is the receipt render render-assembly should use; all the other receipt balances apply
  to it unchanged via `rcptTrafficB_other`.
  `honest_bnd_balance`: `(bndTraffic es).sends B_BND ++ (rcptTrafficB pub x).sends B_BND ~
  (rcptTrafficB pub x).recvs B_BND ++ (bndTraffic es).recvs B_BND` for
  `es = boundaryEntries bounds (physicalBoundaryKeys (rcptTraceNative pub x) 0)`, given
  **coverage** `hc : ∀ r ∈ physicalActiveRows trU 0, physicalBoundaryKey trU 0 r ∈ es.map rec4`.
  Open (precise): `hc` is the public boundary ownership obligation — via
  `physical_provider_render` (`es.map rec4 = Public.boundaryRecords (boundedPrep p k.L k.H.shardId)`)
  it is `∀ r ∈ active, key r ∈ Public.boundaryRecords (boundedPrep …)`, i.e. every native
  routing lookup reads a prepared boundary row; the routing lane keeps it explicit too
  (`normalized_physical_complete`).

## 2026-10-11 (round 6: discharging hypotheses from acceptance)

* Merged `origin/integration/v3-20261011b` (ChaCha `table22`, `MerkleEmpty`, `sortTableV3`,
  `RenderBundleV3`) and `origin/lane/v3-link` (LinkV3 taken from link: balance over A7).
  **Combined `nearV3_size` = 6,415,073 B** (margin 678,518 B after the 1,295,017 B hint);
  **`v3MaxHintBytes` 1,989,000 → 1,973,000** so `4 + hint + maxInner ≤ 8 MiB`.
* `Assembly/RenderV3RcptTables.lean`: `TableRenderV3` instances `rcptRenderV3` (16, via
  `rcpt_aligned_completeB`), `acctRenderV3` (17), `akeyRenderV3` (18), `bndRenderV3` (19),
  `srcpRenderV3` (20), `qvRenderV3` (22).  Table 21 is `sizeA7` (lane v3-trie-complete).
* Discharged from `checkD0a B0 cb wb = .ok ()` (each its own commit):
  - `QvNativeOk` — `Render/AcceptedQv.lean:qvNativeOk_of_accept` (QvNativeOk now carries
    record validity directly);
  - `RcptOk` — `Render/AcceptedRcpt.lean:rcptOk_of_accept` for `acceptedRcptInput`
    (lists = `sourceInputLists ctx p.lists w.entries`; public bytes on `preparedBytes p _`);
  - `MemOk` — `Render/AcceptedMem.lean:memOk_of_accept` (accountId := `nativeAccountId`,
    replay = `newchunk_old_tree_reconstruct`'s old-record tree, `as` = native account views,
    `|as| ≤ 4481`); `acctV3Ok_of_views` (needs `as ≠ []`);
  - `AkcOk` — by construction (choose `accessId := NativeReceiptAccessIds.accessId pre`,
    `fallback := rankAux pre rs fb`; `counter_balance` holds for every `pre`);
  - `AkeyOk` for `providers m.pre applied` — `akeyOk_of_accept`;
  - srcp: `acceptedSrcpInputs` (prepared roots/dup flags + `sourceEntry`), RCL/SRC alignment
    (`accepted_rcl_balance`, `accepted_src_balance`), A10 depth (`acceptedSrcp_depth`), rows
    (`acceptedSrcp_rows`), duplicate occurrences empty (`acceptedSrcp_duplicate`), and
    `acceptedSrcp_ok` (ProofInputsOk with root/sibling widths and RC length < P explicit).
* **Not implied by acceptance (with sketches):**
  - `AcctV3Ok.len_pos` / `AcctWf.nonempty`: an accepted chunk whose applied source lists are all
    empty reads no account, so `nativeAccountViews … = some []`; the frozen `acctV3` forces a
    segment on row 0 (`isFirst·(1−af)`), and a dummy account would emit VBYTES/VPOST/VSLOT traffic
    with no matching value/SHA records.  Fix: the `Rcpt/Candidates/AccountEmpty.table` repair
    (first-row constraint `isFirst·(act−af)`, empty trace proved local) at table 17.
  - BND coverage: the honest receipt routing uses `boundedIntervals k.L own` (boundaries
    truncated to `shardIds.length`), but `prepD0` publishes `p.bnds = ownIntervals L own`.  For a
    malformed-but-decodable layout with `boundaries.length ≥ shardIds.length` the honest lookup
    keys are not `Public.boundaryRecords p` rows.  Fix: publish the bounded representation
    (`boundedPrep`) or render routing over `p.bnds`; for well-formed layouts the two coincide.
* Still open: srcp root/sibling widths and RC-preimage length `< P` (decoding/witness size);
  BND coverage on well-formed layouts (from `native_routing_selected`); `SizeOk` for `sizeA7`
  (trie-complete lane).

## 2026-10-11 (round 7: successor session)

* **Table 17 = empty-capable account table (done).**  `NearAir.lean`: `acctTableV3 :=
  {Rcpt.Candidates.AccountEmpty.table with maxLog := 19}` (row-0 constraint `isFirst·(act−af)`;
  only entry 17 changed; `ExtractV3.nearTablesFull_eq`/`getElem?_acct`/`acctLocal` follow).
  `Rcpt/Candidates/AccountEmptyCap.lean`: cap-generic `first_active_at`, `old_local_at`,
  `empty_or_old_at`, `empty_local_at`, `empty_traffic_exact`; **`Assembly.acctV3_empty_or_old`**
  (silent — every bus count 0 — or `TableLocal {AcctV3.table with maxLog := 19}`);
  `AcctV3WfE cap as := as = [] ∨ AcctV3WfAt cap as` and `acctV3E_view_at`.
  `ViewsV3.acctView` now returns `AcctV3WfE 19`; **`LinkV3.V3RecordsWf.accts : AcctV3WfE 19`**
  (link lane: the account records may now be `[]` with empty traffic).  `rcptV3_view_nearAir`
  unchanged (uses only the traffic of `acctView`).
  Render: `Render/PaddedAcctE.lean` — `AcctV3OkE as := as = [] ∨ AcctV3Ok as`,
  `acctTraceAlignedE` (empty: `AccountEmpty.emptyTrace`, log 1), `acct_aligned_completeE`;
  `acctRenderV3` takes `AcctV3OkE`; `AcceptedMem.acctV3OkE_of_views` (no `as ≠ []`).
  `nearAirV3_wf`/`nearAirV3_npOkPg` re-checked; **`nearV3_sizeMaxAligned` unchanged at
  6,415,073 B** (same widths/degrees), so `v3MaxInner`/`v3MaxHintBytes` unchanged.
  Integration 3,100 jobs OK; audits `AuditAccountEmptyCap` (new), `AuditPaddedRcpt`,
  `AuditNearV3Admission` pass; pin-check OK.
