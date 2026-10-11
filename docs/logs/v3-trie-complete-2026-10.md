# Lane `v3-trie-complete` — log (2026-10)

Trie side of `CompleteV3Stmt`: honest native entries, `TableRenderV3` of tables 0–7, trie bus
balances, A7 (a)/(b).  Worktree `/data/illia/nearproof-wt/v3-trie-complete`, branch
`lane/v3-trie-complete` (from main `4b5e8209`).

## 2026-10-11 — start

* `origin/lane/v3-link` (A7 tables) does not merge cleanly into main: it predates the
  2026-10-11 evening merge (conflicts in `NearAir.lean` — rcpt `tableR`, srcp `tableD`, size cap 4,
  ChaCha `table22` vs. the A7 replacements — and in `ExtractV3`, `LinkV3`, `NearAdmission`,
  `NearAirSize`, whose size bound must be recomputed).  That merge is the lead's integration
  step; this lane works on main's `nearAirV3` (base tables at 2, 4, 7) and keeps the A7 work
  separable.
* `Assembly/RenderV3Trie.lean`: `shaRenderV3` (t = 0, 1), `nodeRenderTrie`, `headRenderTrie`,
  `valRenderTrie`, `walkRenderTrie` (fixed height `2^22`, Walk22 `WalkOk`), `uniqRenderTrie`,
  `upsRenderTrie` : `TableRenderV3 pub t _`, each with `tf` definitionally the entry lists'
  traffic (`*_tf`).  Audit `test/AuditRenderV3Trie.lean`.
* `Assembly/UniqNative.lean` — **the `UEnt` producer**: `rawEnts vs hs` = one entry per `DIGS`
  window (node revealed kids `NPRE(c)`, node values `VPRE(i)`, head roots `NPRE(rid)`), sorted by
  `(τ, le256 digest, rk eid)` (`uniqOf rk`, `List.mergeSort`).  `uniqOf_digsBal`: `Link3.DigsBal`
  for any node/head lists (no hypothesis).  `uniqOf_ok`: `UOk` from `RawOk` (32 digest bytes
  `< 256`, `eid < P`, `τ+1 < P`, `≤ 2^17` windows, a head, τ-coverage).
* `Assembly/TrieNative.lean` — the honest entries as functions of the native objects
  (`forest`, `seedNodes`, `seedVals`, `chain`, `nodes … q`, `vals`, `heads … keys`, `uniqs rk …`);
  `accepted_ok` (NodeOk/ValOk/HeadOk from acceptance at `B0`, any `q`/`keys` of length `< P`),
  `accepted_native` (the native objects incl. the `SizedAccountRun` replay exist for every
  accepted witness), `accepted_bundle_parts` (the node/head/val `TableRenderV3` components with
  `tf` = the native traffic), `uniqs_digsBal`.
* `Assembly/TrieBusBalance.lean` — per-bus reduction of `R.Balanced`: `BalancedAt b`,
  `balanced_iff`, `cnt_tf` (a component's count = its table's bus count), `cnt_tf_off`,
  `sum_tables` (restrict the 25-table sum to a table filter `p` with the kernel check
  `Covers b s p`), `pub_off`.  **`balancedAt_digs`**: `DIGS` balance of any bundle whose
  node/head/uniq components carry record lists with `Link3.DigsBal` — with `uniqs_digsBal` this
  closes `DIGS` for the honest bundle.  Bus/table survey (kernel `#eval` of `nearAirV3`):
  trie-only buses PARENT(2) node/head; EDGE(4) node/head/walk/ups; BMAP(11) node/walk/ups;
  DIGS(17) node,head→uniq; DUP(19) uniq→node,val; ENT(20) node/val; VPARENT(22) node→val;
  MEMD(23) ups; MIDROOT(24) head→ups; UPB(25) node/ups; ROOT(10) ups→head + public both sides.
  Shared: BYTES(0) senders node,val,ups,codec,rcpt,acct,srcp,mrk → sha (+ public recv);
  DIGEST(1) sha → node,head,ups,codec,rcpt,srcp,mrk; VSLOT(3) acct→node; KEYNIB(5) rcpt,qv→walk;
  FINAL(6) walk→rcpt,qv; VBYTES(21) codec,acct,akey,qv→val; SIZE(18) node,val,srcp→size;
  S0F(59) ups→codec, SPOST(60)/SPLEN(61) codec→ups.
* `Assembly/TrieVParent.lean` — **`VPARENT` closed**: `forestNodes_vpar` (the node value windows
  of the seeded forest are, in DFS order, exactly `seedValuesFrom 0 (forestBytes ts)`'s
  `(vid, len)`), the metadata passes keep them, `vparentBal_native` (`Link3.VParentBal` of
  `TrieNative.nodes … q` / `vals`, every `q`), `balancedAt_vparent` (bundle level).
* `Assembly/TrieParent.lean` — **`PARENT` closed**: `seedNodesT_parent`/`seedKidsT_parent`
  (mutual: a seeded tree's receives ~ its root message ++ its kid-window sends),
  `forestNodes_parent`, `forestWalkHeads_parent` (heads send exactly the forest's root
  messages when every tree is revealed), metadata passes keep the messages,
  `parentBal_native`, `accepted_forest_isNode` (every pre tree is a node: its scheduler upsert
  `traceUpsert` succeeds; main pre via `SizedAccountRun`), **`parentBal_accepted`**,
  `balancedAt_parent`.
* `Assembly/TrieEnt.lean` — **`ENT` closed**: `chain_ent` (chain metadata sends ~ receives over
  any occurrence list with distinct ids, via `class_sends`/`class_recvs` + `total_ent`),
  `node_sends_shift` / `val_sends` (the honest node/value `ENT` traffic is the chain traffic of
  their occurrences), `entBal_of`, **`entBal_accepted`**, `balancedAt_ent`.
* `Assembly/TrieUniqOcc.lean` — the `DIGS` windows are the store occurrences:
  `seedNodesT_ents`/`seedKidsT_ents` (a record's `(NPRE n, τ, hashOf)` is sent by its parent's
  kid window or its head), `seedNodesT_valEnts` (value windows), `valTau_ents` /
  `valueOccurrences_ents` (the value occurrences' instance is the tree's), **`rawEnts_perm_occ`**:
  `rawEnts (nodes … q) (heads … keys) ~ (allOccurrences …).map occEnt` (revealed wf trees).
* `Assembly/TrieUniqDup.lean` — **`DUP` closed** with the class-ordered uniq list
  `uniqBlocks rs` (blocks = equal-content classes in occurrence order, classes sorted by
  `(τ, le256 sha)`; `uniqNative m steps`).  `uniqEntries_eq` (recursive form), `dupAux_blocks`
  (DUP sends of a block list = the blocks' chain links), `HF` (contents of one instance are
  hash-functional) ⇒ `uniqSends_blocks`; `chain_dup`/`dupRecvs_eq` (receives = chain links);
  `dupBal_of`.  Native: `hf_native` — **no SHA injectivity needed**: every key is in the
  `normalStore` of its tree (`combined_keys`), which is `HashFunctional` because the tree is
  `Stored` in its witness store (`built_spec`, `normalStore_hashFunctional`);
  **`dupBal_accepted`**, **`digsBal_accepted`** (DIGS for the class-ordered list, via
  `rawEnts_perm_occ` + `uniqBlocks_perm`).
* `Assembly/TrieUniqOk.lean` — **`UOk (uniqNative m steps)` from acceptance**
  (`uniqNative_ok`): `occ_count`/`kids_count` (every non-root occurrence costs a 32-byte hash in
  its parent, every value a 36-byte reference: `32·(#occ + #vals) ≤ Σ|nodeEnc| + 32` per tree),
  so with `preBytes ≤ B0` and `≤ 32` trees there are `≤ 62,532` store entries `≤ 2^17`;
  adjacency (`Adj`, `adj_flatMap`) of the class blocks; instance coverage from the revealed
  roots (`forestNodes_cover`).  The uniq table is now fully native: `uniqRenderTrie pub
  (uniqNative m steps) (uniqNative_ok …)` with `DIGS` (`digsBal_accepted`) and `DUP`
  (`dupBal_accepted`).
* `Assembly/TrieComplete.lean` — `walk_accepted` (Walk22 `WalkOk` of the ranked native lookup
  walks for the SAME `m`, `steps`), **`trie_accepted`** (one choice of native objects; for all
  `q`/`keys` of field-bounded length: node/head/val/uniq `TableRenderV3` components with native
  `tf` and `ParentBal`/`VParentBal`/`EntBal`/`DigsBal`/`DupBal`; for every resolver: the walk
  component), `RenderBundleV3.balancedAt_trie_core` (bundle balanced on PARENT, VPARENT, ENT,
  DIGS, DUP).

## Open (state at end of session)

1. **SHA (tables 0, 1) — capacity not established; believed infeasible at the D0a bounds.**
   The proven per-family SHA row bounds are scheduler ≤ 1,663,260, native trie ≤ 2,925,275,
   receipt ≤ 1,373,299, source ≤ 8,932,712 (`relD0a_work_bounds`, `ShaFourPhysical`,
   `SourceUpsertShaLog22`), total 14,894,546 rows, while `nearAirV3` has two `shaTable`s of cap
   `2^22` = 8,388,608 rows in total (the source family alone exceeds it).  The candidates pack
   into **four** log-22 bins (`FourPackedSha`, `fourShaJobBins`).  `TableRenderV3` for a bin is
   done (`shaRenderV3`, needs `Sha.MsgsOk bin`), but no 2-bin split of the honest messages with
   `MsgsOk` exists, and with these bounds none can be proved.  Needs an AIR decision (≥ 4 SHA
   instances, or a tighter source bound); `Assembly/NearAir.lean` not touched here.
2. **`upsV3` (table 7) and every bus it touches** — `EDGE`, `BMAP`, `UPB`, `MIDROOT`, `MEMD`,
   `ROOT` (+ public), `BYTES`, `DIGEST`, `S0F`/`SPOST`/`SPLEN`.  The render
   `upsRenderTrie` needs `UpsRenderOk insts`; `upsRenderOk_of_native` gives it from
   `UpsNativeOk` per instance, but no theorem produces the `UpsNativeData` list (with
   `encodeNativeParts … = some Qs`, `WalkOkU`, the `qhk/phk < 2^22` bounds) from acceptance, and
   the ups traffic is the trace view `upsTraffic (viewOf (upsTraceAligned insts) …)`, so a
   trace-free balance needs `viewOf (upsTraceAligned insts) = rows of insts` first.  The candidate
   balances (`concrete_actual_ups_edge_balance`, `native_midroot_balance`,
   `native_root_balance`, the UPB parts of the allocation theorems) are stated for
   `UpsRelay.compactTable` (no `SPOST` receive) over `physicalPrefixUps … rawInsts` with
   `patchWindowCounters`, not for `UpsV3.table` over `UpsNativeData.inst`.
   Open statement (per bus `b` in that list): `∀ accepted, ∃ insts q keys …, the bundle
   component equations ⇒ R.BalancedAt b` — with the use requests `q` (EDGE/BMAP from
   `walkEdgeKeys (ws ++ upsWalkInventory insts)`, UPB windows from the ups rows) and head keys
   chosen from the walks.
3. **Shared buses, trie contribution** (other tables in parentheses must supply the rest):
   `VSLOT` node receives `[i]` for written value windows (acct 17 sends);
   `KEYNIB` walk receives (rcpt 16, qv 22 send); `FINAL` walk sends (rcpt, qv receive);
   `VBYTES` val receives `[vid, p, byte]` (codec 11, acct, akey 18, qv send — the candidate
   allocation proves it against `EmptyValue.table`/`AccountEmpty.table`, not `ValV3.table`);
   `SIZE` node/val send record totals (srcp 20, size 21);
   `BYTES`/`DIGEST` node/val/head/ups vs. the SHA bins (blocked by 1).
4. **A7 (a), (b)** — not started here.  The A7 tables (`nodeA7`/`valA7`/`upsA7`/`sizeA7`,
   `RenderV3A7`) are on `lane/v3-link` only, which does not merge cleanly with main
   (`NearAir`/`ExtractV3`/`LinkV3`/`NearAdmission`/`NearAirSize` conflicts, size bound to be
   recomputed).  (a) needs the record-level traffic of the appended interactions
   (`RPL`/`RPLV` sends of `upsA7` per replaced record ↔ `rpl`/`rplv` receives chosen by `sel`,
   and `SIZE (3..5, ·)` ↔ `yN`); (b) needs `Σ(2−rpl)·len + Σ(2−rplv)·len + Σ_τ(L_τ+Σ|Q_j|) =
   Σ_τ unfoldedBytesT pre_τ + unfoldedBytesT post_τ ≤ B0` for the honest choice — both depend
   on the ups instances of item 2.
* Verification: `lake build ZkFormal.V3.Integration` passes (3024 jobs) with all new modules; the 10 new audits pass; `make pin-check` OK.

## 2026-10-11 (cont.) — ups component, EDGE/BMAP

Lead: continue with ups (native instances, view, ups buses) and the shared buses; SHA and
BYTES/DIGEST parked; A7 after the link merge.

* `Assembly/TrieUps.lean` — `upsRenderOk_of_family` (`UpsRenderOk` from `InstOk` +
  `NativePartFamily` + the row cap), `upsRenderOk_ranked` (counter ranking changes only the
  walk; `R` unchanged), `aligned_view_walk_messages` (**view lemma**: the aligned ups trace's
  view carries on EDGE/BMAP exactly `upsWalkMessages Is`; the candidate `physical_view_messages`
  needed the unpadded height), `edge_records`/`bmap_records` (record-level conservation, ported
  from `shared_physical_edge_balance` — which is already about `UpsV3.table`, not the compact
  table), `balancedAt_edge`/`balancedAt_bmap`.
* `Assembly/TrieUpsNative.lean` — **`accepted_ups_walks`**: from one choice of native objects
  (`accepted_window_coverage` + `accepted_same_lookup_physical`) the walk component, the native
  ups instances (`InstOk`, `NativePartFamily`), EDGE and BMAP record conservation for
  `TrieNative.nodes … (useReq ws insts W)` / `heads … q.edges` / ranked walks / ranked ups walks,
  and `UpsRenderOk` of the ranked instances **given the row cap**.
* **Ups row cap — open, and not implied by the proven bounds.** `R insts = Σ_τ (4 + |v_τ| +
  outputByteCharge run_τ)`; the proven bounds are `Σ|v| ≤ 3,146,912`, `Σ charge ≤ 2,131,072`
  (total ≤ 5,278,112 > 2^22).  The candidates' compact ups table has no value rows (`compactR`
  fits); `UpsV3.table` does.  Under the 2026-10-11 A7 measure (whole rebuilt post trie) the new
  values and the new path nodes are post-trie bytes, so `R ≤ 128 + Σ_τ unfoldedBytesT post_τ ≤
  128 + B0` — provable with the A7 (b) accounting (same work package).
* `Assembly/TrieUpsRoot.lean` — **MIDROOT and ROOT**.  Compact-table row lemmas ported to
  `upsV3` (same interactions on these buses, same `W`/`V` cells, `Q` rows silent):
  `aligned_view_midroot` (ups receives `[τ, rid] ++ mid` once per instance),
  `aligned_view_root` (ups sends `[τ+1] ++ post` once per instance); `balancedAt_midroot`,
  `balancedAt_root` (with the public endpoint counts and the chain as hypotheses);
  `root_endpoints_accepted` (for the prepared statement of ANY hint: public ROOT messages
  `[0]++prevStateRoot` / `[K+1]++H.prevStateRoot` and the native root chain).
  `accepted_ups_walks` now also gives the head MIDROOT sends `= Js.map ([τ,rid]++mid)`, the
  head ROOT receives `= nativeInputRoots`, the ups ROOT records `= nativeRootRecords`, and the
  32-byte mid/post digests.  ⇒ MIDROOT and ROOT closed from acceptance up to the ups row cap.
* `Assembly/TrieShared.lean` — shared buses, trie side.  **VSLOT**: `vslot_records`
  (acct `[a.k]` sends ~ node written-value receives, from the account-digest permutation),
  `vslot_accepted` (the permutation for `TrieNative.nodes` and `nativeAccountViews m.pre oldPost
  (appliedReceipts k w) = some as`, given the replay's write keys and final upsert),
  `balancedAt_vslot` (node 2 / acct 17 with `acctV3Traffic as`, main's acct render).  Trie
  contributions stated exactly: `vals_vbytes` (VBYTES receives = every pre-forest value's bytes at
  its id), `nodes_size`/`vals_size` (SIZE tags 0/1 totals); KEYNIB/FINAL = `walkTraffic3 (rankWalks
  [] ws)`.  Open for VSLOT: one native choice giving `SizedAccountRun` **and** the write keys and
  the final upsert of the same replay (the candidate chain `native_rebased_origin_instances` drops
  `hkeys`/`hup`; `native_execution_rebased_payloads_keys` has them without the ups instances), and
  the receipt lane's acct entries must be `nativeAccountViews m.pre oldPost …` for that `oldPost`.
* `Assembly/TrieAll.lean` — **`trie_all_accepted`**: one native choice (m, steps, writes,
  oldPost, ups instances, lookup walks) gives the node/head/val/walk/uniq components, the ups
  component given the row cap, and the record balances PARENT, VPARENT, ENT, DIGS, DUP, EDGE,
  BMAP, MIDROOT, ROOT (records; public side `root_endpoints_accepted`).

### Open after this session (trie side)

1. ups row cap `R insts + 1 ≤ 2^22` (A7 (b)-type accounting; the proven bounds do not suffice).
2. UPB (node windows ↔ ups `Q`-row reads, counter chain on `uU`), MEMD (ups-internal memory
   chain of the honest generator), S0F/SPOST/SPLEN (ups ↔ codec, scheduler lane's codec render):
   no completeness-side lemma exists for `UpsV3.table` (the candidates' UPB is for the compact
   table; MEMD only has the soundness-side `memdMsgs`).
3. VSLOT: single native choice carrying the write keys / final upsert (see above).
4. KEYNIB/FINAL/VBYTES full balances need the receipt/qv/codec sides on main
   (rcpt only existential; the candidate key/final/vbytes balances are for candidate receipt and
   value tables).
5. SHA, BYTES/DIGEST (parked by the lead); A7 (a)/(b) (after the link merge).
* Verification (end of session): `lake build ZkFormal.V3.Integration` passes (3199 jobs); all new audits pass; `make pin-check` OK.

## 2026-10-11 (session 3) — merge of the A7 integration, port, A7 (a) node/val traffic

* Merged `origin/integration/v3-20261012` (main + link + rcpt + sched + this lane), then
  `origin/lane/v3-link` `44399c03` (fixes `LinkShaKinds.acct_slot_lt` for the empty-capable
  acct view — the integration branch did not build without it) and `origin/lane/v3-render-sched`
  `23c49506` (drops the pre-A7 table-7 instance from `BundleSched`; ups belongs to this lane).
* **Port to the A7 tables.**  `RenderV3Trie` now imports `RenderV3A7`; the base node/val/ups
  renders are gone (tables 2, 4, 7 are `nodeA7`/`valA7`/`upsA7`), the link lane's
  `nodeRenderV3`/`valRenderV3`/`upsRenderV3` are the components.  New: `ExtOf tf base` (a
  component's traffic agrees with `base` off `RPL`/`RPLV`/`SIZE`), `extOf_append`,
  `nodeRenderV3_ext`, `valRenderV3_ext`, `upsRenderV3_ext`, `RenderBundleV3.tf_ext`/`tf_ext_sel`.
  Every bus-balance theorem (`balancedAt_parent/vparent/ent/digs/dup/edge/bmap/midroot/root/vslot`,
  `balancedAt_trie_core`, `ups_tf_walk`) now takes `ExtOf` hypotheses for node/val/ups (same
  record-level content).  `accepted_bundle_parts`, `trie_accepted`, `trie_all_accepted` export
  `NodeOk ns`/`ValOk es` (so the components are `nodeRenderV3 pub ns hn sel` for ANY `sel`) with
  `∀ sel, ExtOf …`, and the ups part `UpsRenderOk Js` with `ExtOf (upsRenderV3 …).tf …`.
* `Assembly/TrieA7Node.lean` (A7 (a), node side): `selN vs S` (row choice from a record
  predicate `S`), **`node_rpl_recvs`**: `RPL` receives of `nodeA7Trace vs T_NODE (selN vs S)` =
  `((range |vs|).filter S).map ([·])`; **`node_size_sends`**: the only `SIZE` send is
  `[3, nodeA7Total vs S]`, `nodeA7Total = Σ_n (S n ? 1 : 2)·|ser n|`; `node_rpl_sends`,
  `node_size_recvs` empty.  (`node_ra`: `ra` on the SUM row.)
* `Assembly/TrieA7Val.lean` (value side): `selV es S`, **`val_rpl_recvs`** (record `t` has
  `vid = t`, `ent_vid`), **`val_size_sends`** `[4, valA7Total es S]`,
  `valA7Total = Σ_t (S t ? 1 : 2)·len_t`; `val_rpl_sends`, `val_size_recvs` empty.
* Verification: `lake build ZkFormal.V3.Integration` passes (4120 jobs); audits
  `AuditRenderV3Trie` (tf_ext_sel needs no `Classical.choice`), `AuditTrieA7Node`, `AuditTrieA7Val`
  and the 12 older trie audits pass; `make pin-check` OK.
* Host note: `heavy` builds at `taskset -c 8-15,24-31` were OOM-killed inside the 10G scope
  (16 parallel lean workers); `taskset -c 8-13` works.
