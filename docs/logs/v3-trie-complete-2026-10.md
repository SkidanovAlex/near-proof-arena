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
* `Assembly/TrieA7Ups.lean` (ups side): **`ups_rpl_sends`**: `RPL` sends of `upsA7Trace Js T_UPS` =
  `Js.flatMap upsRplMsgs` (per instance `[N_D % P]` (`nDOf`), then `[sN % P]` of every upper part
  — kind RDB/RDE/PT, `upperB` — with a row); **`ups_rplv_sends`** = `Js.flatMap upsRplvMsgs`
  (`[e₃ % P]` of the walk's step 3 when it is a value step, `presV`); **`ups_size_sends`**: exactly
  `[5, upsA7Total Js]`, `upsA7Total = Σ_I (L_I + Σ_k |Q_k|)` (`ups_s_last`, `upsA7Total_le : ≤ R`);
  `ups_recvs`: no receives on the appended interactions.
* `Assembly/TrieA7Bal.lean`: `RenderBundleV3.cnt_ext` (count of an A7 component on an
  appended-only bus = count of the appended interactions' trace traffic), kernel `Covers`/`pub_off`
  for `RPL`/`RPLV`; **`balancedAt_rpl`** / **`balancedAt_rplv`**: a bundle whose node/val/ups
  components are the honest A7 traces balances on `RPL` (`RPLV`) given the record-level
  permutation `(Js.flatMap upsRplMsgs).Perm (((range |ns|).filter S).map ([·]))`
  (resp. `upsRplvMsgs` vs. the value records `SV`).
* Verification: Integration 4122 jobs; `AuditTrieA7Ups` (5 names) passes.

### Open after session 3 (exact)

1. **A7 (a), semantic part.**  For the honest native choice of `trie_all_accepted`
   (`ns = TrieNative.nodes m steps oldPost writes q`, `es = TrieNative.vals m steps`,
   `Js = upsRanked ws insts`): there exist `S SV : Nat → Bool` with
   `(Js.flatMap upsRplMsgs).Perm (((List.range ns.length).filter S).map ([·]))` and
   `(Js.flatMap upsRplvMsgs).Perm (((List.range es.length).filter SV).map ([·]))`.  Needs: the
   ups instances' `N_D`, upper-part `sN` and old-value `e₃` are the node/value record **indices** of
   `ns`/`es` (record `n` has `nid = n`, value `t` has `vid = t`), all `< P`, pairwise distinct (no
   record replaced twice: different instances act on different τ, within an instance the path
   records are distinct).  Not started; the EDGE proof (`TrieUpsNative.accepted_ups_walks`) is the
   closest existing link between `I.N` and node ids.
2. **A7 SIZE tags (rows 0–2 of `sizeA7`)**: the size table's appended receives are computed
   (`Assembly/TrieA7Size.lean`, **`size_a7_recvs`**: exactly `[3, yN 0 % P], [4, yN 1 % P],
   [5, yN 2 % P]`).  Open: the bundle-level `SIZE` balance with `yN 0 = nodeA7Total ns S`, `yN 1 = valA7Total es SV`,
   `yN 2 = upsA7Total Js` (node/val/ups sends: `node_size_sends`, `val_size_sends`,
   `ups_size_sends`, plus the base tag-0/1/2 traffic of node/val/srcp).
3. **A7 (b)**: `nodeA7Total ns S + valA7Total es SV + upsA7Total Js = unfoldBytes cb w ≤ B0` —
   the accounting identity (pre bytes counted twice minus replaced records, plus the new parts and
   value) against `Σ_τ unfoldedBytesT pre_τ + unfoldedBytesT post_τ`.  Not started.  The **ups row
   cap** `R insts + 1 ≤ 2^22` (open since session 2) is to be derived from (b)
   (`R = Σ_I (4 + L_I + Σ|Q_k|)`, `upsA7Total ≤ R`).
4. SHA two-instance packing (task 2), UPB/MEMD/S0F/SPOST/SPLEN, VSLOT native fact,
   KEYNIB/FINAL/VBYTES: unchanged from session 2's list.
* (session 3, end) `TrieA7Size.size_a7_recvs`; Integration 4123 jobs; audits `AuditTrieA7Size`,
  `AuditTrieA7Ups`, `AuditTrieA7Node`, `AuditTrieA7Val`, `AuditRenderV3Trie` pass; `make pin-check` OK.

## 2026-10-11 (session 3, cont.) — lead: items (1)–(5) in order

Lead: HEAVY_MEM=12G allowed (`taskset -c 8-13`).  Order: (1) A7 (a) semantic Perm, (2) A7 (b)
+ ups row cap, (3) bundle SIZE balance, (4) SHA two-bin packing, (5) the remaining shared buses.

* `Assembly/TrieA7Rank.lean`: `rpl_ranked`, `rplv_ranked`, `total_ranked` — the A7 ups messages and
  total of `upsRanked ws insts` are those of `insts` (ranking/sync rewrite only walk counters).

### Plan for (1), from a survey of the existing native-instance lemmas (not yet executed)

* Source: `accepted_window_coverage` (`Rcpt/Candidates/AcceptedWindowCoverage.lean`) gives per
  instance `AllocatedNativeInstance us tau u I` (`I.tau = tau`), `ExactNativeWalkProviders`, and
  `∃ root, forestRootAt 0 0 (us.map pre) tau = some root ∧ NativeReaderOrigin root u.run u.value I`
  — `accepted_ups_walks` currently discards the last component (`-`); keep it.
* `NativeReaderOrigin`: `I = nativeInstance recordId B root.tree run value Qs` with
  `N := sourceLevelIds recordId run` (descend sources top-down, then the terminal source),
  `D := descentCount run.parts`, `(part I k).sN := recordId part.source`.
* Node ids: `native_reader_depth` (`Rcpt/Candidates/NativeReaderDepth.lean`) — for kind ≠ 8,
  `(forestStoreViews ts).nodes[(part I k).sN]? = some s ∧ pdep = s.depth` (internally
  `s = seedNodeView tau …`, so `s.tau = tau`; copy it exporting `s.tau = I.tau`).
  `PartOk` (`Render/Ups/PlanInput.lean`): `kindT/kindU` (kinds 0,1,11 only at `k ≥ nT`), `pdepU`
  (`pdep + (k+1−nT) = dep[D]`), terminal part of kind ≠ 11: `sN = N[D]`, `pdep = dep[D]`;
  `InstOk.q1` (every part has a row, so the nonempty-q filter is vacuous).
  ⇒ every RPL message is a record id with `(tau, depth)` = `(I.tau, dep[D])` for `N_D` and
  `(I.tau, dep[D] − (k+1−nT))` for upper parts — pairwise distinct (no new Nodup lemma needed).
* Forest bridge: ids are in `forestNodes 0 0 0 (oldPost :: steps.pre)` (`us.map pre`), while
  `TrieNative.nodes` is `assignList ∘ records ∘ ChainMetadata.assign ∘ initializeList` over
  `m.pre :: steps.pre` — length-preserving; `hpreEq : us.map pre = rs.map post` and
  `replay_forest_depths` (`NativeRebasedDepths.lean`) give equal record lists up to metadata, so
  index `x` is the same record with the same `tau/depth`.
* Values: `ExactNativeWalkProviders` gives `(step I I.ts).e ∈ edgesOf3 a.nid s`; with mode 0,
  `WalkOkU` gives `ts = 3` and `e[5] = EK_VAL`; new small lemma `e ∈ edgesOf3 n s → e[5] = EK_VAL →
  seedValueId s = some e[3]` (model: `edge_val`, `Extract/Ups/UpsTermT.lean`); `forestNodes_valueIds`
  (`filterMap seedValueId = range' 0 |forestBytes|`) gives Nodup across instances (distinct `N_D`
  records) and the bound `< es.length` (`write_vals_count`, `assignValues` length).
* Bounds for `% P`: `ns.length ≤ R ns < 2^22` (`length_le_R`, `node_P`), `es.length ≤ ValGen.R
  < 2^22` (`val_length_le`, `val_R_lt`).
* Then `S n := decide ([n] ∈ Js.flatMap upsRplMsgs)` and `List.perm_ext_iff_of_nodup`.

## 2026-10-11 (session 4) — A7 (a) semantic Perm DONE

* `Assembly/TrieUpsOrigin.lean`: **`UpsOrigin F insts`** — a forest `ts` (the rebased
  `oldPost :: steps.pre`) with `|forestNodes ts| = |forestNodes F|`, `|forestBytes ts| = |forestBytes F|`,
  and per instance at position `tau`: `I.tau = tau`, `InstOk`, `NativePartFamily`, every part of
  kind ≠ NLF reads node record `sN` of `ts` with `s.tau = tau ∧ pdep = s.depth`
  (`native_reader_depth_tau`), and a `W3` value step reads an edge of a node record of `ts`
  (`ups_edge_inventory_coverage`; head `START` keys excluded by the symbol).
  `upsOrigin_of_coverage` derives it from the `accepted_window_coverage` outputs (keeps the
  `NativeReaderOrigin` component).  Lengths via `replay_forest_depths` / `forestBytes_replay_length`.
  Note: the forest bridge reduced to LENGTHS (the Perm only talks about indices).
* `accepted_ups_walks` and `trie_all_accepted` now export `UpsOrigin (m.pre :: steps.pre) insts`
  (new outer conjunct, after the walk render).
* `Assembly/TrieA7Perm.lean`: `InstOrigin`, `nD_node` (`N_D` is a reader of a terminal part of kind
  ∉ {NLF, PT, RDB, RDE}; `term_has_reader`/`term_not_upper` by `decide`), `upper_node`, `rpl_mem`,
  `rpl_inst` (Nodup by depth), `rplv_mem` (`ts = 3` from the walk, edge `e₀ = N_D`,
  `edge_val_id`: the value id of the `N_D` record), `findIdx_valueId`, `nodup_flatMap_key`
  (distinct `tau` across instances), `perm_of_singletons`; **`rpl_perm`**, **`rplv_perm`**,
  `nodes_length`, `vals_length`, and **`a7_perm_native`**: for `ns = TrieNative.nodes …`,
  `es = TrieNative.vals …`, `Js = upsRanked ws insts`, given `UpsOrigin`, `NodeOk ns`, `ValOk es`:
  `∃ S SV`, the two Perm hypotheses of `balancedAt_rpl` / `balancedAt_rplv`.
  `S n = decide ([n] ∈ insts.flatMap upsRplMsgs)` (so `S` = the replaced records).
* Verification: Integration 4126 jobs; `AuditTrieA7Perm` (4 names), `AuditTrieAll`, `AuditTrieUps` pass;
  `make pin-check` OK.

### A7 (b): NOT provable from `checkD0a` as stated (finding, 2026-10-11 session 4)

`unfoldBytes` measures each post trie as `rebuildPost ws post keys = partialTrie (ws ++ postBlobs)
post.hashOf keys` (A11 lets us replace `ws` by `revealedStore pre`).  `storeGet` returns the FIRST
blob with the looked-up SHA-256, and the pre blobs come first.  If a revealed pre blob `b'` has
`sha256 b' = sha256 (nodeEnc o)` for a post node/value `o` with `b' ≠ nodeEnc o` (a SHA-256
collision), the rebuild decodes `b'` instead and its unfolded count is unrelated to the native post
`out.trie` — while the AIR's A7 sums (`nodeA7Total + valA7Total + upsA7Total`) count the native
post.  Nothing in `RelD0a` excludes this (A11 only fixes the store, A3 is about the witness store),
so neither `… = unfoldBytes` nor `… ≤ B0` nor the ups row cap (`Σ_τ |v_τ|` can reach
32·98,341 = 3,146,912 B; only A7 bounds it, and only through the rebuild) is derivable without
an extra premise.  Needs a user/lead decision, e.g. a decidable amendment
`unfoldedBytesT (rebuildPost (revealedStore pre_τ) post_τ keys) = unfoldedBytesT post_τ` for every
transition (never binding on honest witnesses, violations need a SHA-256 collision — like A3/A11),
or measuring A7's post term on the native post `out.trie` directly.
What remains provable and is still needed under either fix (open, not started): the structural
identity on NATIVE posts, per transition `τ` with scheduler run `u_τ`:
`unfoldedBytesT u.pre + unfoldedBytesT u.run.output = Σ_{records x of τ} (S x ? 1 : 2)|enc x|
 + Σ_{values t of τ} (SV t ? 1 : 2)|v_t| + |u.value| + outputByteCharge u.run`, with
`upsA7Total I = L + Σ_k |Q_k| = |u.value| + outputByteCharge u.run` (from `recsI` length,
`AllocatedNativeInstance`), `S` = path records (the RPL ids), `SV` = overwritten value (LP/BV);
τ = 0: `SizedAccountRun.unfolded_bytes` (oldPost ↔ m.pre).  Ingredients: an exact
`traceUpsert` occurrence identity (the existing `traceUpsert_output_charge*` are inequalities),
`hforest` (record `ser` = rebased `nodeEnc`).

## Task 3 DONE — bundle `SIZE` balance

* `Assembly/TrieA7SizeBal.lean`: `covers_size_send` (tables 2, 4, 7, 20), `covers_size_recv` (21),
  `pub_size`, `RenderBundleV3.tf_eq`, **`RenderBundleV3.balancedAt_size`**: node/val/size components
  with the `Traffic.append` traffic of `nodeRenderV3`/`valRenderV3`/`sizeRenderV3`, ups trace
  `upsA7Trace Js`, srcp `SIZE` sends `= (srcpTraffic bs).sends B_SIZE`, size base view
  `honestSizeV ns es bs`, `yN 0/1/2 = nodeA7Total ns S / valA7Total es SV / upsA7Total Js` ⇒
  `R.BalancedAt B_SIZE` (tags 0–2 `honest_size_balance`, tags 3–5 the A7 sends vs `size_a7_recvs`).
  The size COMPONENT itself (`sizeRenderV3`) still needs `SizeOk` and the `≤ B0` row premise —
  i.e. A7 (b).
* Audit `AuditTrieA7SizeBal` passes.

## Task 4 (SHA two-bin packing): (a), (b), (c)-components DONE; senders' identification open

* `Assembly/TrieShaTwo.lean`:
  (a) `preparedSourceLists_paths` (A10 reaches every prepared occurrence), **`source_rows_A10`**:
  accepted ⇒ `(honestRows (sourceShaMessages p.lists w.entries)).length ≤ 2,257,792`
  (`computedLists ≤ 1984`, `computedPaths ≤ 1984·Dp0`, `sourceSha_A10`).
  (b) `twoBudget_fit` (two residual capacities, jobs ≤ 35 rows, `S+Rc+N+Σ+35 ≤ 2·2^22`),
  `twoShaJobBins` = `[native ++ src₀, scheduler ++ receipt ++ src₁]`, `twoShaJobBins_preserve`,
  **`twoSha_physical_fit`** (bounds 1,663,260 / 2,925,275 / 1,373,299 / 2,257,792; total
  8,219,626 + 35 ≤ 8,388,608).
  (c) **`two_sha_renders`**: bins `[b0, b1]` with `Sha.MsgsOk`, the components
  `shaRenderV3 pub 0/1` (tf = `shaBinTraffic`), and `BYTES` receives / `DIGEST` sends of the two
  bins are permutations of `expectedBytes`/`expectedDigests` of all four families.
* Open for task 4: an accepted-witness theorem producing the scheduler / native / receipt families
  with their bounds for the v3 bundle (the existing ones live in the four-bin chain,
  `NativeFinalAllocation`, `relD0a_work_bounds`, and are not tied to the v3 `BYTES` senders), and
  the `BYTES`/`DIGEST` balance: the senders' (node, val, ups, codec, rcpt, acct, srcp, mrk)
  `BYTES` messages must be exactly `expectedBytes` of those four families (and `DIGEST`
  receivers the digests).  Not started.
* Verification: Integration 4149 jobs (after merging nothing new; the job count rose with the new
  imports); audits `AuditTrieShaTwo` (3), `AuditTrieA7SizeBal`, `AuditTrieA7Perm` pass.

## Task 5: VSLOT native fact DONE

* `Assembly/TrieUpsKeys.lean` (namespace `…Rcpt.Candidates.NodePostUpdate`): `KeysFinal k w m writes
  oldPost` (write keys = applied receipts' account keys ∧ `∃ state, oldPost.upsert keyBwState
  state = some m.result.trie`); copies `upserts_kf`, `physical_kf`, **`coverage_kf`** of the chain
  `native_rebased_upserts_keys` → `native_rebased_physical_bounds` → origin instances →
  `accepted_window_coverage`, carrying `KeysFinal` for the same `writes`/`oldPost` (originals untouched).
* `accepted_ups_walks` now uses `coverage_kf`; it and `trie_all_accepted` export
  `KeysFinal k w m writes oldPost` (outer conjunct right after `SizedAccountRun`).
* `Assembly/TrieVslotNative.lean`: **`TrieShared.vslot_native`** — given `KeysFinal` and the receipt
  side's `nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as` (for that `oldPost`), the
  `hbal` premise of `balancedAt_vslot` for `TrieNative.nodes`.  Remaining for VSLOT: the receipt
  lane's acct component must be `acctV3Traffic as` for those native views.
* Verification: Integration 4153 jobs; audits `AuditTrieVslotNative`, `AuditTrieAll`, `AuditTrieUps`,
  `AuditTrieA7Perm` pass.

### Open after session 4 (exact; successor starts here)

1. **A7 (b) / ups row cap / size component** — blocked on a spec decision (see "A7 (b): NOT
   provable" above).  Provable now and needed under any fix: the per-transition structural identity
   on native posts (plan in that section).  The `TrieA7Bal` module doc still calls the A7 (a) Perm
   "open" — it is closed by `TrieA7Perm.a7_perm_native` (+ `UpsOrigin` from `trie_all_accepted`).
2. **SHA / BYTES / DIGEST**: `TrieShaTwo.two_sha_renders` takes the four families as parameters.
   Open: (i) one accepted-witness theorem giving scheduler/native/receipt families with the bounds
   1,663,260 / 2,925,275 / 1,373,299 for the SAME native choice as `trie_all_accepted`
   (`NativePackedAllocation.accepted` gives `native := jobsToSha (nativeShaJobs ns vals)` ≤ 2,925,275
   but re-chooses `writes/oldPost`; port it onto `coverage_kf`'s choice); (ii) the identification
   of those families with the v3 `BYTES` senders (node, val, ups, codec, rcpt, acct, srcp, mrk) and
   `DIGEST` receivers, then the two bus balances.
3. **UPB**: the balance exists only for the compact ups table
   (`AcceptedRankedWindowBalance.accepted_ranked_window_balance`: windows
   `PhysicalWindowRequests.keys`, counters `patchWindowCounters … physicalWindowRank`).  For `upsA7`
   (UpsV3 interactions `recv/send B_UPB (c rd) (upbMsg u/u+1)`) one needs: `W := ` the UpsV3 read
   keys in `useReq ws insts W`, a UPB counter ranking of the rendered ups rows (as `upsRanked`
   does for EDGE/BMAP walk counters), and the coverage `physicalWindowKey ∈ nodeWindowKeys` (the
   last component of `accepted_window_coverage` / `coverage_kf`, currently discarded by
   `accepted_ups_walks`).
4. **MEMD, S0F/SPOST/SPLEN, KEYNIB/FINAL/VBYTES**: unchanged from session 2 (no completeness-side
   lemma for `UpsV3.table`'s MEMD; S0F/SPOST/SPLEN need the scheduler lane's codec render;
   KEYNIB/FINAL/VBYTES need the receipt/qv/codec sides).
5. **VSLOT**: closed on the trie side (`vslot_native`); needs the receipt lane's acct component
   `= acctV3Traffic as` with `nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as` for
   the `oldPost` of `trie_all_accepted`.

## 2026-10-11 (session 4, cont.) — after the lead's message (main c87a7cae merged)

Lead: A7 (b) target becomes `nodeA7Total + valA7Total + upsA7Total = Σ_τ unfoldedBytesT pre_τ +
unfoldedBytesT (native post_τ) ≤ B0` (A11 retired, spec change on lane/v3-a11) — start only once it
lands on main.  Continue with SHA families + BYTES/DIGEST, UPB, MEMD/S0F/SPOST/SPLEN, KEYNIB/FINAL/VBYTES.

* Merged origin/main (`be28ed45`); Integration 4172 jobs.
* `TrieAll.trie_all_of` (**new**): `trie_all_accepted` for GIVEN `hk hw h hm hv` (so the trie side can
  be instantiated with `AcceptedV3`'s `k, w, m, steps` — the receipt side's choice);
  `trie_all_accepted` is now a corollary.  Both also export `UpsSha insts` (below).
* `TrieUpsOrigin.UpsSha insts`: the scheduler witnesses `us` of the same instances
  (`NativeShaFamily u I`, `I.v = u.value`, `I.tau = τ`, ≤ 32 runs, parts ≤ 403, output bytes
  ≤ 2,131,072, values ≤ 3,146,912).
* `Assembly/TrieShaFamilies.lean`: **`native_sha_of`** (node+val family `jobsToSha (nativeShaJobs ns es)`
  for `TrieNative.nodes/vals` of any `oldPost/writes/q`: ≤ 2,925,275 rows and
  `jobBytes = nodeSends3 ns B_BYTES ++ valSends es B_BYTES`); **`scheduler_sha_of`**
  (`UpsSha` ⇒ `schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us` ≤ 1,663,260 rows, NO A7 needed).
  With `source_rows_A10` (2,257,792) and the receipt family (1,373,299) this feeds `two_sha_renders`.
  Open for BYTES/DIGEST: (i) ups BYTES sends of `upsA7` (`send B_BYTES (vb+qb) [upsId j, qpos, b]`)
  = `expectedBytes (schedulerShaJobs 0 us)` (via `NativeShaFamily`; ids `upsId` vs `upsertJobId`),
  (ii) the sanity jobs are the codec's (sched lane), (iii) the receipt family vs rcpt/acct/srcp/mrk
  senders (rcpt lane), (iv) DIGEST receivers (node, head, ups, codec, rcpt, srcp, mrk) vs
  `expectedDigests` (multiplicity: `dmult` flags).
* `Assembly/TrieUpsSched.lean` — ups side of S0F/SPLEN/SPOST, exact: `aligned_view_bus` (generic),
  **`view_s0f_send`** = `Is.map (reduceMessage [τ, presN I, vidN I])`
  (`presN = [W3 is a value step]`, `vidN = e₃` then, else 0), **`view_splen_recv`** =
  `Is.map (reduceMessage [τ, L I])`, **`view_spost_recv`** =
  `Is.flatMap (range (L I)).map (reduceMessage [τ, p, v_p])`; silent sides `view_s0f_recv`,
  `view_splen_send`, `view_spost_send`.
  **Needed from the sched lane's codec render** (codec interactions `recv S0F (kF) [τ, pres, vid]`,
  `send SPLEN (kF) [τ, 37+24·NN]`, `send SPOST (encG) [τ, pos, bpost]`): for the SAME scheduler
  runs as `UpsSha`'s `us` (τ = position, `u.value = so.state`):
  (a) one S0F receive per τ equal to `[τ, presN I_τ, vidN I_τ]` — `pres` = the old BwState value is
  present (the ups `W3` step is a value step), `vid` = its id in `TrieNative.vals` (=
  `seedValueId` of record `N_D`, see `TrieA7Perm.rplv_mem`), `[τ,0,0]` otherwise;
  (b) one SPLEN send `[τ, |u.value|]` (`|u.value| = 37+24·n²`, `SchedulerUpsertWitness.value_length`);
  (c) SPOST sends `[τ, p, u.value[p]]` for `p < |u.value|`; no other table touches these buses
  (to be checked with `Covers`).  Then the three balances follow from the view lemmas.
* MEMD: ups-internal (`send MEMD (gMs) [τ, j, idx, rx, rb, qlen]`, `recv MEMD (gMr) [τ, jm, idx,
  mBv, mCv, clen]`); needs a per-part traffic computation over `UpsGen` cells using `MemOk`
  (in `NativePartFamily`).  Not started.
* UPB on upsA7: the ups render's counter is `uU` (earlier reads of the same `rkey = (sN, spos)`), so
  only the node side needs `W := ` the read keys and the coverage `physicalWindowKey ∈
  nodeWindowKeys` for `upsTraceAligned` (the existing coverage is for `CompactHeight.trace`).
  Plan: show rank-by-`rkey` = `physicalWindowRank` given coverage (keys with equal `(sN, spos)`
  are equal by `nodeWindowKeys_distinct`), then reuse `window_counter_field_balance`.  Not started.
* KEYNIB/FINAL/VBYTES: walk (5) receives KEYNIB from rcpt (16) and qv (22), sends FINAL; val (4)
  receives VBYTES from qv.  Trie side: `walkTraffic3 (rankWalks [] ws)`, `vals_vbytes`.  Open: the
  walks `ws` of `accepted_ups_walks` come from `allLookupQueries (appliedReceipts k w) m.pre v …`
  with its own `v`; they must be the walks of `A.rcptRenders.qv` / `rcpt` (same `v`).  Not started.
* Verification: Integration 4177 jobs; audits `AuditTrieUpsSched` (6), `AuditTrieAll`, `AuditTrieUps`,
  `AuditTrieVslotNative`, `AuditTrieA7Perm` pass.

## 2026-10-11 (session 4, cont. 2) — lead: UPB, MEMD, walk alignment, BYTES/DIGEST

* **Walk alignment (KEYNIB/FINAL/VBYTES prerequisite)**: `accepted_ups_walks` / `trie_all_of` /
  `trie_all_accepted` now export `∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
  nativeQueryWalks … (allLookupQueries (appliedReceipts k w) m.pre v (steps.pre) resolve) = some ws`.
  `Assembly/TrieWalkAlign.lean`: `mainValues_unique` (Valid ∧ Reads determine `MainValues`; shards by
  `bufferedShards_iff`), **`trie_v_eq_qvVals`**: run on `AcceptedV3 A`'s data, that `v = A.qvVals`
  (the qv table 22's values).  Open: the KEYNIB/FINAL/VBYTES balances themselves — walk (5) KEYNIB
  receives vs rcpt (16) + qv (22) sends, FINAL, and val (4) VBYTES receives vs qv sends
  (`vals_vbytes` is the trie side), now for the same `v`; `resolve` must be the rcpt side's.
* **BYTES, ups part** (`Assembly/TrieUpsSched.lean`, `Assembly/TrieUpsBytes.lean`): `uMsgs_bytes`,
  `bytes_row`, `upsBytes` (value = job 0, part `k` = job `k + 1`), **`view_bytes_send`**
  (aligned ups view BYTES sends `= Is.flatMap upsBytes`; receives `[]`), `ups_bytes_jobs`
  (per instance, as field messages = `expectedBytes (upsertShaJobs τ u.value u.run)` via
  `NativeShaFamily`; ids agree: `upsId = msgId K_VUPS (512τ+j) = upsertJobId τ j`), and
  **`ups_bytes_scheduler`**: for `UpsSha insts` and any `ws`, `((upsRanked ws insts).flatMap upsBytes)
  .map toFp = (expectedBytes (schedulerShaJobs 0 us)).map toFp` with the 1,663,260-row bound.
  Open for BYTES/DIGEST: the sanity jobs `schedulerSanityJobs 0 us` must be the codec's BYTES sends
  (sched lane); the receipt family vs rcpt/acct/srcp/mrk senders (not examined); the bundle-level
  BYTES balance (sha tables 0/1 receive `expectedBytes` of `twoShaJobBins` of the four families,
  `two_sha_renders`; senders node+val `native_sha_of`, ups this, codec, rcpt-side, plus the public
  BYTES receive); DIGEST (sha sends `expectedDigests`, receivers node/head/ups/codec/rcpt/srcp/mrk
  with `dmult` flags) — not started.
* **UPB** — not started (plan unchanged: coverage for `upsTraceAligned`, rank-by-`rkey` =
  `physicalWindowRank`, then `window_counter_field_balance`; the trace-level route needs the bundle
  ups trace `upsA7Trace Js` = `upsTraceAligned Js` + A7 columns and that compactTable and UpsV3 have
  the same two UPB interactions).
* **MEMD** — not started (ups-internal; `aligned_view_bus` applies: row lemma for
  `send MEMD (gMs) [τ, j, idx, rx, rb, qlen]` / `recv MEMD (gMr) [τ, jm, idx, mBv, mCv, clen]` on
  `Q` rows, then a per-instance pairing using `MemOk` / `jm`).
* Verification: Integration 4179 jobs; audits `AuditTrieUpsBytes`, `AuditTrieUpsSched`,
  `AuditTrieWalkAlign`, `AuditTrieAll` pass; `make pin-check` OK.
* Session ended here (context budget); next: UPB, MEMD, then KEYNIB/FINAL/VBYTES and BYTES/DIGEST
  bundle balances; A7 (b) after the spec change lands.

## 2026-10-11 (session 5) — UPB DONE

* **`Assembly/TrieUpb.lean`** (new):
  - trace level, any `upsV3` trace: `aligned_window_row` (UPB row traffic: rd rows send/recv
    `windowFieldKey ++ [u(+1)]`), `Ranked tr t` (read counters = `physicalWindowRank`),
    `aligned_window_count`, `aligned_upb_balance` (via `window_counter_balance`), `upbBal_of_trace`
    (record-level `UpbBal (assignList q 0 vs) v` from `TableTraffic` + `q.windows = keys tr t` +
    coverage + `Ranked`);
  - window keys: `nodeWindowKeys_get`, **`nodeWindowKeys_eq`** (same `(NPOST(n), p)` ⇒ equal key),
    `phys_key_eq`;
  - aligned render: `aligned_cell`, `aligned_height`, `rbit`/`spq` (read bit / position of a part
    row; `rkey_q`), `PartCov Js vs` (part-level coverage: every read row's `readerSourceKey` ∈
    `nodeWindowKeys vs`, `0 ≤ spos`), `aligned_read_row`, `aligned_u`, `aligned_key`, `read_info`,
    `rd_of_rkey`, **`uU_rank`** (`uU Js r = physicalWindowRank (upsTraceAligned Js) t r` on read rows,
    given `PartCov`, `NodeWf3`, bytes, cap), **`aligned_upbBal`** (`UpbBal (assignList q 0 vs)
    (viewOf (upsTraceAligned Js) t (segsOf Js))` for `q.windows = keys (upsTraceAligned Js) t`;
    coverage on `vs₀` with `nodeWindowKeys vs₀ ⊆ nodeWindowKeys vs`), **`partCov_native`**
    (allocated native instances ⇒ `PartCov` for the initialized provider records), `keys_length`
    (`keys` field-bounded, unconditional), **`RenderBundleV3.balancedAt_upb`** (bundle `UPB` from
    `UpbBal` + node/ups `ExtOf`).
* `TrieUpsNative.accepted_ups_walks`, `TrieAll.trie_all_of`, `trie_all_accepted`: new last conjunct
  in the `∀ W` block: `W = PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS → R insts + 1 ≤ 2^22 →
  UpbBal ns (viewOf (upsTraceAligned Js) T_UPS (segsOf Js))`.  So the bundle takes
  `W := keys (upsTraceAligned Js) T_UPS` (with `keys_length`).
* Audit `test/AuditTrieUpb.lean`; Integration 4180 jobs; pin-check OK.

## 2026-10-11 (session 5) — MEMD: generic layer DONE, per-instance pairing OPEN

* **`Assembly/TrieUpsMemd.lean`** (new): `uMsgs_memd` (send `gMs`: `[τ, j, idx, rx, rb, qlen]`, recv
  `gMr`: `[τ, jm, idx, mBv, mCv, clen]`), `memdCols`, `memd_congr` (MEMD messages read only those 12
  columns — not `u`, not the next row), `instRow I rk := generatedRow [I] 0 (0, rk)`,
  `generated_memd`, `memdI I sd` (the instance's own rows' MEMD messages), **`view_memd`**
  (aligned view MEMD traffic `= Is.flatMap (memdI · sd)`), `MemdPair I :=
  (memdI I true).map toFp ~ (memdI I false).map toFp`, `covers_memd` (table 7 only), `pub_memd`,
  **`RenderBundleV3.balancedAt_memd`** (`R.BalancedAt B_MEMD` from `∀ I ∈ Is, MemdPair I`).
  Audit `test/AuditTrieUpsMemd.lean`.
* **Open (exact): `∀ I ∈ upsRanked ws insts, MemdPair I`** for the native instances.  Analysis:
  - sender rows: part `k`, `MEM` rows (`st = 8`, i.e. `p = |q| − 8 + ix`, `FieldsOk.mem_position`),
    gate `k + 1 ≠ nQ ∧ kind ≠ NLF`: `[τ, k+1, ix, limb (RV I Q_k) ix, memRb Q_k ix, |Q_k.q|]`
    (`rbV` at `st = 8` reads `sposV = |pb| − 8 + ix`);
  - receiver rows: `kind ∈ {RDB, RDE, WEX, PT}` (`jm = k`, `PartOk.jmD`) or `SPB` with
    `ci ∈ {5,6,7,9}` (`jm = 1`, `jmS`): `[τ, jm, ix, limb mB ix, memByte (part (jm−1)) ix, clen]`;
  - plan check (by `termPlan`, all 11 cases): sender `k` ↦ receiver `k+1`, except LSc/ESn0
    (`[MV*, NLF, SPB]`) where part 0 ↦ the SPB at 2; NLF parts and the root never send;
    RBI/RLP/RBR/RBV/MV*/NLF and SPB with `ci ∈ {4,8,10}` never receive;
  - value identities needed per pair (receiver `r`, sender `s = jm_r − 1`): `clen_r = |Q_s.q|`
    (`NativePartFamily`, done), `8 ≤ |Q_s.pb|` (then `memByte_eq_memRb`), and **`(Q_r.mB : ℤ) =
    RV I Q_s`** — native: `nativeInstance_newChildMemory` (`mB_{k+1}` = new child's `memD`, upper
    kinds), `nativeInstance_upperRV` (upper `RV` = output `memD`), split/WEX analogues in
    `Tree*Memory*`; missing: terminal-kind `RV` = output `memD` and "new child of part `k+1` =
    output of part `k`" in the `AllocatedNativeInstance` form the accepted instances carry.

## 2026-10-11 (session 5) — KEYNIB / FINAL (trie + qv sides DONE; rcpt identities OPEN), VBYTES analysis

* Participants (kernel `Covers`): `KEYNIB` send rcpt 16, qv 22 / recv walk 5; `FINAL` send walk 5 /
  recv rcpt 16, qv 22; `VBYTES` send codec 11, acct 17, akey 18, qv 22 / recv val 4; no public
  messages on these three.
* **`Assembly/TrieKeyFinal.lean`** (new): `keyOf qs` (key messages of a query list), `walk_keynib`
  (walk receives = `keyOf qs` for the SAME query list), `keyMsgs_snoc`, `repaired_key`,
  **`qv_keynib`** (`(qvNativeTraffic pre v pres).sends B_KEYNIB = keyOf (queueLookupQueries pre v pres
  (NativeQueueIds.resolve pre v pres))`), `keyOf_all`, `qv_keynib_recv`, `rcpt_keynib_recv`,
  `walk_final`, `walk_final_recv`, **`qv_final`** (qv FINAL receives = `queueLookupQueries.map
  (queryMessage pairs)`, from `NativeQueueFinalMessages.plan_messages`; needs `pairs.map fst =
  pre :: pres` and `queueInputs` holds), `qv_final_send`, `rcpt_final_send`,
  `RenderBundleV3.balancedAt_keynib`, `RenderBundleV3.balancedAt_final`, and
  **`keynib_final_accepted`**: for `A : AcceptedV3`, any bundle with walk component
  `walkTraffic3 (rankWalks [] ws)` (the `ws` of `trie_all_of` run on `A`'s `hk hw h hm hv` with
  `resolve := NativeQueueIds.resolve A.m.pre A.qvVals (A.steps.map pre)`, its `v` with
  `Valid ∧ Reads`), `R 16 = A.rcptRenders.rcpt`, `R 22 = A.rcptRenders.qv`, gives
  `BalancedAt B_KEYNIB ∧ BalancedAt B_FINAL` **given the receipt lane's two identities**:
  - `RcptKeys (rcptTrafficB A.pub A.rcptInput) (appliedReceipts A.k A.w)`: rcpt KEYNIB sends ~
    `keyOf (accountLookupQueries rs ++ accessKeyLookupQueries rs)` (as field messages);
  - `RcptFinal (rcptTrafficB A.pub A.rcptInput) pairs (appliedReceipts A.k A.w)`: rcpt FINAL
    receives ~ `(accountLookupQueries rs ++ accessKeyLookupQueries rs).map (queryMessage pairs)`,
    `pairs = (A.m.pre, A.m.result.trie) :: A.steps.map (pre, post)`.
  (Old-candidate analogues exist: `NativeReceiptKeyTraffic.physical_keys`,
  `NativeLookupFinalBalance` for `booleanReceiptTrace`; the current render is `rcptTraceNative`.)
* **VBYTES — not done (exact open statement)**: val receives (`vals_vbytes`) =
  `seedVals.flatMap (if vz then [] else [vid, p, byte_p])`; qv sends =
  `canonicalTraffic (qvNativeRecords …)` `= records.flatMap (numberedBytes vid 0 bytes)`. Needed:
  every non-empty pre-forest value (`TrieNative.seedVals m steps`, ids `vid` after
  `ChainMetadata.assignValues`) is sent exactly once by exactly one of codec (BwState values, sched
  lane), acct/akey (rcpt lane), qv (queue values: `qvNativeRecords` vids must be the `TrieNative.vals`
  ids) — i.e. `valRecvs (TrieNative.vals m steps) B_VBYTES ~ codec ++ acct ++ akey ++ qv` VBYTES
  sends.  This is a reader-partition of the value ids across three lanes; not started.
* Verification: Integration 4184 jobs; audits `AuditTrieKeyFinal`, `AuditTrieUpsMemd`,
  `AuditTrieUpb` pass; pin-check OK.

## 2026-10-11 (session 5) — BYTES reduction; DIGEST not started

* **`Assembly/TrieShaBus.lean`** (new): `jobBytes_expected` (`expectedBytes (jobsToSha J) = jobBytes J`),
  `covers_bytes_send` (2, 4, 7, 11, 16, 17, 20, 23), `covers_bytes_recv` (0, 1), `pub_bytes_send`,
  **`RenderBundleV3.balancedAt_bytes`**: `R.BalancedAt B_BYTES` from the SHA bins `b0 b1`
  (`R 0`, `R 1` = `shaBinTraffic`, `expectedBytes b0 ++ b1 ~ expectedBytes (scheduler ++ native ++
  receipt ++ source)` as from `TrieShaTwo.two_sha_renders`), the trie-side identities (proved
  elsewhere: `native_sha_of` → `hnat`, `ups_bytes_scheduler` → `hups`) and the other lanes'
  count identities:
  - `hcodec` (sched lane): `cnt ((R.tf 11).sends B_BYTES) = cnt (expectedBytes (schedulerSanityJobs 0 us))`
    for the SAME `us` as `ups_bytes_scheduler` (codec = the sanity jobs);
  - `hrest` (rcpt lane): `cnt 16 + cnt 17 + cnt 20 + cnt 23 = cnt (expectedBytes (receipt ++ source))
    + pubCount nearAirV3 pub B_BYTES false` (receipt/source families as passed to `two_sha_renders`).
* Not done: the glue `∃ b0 b1` instantiating `two_sha_renders` with the trie families (needs the
  byte bound `∀ M, ∀ x ∈ M.bytes, x < 256` for the scheduler and native families, and the receipt/
  source families from the rcpt lane); **DIGEST** (sha sends `expectedDigests` of the `dmult` jobs;
  receivers node 2, head 3, ups 7, codec 11, rcpt 16, srcp 20, mrk 23) — not started.

### Open after session 5 (exact; successor starts here)

1. **MEMD per-instance pairing** `∀ I ∈ upsRanked ws insts, TrieUpsMemd.MemdPair I` (plan and
   ingredients in the MEMD section above); then `balancedAt_memd`.
2. **Receipt-lane identities** for KEYNIB/FINAL: `TrieKeyFinal.RcptKeys`, `RcptFinal` for
   `rcptTrafficB A.pub A.rcptInput` (then `keynib_final_accepted`).
3. **VBYTES** reader partition (section above).
4. **BYTES** glue + the codec/receipt identities `hcodec`/`hrest`; **DIGEST** entirely.
5. **A7 (b)** — waiting for the lead (spec change on main).
6. The bundle must take `W := PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS` in
   `trie_all_of` (for `UpbBal`; `TrieUpb.keys_length` gives `W.length < P`) and
   `resolve := NativeQueueIds.resolve A.m.pre A.qvVals (A.steps.map pre)` (for KEYNIB/FINAL).
* Verification: Integration 4185 jobs; audits `AuditTrieUpb`, `AuditTrieUpsMemd`,
  `AuditTrieKeyFinal`, `AuditTrieShaBus` (+ `AuditTrieAll`, `AuditTrieUps*`, `AuditTrieWalkAlign`,
  `AuditTrieVslotNative`) pass; pin-check OK.

## 2026-10-11 (session 5, cont.) — lead: MEMD pairing, BYTES glue, DIGEST

* **BYTES glue DONE** (`TrieShaBus.sha_bins_of`): for `ns = TrieNative.nodes m steps oldPost writes q`,
  `es = TrieNative.vals m steps` (field-bounded `q`, `ValWf es` — from `ValOk.wf` of `trie_all_of`),
  the scheduler family of `us` (rows ≤ 1,663,260) and the receipt/source families with their row
  bounds, `≤ 35` rows per source message and bytes `< 256` (receipt-lane inputs), the two SHA renders
  `b0 b1` exist with `shaBinTraffic`, the bytes and digests permutations against
  `all = (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++ jobsToSha (nativeShaJobs ns es) ++
  receipt ++ source`, and `jobBytes (nativeShaJobs ns es) = nodeSends3 ns BYTES ++ valSends es BYTES`.
  Scheduler/native bytes `< 256`: `schedulerShaJobs_bytes`, `schedulerSanityJobs_bytes`,
  `NativePostShaOk.accepted`.
* **DIGEST reduction DONE** (`TrieShaBus.RenderBundleV3.balancedAt_digest`; `covers_digest_*`:
  sends 0, 1; receives 2, 3, 7, 11, 16, 20, 23; no public): from the SHA bins' digest permutation and
  - `htrie` (**trie side, OPEN — mine**): `cnt (R.tf 2).recvs DIGEST + cnt (R.tf 3).recvs DIGEST +
    cnt (R.tf 7).recvs DIGEST = cnt (expectedDigests (schedulerShaJobs 0 us ++ jobsToSha
    (nativeShaJobs ns es)))` (node: `NPRE/NPOST` of revealed children and `VPRE/VPOST` values; head:
    roots; ups: `upsId` jobs via `dIV`).  Not yet checked against the definitions (in particular
    that every native `NPOST`/`NPRE` job digest — all `dmult = true` in `jobsToSha` — is received
    exactly once, by the parent record or the head, and dup records);
  - `hcodec` (sched lane): codec receives `expectedDigests (schedulerSanityJobs 0 us)`;
  - `hrest` (rcpt lane): rcpt + srcp + mrk receive `expectedDigests (receipt ++ source)`.
