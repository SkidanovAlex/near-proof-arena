# Lane v3-render-vbytes (2026-10): `VBYTES` (bus 21) and `MPOS` (bus 9) balances of the honest render

Branch `lane/v3-render-vbytes`, branched from `lane/v3-render-sched` (bdb67614).

## 2026-10-12

### Key-list check (done first, per the brief)

The spec's pre tries are `partialTrie ws root keys` with
* main: `mainKeys rs bshards = [keyDelayedIdx, keyBwState, keyBufferedIdx, keyYieldIdx] ++ bshards.map keyGroupsData ++
  rs.map (accountKeyPath ·.receiverId) ++ (system receipts with signer = receiver).map keyAccessKey`;
* implicit: `[keyDelayedIdx, keyBwState]`.

Readers in `nearAirV3`: codec (11, `keyBwState`, every tree), acct (17, the written account keys = every receiver),
akey (18, the access keys of system self-refunds), qv (22, `mainRequests` = delayed/buffered/yield + `keyGroupsData s`
for `s ∈ v.shards`, and `missingRequest t` = `keyDelayedIdx` on every implicit tree). Every listed key is read
(`v.shards = m.bufferedShards`: `shards_eq`). **No unmatched value receive; no AIR change needed.**

### Proved (all axioms ⊆ {propext, Classical.choice, Quot.sound}; audit `test/AuditCodecVbytes.lean`, `test/AuditMposBal.lean`)

* `Render/MposBal.lean`: `AcceptedV3.receipt_mpos` (from `ReceiptSourcePublicBody.native`'s MPOS equation,
  transported by `patched_counts` / `outcome_traffic_v3`, the `receipt_sha` route), **`RenderBundleV3.balancedAt_mpos`**
  (R16 = accepted receipt render, R23 = `A.mrkAcc`).
* `Render/CodecVbytesRows.lean`: `bus_vbytes`, `vbytes_hdr/rec/hash/ash`, `vbT`, `rt_vbytes`, **`blk_vbytes`**
  (block sends = `posMsgs vid 0 (stateBytes ids a0 hpre)` if present, else `[]`).
* `Render/CodecVbytes.lean`: `takeN_some`, `readLE_some`, `readLink_some`, `readMany_some`, **`decode_encode'`**
  (`State.decode v = some st → st.encode = v`), `links_canon`, **`prior_stateBytes`** (present canonical prior's
  bytes = codec pre bytes), `decode_hash_len`, `hpre_len`, `priorMsgs`, **`codec_vbytes_native`**.
* `Render/VbytesKeys.lean`: `Good`, `good_hash/leaf/ext/kids/branch`, **`buildFor_good`** (every revealed value of
  `buildFor s f h keys` is the `valueIndex` of a listed key), `partialTrie_vals_keys`.
* `Render/VbytesPartition.lean`: `qv_vbytes` (queue sends = provider streams), `implicit_remaining`,
  `remaining_bw`, **`forest_partition_bw`** (implicit trees: queue + codec), **`main_final`** (after
  account/akey/queue only the `keyBwState` occurrence is left), **`main_partition`**.
* `Render/VbytesNative.lean`: `priorMsgs_bw`, `blocks_bw`, `val_requests`, `shards_eq`, **`vbytes_native`**.
* `Render/CodecVbytesBal.lean`: **`RenderBundleV3.balancedAt_vbytes`**, **`RcptTrieSide.rcpt_trie_vbytes`**
  (`rcpt_trie_sched` + `VBYTES` + `MPOS`, same hypotheses and witnesses).

### Shared statements changed (conjunct added only; merge note)

`TrieSide.trie_side_exact`, `RcptTrieSide.rcpt_trie_side`, `rcpt_trie_codec`, `rcpt_trie_sched` now also export
`ExtOf r4.tf (valTraffic (TrieNative.vals A.m A.steps))` (right after the `∃ Js …` block). Callers' patterns
adjusted (`trie_side`, the three chain proofs). Nothing weakened.

### Checks

`lake build ZkFormal.V3.Integration` (4616 jobs) OK; audits `AuditCodecVbytes`, `AuditMposBal`, `AuditRcptTrieSide`,
`AuditUpsS0F`, `AuditCodecTriePin` OK; `make pin-check` OK.  Note: the worktree lacked
`spec/lean/v3/.lake` (copied with `cp -a` from v3-render-sched; no hard links).

### Open (this lane): none for buses 9 and 21.
