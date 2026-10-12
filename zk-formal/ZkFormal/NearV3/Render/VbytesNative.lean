import ZkFormal.NearV3.Render.VbytesPartition
import ZkFormal.NearV3.Render.CodecVbytes

/-!
# `VBYTES` on the native objects of an accepted witness

* `priorMsgs_bw`/`blocks_bw`: the codec blocks' `VBYTES` sends are the `keyBwState` shares
  `bwForest` of their pre forest (the block's value id is `priorValueId`).
* **`vbytes_native`**: for an accepted witness `A`, any account replay the trie side exports and any
  `PriorCore` block list on `A`'s trace, the `VBYTES` sends of the account (`A.accts`), access-key
  (`A.akeys`), queue (`qvNativeTraffic`) and codec (`bs`) renders count exactly the value table's
  receives over the native value records `TrieNative.vals A.m A.steps`.
-/
namespace ZkFormal.NearV3.Assembly.VbytesPart
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates ZkFormal.NearV3.Render VbytesKeys
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

theorem posMsgs_emit (tv off : Nat) (L : List Nat) : posMsgs tv off L = (emitAt tv off L).map Msg.toFp := by
  simp [posMsgs, emitAt, Msg.toFp]

theorem forestBytes_len (ts : List PTrie) :
    (forestBytes ts).length = (ts.map fun t => (NearSpecV3.valsOf t).length).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [forestBytes, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, native_valsOf_eq]

/-- A block's codec sends are its tree's `keyBwState` share. -/
theorem priorMsgs_bw (b : NativeBlock) (before : List PTrie)
    (hr : readKey b.witness.pre keyBwState "bandwidth scheduler state" = .ok b.prior)
    (hv : b.vid = priorValueId before b.witness.pre) :
    priorMsgs b = (bwMsgs (forestBytes before).length b.witness.pre).map Msg.toFp := by
  have hf : b.witness.pre.find keyBwState = some b.prior := (readKey_iff _ _ _ _).mp hr
  unfold priorMsgs bwMsgs
  cases hi : valueIndex b.witness.pre keyBwState with
  | none =>
    cases hq : b.prior with
    | none => rfl
    | some v =>
      rw [hq] at hf
      obtain ⟨j, hj, -⟩ := valueIndex_complete _ _ v hf
      rw [hi] at hj; cases hj
  | some i =>
    obtain ⟨v, hv'⟩ := valueIndex_defined _ _ i hi
    obtain ⟨j, hj, hb⟩ := valueIndex_complete _ _ v hv'
    rw [hi] at hj; cases hj
    rw [hf] at hv'
    cases hq : b.prior with
    | none => rw [hq] at hv'; cases hv'
    | some v' =>
      rw [hq] at hv'
      cases hv'
      rw [hv]
      simp only [priorValueId, hi, forestLookupVid, posMsgs_emit, E, Nat.add_comm,
        List.getD_eq_getElem?_getD, hb, Option.getD_some]

/-- **The codec blocks' `VBYTES` sends are the `keyBwState` shares of their pre forest.** -/
theorem blocks_bw : ∀ (bs : List NativeBlock) (before : List PTrie),
    (∀ (i : Nat) (b : NativeBlock), bs[i]? = some b →
      readKey b.witness.pre keyBwState "bandwidth scheduler state" = .ok b.prior ∧
      b.vid = priorValueId (before ++ (bs.map (·.witness.pre)).take i) b.witness.pre) →
    bs.flatMap priorMsgs = (bwForest (forestBytes before).length (bs.map (·.witness.pre))).map Msg.toFp
  | [], _, _ => rfl
  | b :: bs, before, h => by
    obtain ⟨hr, hv⟩ := h 0 b rfl
    simp only [List.map_cons, List.take_zero, List.append_nil] at hv
    have ih := blocks_bw bs (before ++ [b.witness.pre]) (by
      intro i b' hb'
      obtain ⟨hr', hv'⟩ := h (i + 1) b' (by simpa using hb')
      refine ⟨hr', ?_⟩
      simpa [List.take_succ_cons, List.append_assoc] using hv')
    simp only [List.flatMap_cons, List.map_cons, bwForest, List.map_append, priorMsgs_bw b before hr hv, ih]
    congr 3
    simp [forestBytes, List.flatMap_append, native_valsOf_eq]

/-- The value table's `VBYTES` receives over the native records. -/
theorem val_requests (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    valRecvs (TrieNative.vals m steps) B_VBYTES =
      NativeValueByteInventory.requests 0 (NearSpecV3.valsOf m.pre) ++
        NativeValueByteInventory.requests (NearSpecV3.valsOf m.pre).length
          (forestBytes (steps.map ImplicitStepV3.pre)) := by
  unfold TrieNative.vals TrieNative.seedVals
  rw [NativeValueByteInventory.metadata, NativeValueByteInventory.seed]
  have he : forestBytes (TrieNative.forest m steps) =
      NearSpecV3.valsOf m.pre ++ forestBytes (steps.map ImplicitStepV3.pre) := by
    rw [native_valsOf_eq]; rfl
  rw [he, NativeValueByteInventory.append, Nat.zero_add]

/-- The main queue values' buffered shards are the main execution's. -/
theorem shards_eq {cb wb : Bytes} (A : AcceptedV3 cb wb) : A.m.bufferedShards = A.qvVals.shards := by
  obtain ⟨v', hv', hbs⟩ := A.hm.buffered
  have hreads := (Classical.choose_spec A.qvOk_exists).2
  have hvalid := A.qvOk.valid
  have hb : A.m.pre.find keyBufferedIdx = some A.qvVals.buffered := hreads.2.1
  have hsf := single_find A.w.main.values A.k.slotB2.prevStateRoot
    (mainKeys (appliedReceipts A.k A.w) A.m.bufferedShards) keyBufferedIdx A.hm.root_length
    (by rw [← A.hm.pre, hb]; simp)
  rw [hsf, ← A.hm.pre, hb] at hv'
  cases hv'
  have h2 := (bufferedShards_iff _ _).mpr hvalid.2.1
  rw [h2] at hbs
  exact (Except.ok.inj hbs).symm

/-- **`VBYTES` on the native objects of an accepted witness.** -/
theorem vbytes_native {cb wb : Bytes} (A : AcceptedV3 cb wb) {writes : List (List Nat × Bytes)}
    {oldPost : PTrie} (hr : SizedAccountRun A.m.pre writes oldPost) (hkf : KeysFinal A.k A.w A.m writes oldPost)
    {B : Nat} {bs : List NativeBlock} (hc : PriorCore A.p B bs)
    (hF : bs.map (·.witness.pre) = A.m.pre :: A.steps.map ImplicitStepV3.pre) (m : List Fp) :
    cnt (acctV3Sends A.accts B_VBYTES) m + cnt (akeySends A.akeys B_VBYTES) m +
      cnt ((qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)).sends B_VBYTES) m +
      ((bs.flatMap priorMsgs).count m) =
    cnt (valRecvs (TrieNative.vals A.m A.steps) B_VBYTES) m := by
  have hwell : A.m.pre.wf = true := by
    rw [A.hm.pre]
    exact (ZkFormal.NearV3.built_spec A.w.main.values NearSpecV3.trieFuel A.k.slotB2.prevStateRoot _
      A.hm.root_length).2.1
  have hvalid := NativeAccessKeyValidation.newchunk_valid (TrieShape.of_wf _ hwell) A.hm.run
  have hg : Good A.m.pre (mainKeys (appliedReceipts A.k A.w) A.m.bufferedShards) := by
    rw [A.hm.pre]; exact buildFor_good _ _ _ _
  have hsh : ∀ s ∈ A.m.bufferedShards, s ∈ A.qvVals.shards := by
    intro s hs; rw [← shards_eq A]; exact hs
  have hmain := main_partition hg hkf.1 hsh (A.vslot_views hr hkf) hvalid m
  have himp := forest_partition_bw (A.steps.map ImplicitStepV3.pre) (by
      intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      rw [(A.hv.input_facts e he).1]
      exact buildFor_good _ _ _ _) 1 (NearSpecV3.valsOf A.m.pre).length m
  have hq := qv_vbytes A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)
    (queueForestProviders_accepts _ 0 0 A.qvHolds)
    (checkD0a_queue_provider_bytes A.hk A.hw A.h A.hm A.hv A.qvVals)
  have hsplit := NativeQueuePhysicalBytes.forest_split A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) m
  have hcod : bs.flatMap priorMsgs = (bwForest 0 (A.m.pre :: A.steps.map ImplicitStepV3.pre)).map Msg.toFp := by
    have h := blocks_bw bs [] (by
      intro i b hb
      obtain ⟨-, -, hv⟩ := hc.indexed i b hb
      exact ⟨(hc.valid b (List.mem_of_getElem? hb)).1.2.1, by simpa using hv⟩)
    rw [h, hF]; rfl
  have hak : A.akeys = NativeAccessKeyProviders.providers A.m.pre (appliedReceipts A.k A.w) := by
    have he : A.rcptInput.lists.flatten.map RcptSkeleton.Input.receipt = appliedReceipts A.k A.w := A.lists_applied
    unfold AcceptedV3.akeys; rw [he]
  rw [hak, hq, hcod, val_requests]
  simp only [bwForest, Nat.zero_add, List.map_append, List.count_append] at ⊢
  simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, List.map_append, List.count_append]
    at hmain himp hsplit ⊢
  omega

end ZkFormal.NearV3.Assembly.VbytesPart
