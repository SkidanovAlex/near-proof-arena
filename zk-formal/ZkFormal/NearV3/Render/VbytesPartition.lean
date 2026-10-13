import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Render.VbytesKeys
import ZkFormal.NearV3.Candidates.NativePriorOwnership
import ZkFormal.NearV3.Candidates.NativeQueueForestPartition

/-!
# The honest `VBYTES` partition of the pre-forest values

Every value occurrence of the native pre forest (`requests 0 (forestBytes F)`, what the value table
receives) is sent exactly once:

* main pre-trie: by the account table (written account values, one per distinct key), the
  access-key table (one per distinct key), the queue table (main queue reads), and the codec
  (`keyBwState`) — `main_partition`;
* each implicit pre-trie: by the queue table (`keyDelayedIdx`) and the codec (`keyBwState`) —
  `forest_partition_bw`.

The "nothing else" half is `VbytesKeys.buildFor_good` (a built partial trie reveals values only at
listed keys) plus a case analysis over the key lists (`mainKeys` / `[keyDelayedIdx, keyBwState]`).
`bwMsgs base t`: the codec's share of tree `t` (its `keyBwState` value at occurrence `base + i`).
-/
namespace ZkFormal.NearV3.Assembly.VbytesPart
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates ZkFormal.NearV3.Render VbytesKeys
open ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen ZkFormal.NearV3.Qv.Candidates.ValueGen

/-- The value bytes of occurrence `j` of tree `t` at global id `base + j`. -/
def E (t : PTrie) (base j : Nat) : List Msg :=
  emitAt (base + j) 0 (((NearSpecV3.valsOf t).getD j []).map UInt8.toNat)

/-- The codec's share of tree `t`: its `keyBwState` value occurrence. -/
def bwMsgs (base : Nat) (t : PTrie) : List Msg :=
  match valueIndex t keyBwState with
  | some i => E t base i
  | none => []

/-- The codec's share of a forest, with running occurrence offsets. -/
def bwForest : Nat → List PTrie → List Msg
  | _, [] => []
  | base, t :: ts => bwMsgs base t ++ bwForest (base + (NearSpecV3.valsOf t).length) ts

theorem cnt_perm {l l' : List Msg} (h : l.Perm l') (m : List Fp) : cnt l m = cnt l' m :=
  (h.map Msg.toFp).count_eq m

/-! ## Queue table sends -/

/-- **The queue table's `VBYTES` sends**: one stream per queue provider. -/
theorem qv_vbytes (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (ha : ∀ p ∈ queueForestProviders 0 0 (queueInputs pre v pres), p.mode.Accepts (some p.bytes))
    (hb : ((queueForestProviders 0 0 (queueInputs pre v pres)).map (fun p => p.bytes.length)).sum ≤ B0) :
    (qvNativeTraffic pre v pres).sends B_VBYTES =
      (queueForestProviders 0 0 (queueInputs pre v pres)).flatMap
        (fun p => emitAt p.vid 0 (p.bytes.map UInt8.toNat)) := by
  have hz : (qvNativeWalks pre v pres).flatMap (fun w => w.repairedWordMessages B_VBYTES true) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro w _
    simp [Walk.repairedWordMessages, Walk.wordMessages, B_VBYTES, B_KEYNIB, ValueTable.B_QVC]
  simp only [qvNativeTraffic, repairedTraffic, hz, List.nil_append, canonicalTraffic, ite_true,
    qvNativeRecords]
  rw [queueRecords_byte_list _ ha hb]
  simp only [NativeQueuePhysicalBytes.numbered_eq]

/-! ## An implicit pre-trie: queue + codec -/

theorem zipIdx_mem {L : List Bytes} {x : Bytes × Nat} : x ∈ L.zipIdx ↔ L[x.2]? = some x.1 := by
  obtain ⟨b, j⟩ := x
  simp [List.mk_mem_zipIdx_iff_getElem?]

theorem zipIdx_nodup (L : List Bytes) : L.zipIdx.Nodup := by
  have : L.zipIdx.map Prod.snd = List.range' 0 L.length := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  have h : (L.zipIdx.map Prod.snd).Nodup := by rw [this]; exact List.nodup_range' ..
  exact List.Pairwise.of_map Prod.snd (fun a b h e => h (by rw [e])) h

/-- The non-queue values of an implicit pre-trie are exactly its `keyBwState` value. -/
theorem implicit_remaining (t : PTrie) (base : Nat) (hg : Good t [keyDelayedIdx, keyBwState]) (m : List Fp) :
    cnt (NativeQueueForestPartition.remainingBytes t [missingRequest t] base) m = cnt (bwMsgs base t) m := by
  unfold NativeQueueForestPartition.remainingBytes bwMsgs
  have hne : keyDelayedIdx ≠ keyBwState := by decide
  cases hi : valueIndex t keyBwState with
  | none =>
    rw [List.flatMap_eq_nil_iff.mpr]
    intro x hx
    exfalso
    obtain ⟨hx, hk⟩ := List.mem_filter.mp hx
    have hj := (List.getElem?_eq_some_iff.mp (zipIdx_mem.mp hx)).1
    obtain ⟨k, hk', hik⟩ := hg x.2 hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl
    · simp [missingRequest, hik] at hk
    · rw [hi] at hik; cases hik
  | some i =>
    have hil := valueIndex_bound hi
    have hp : ((NearSpecV3.valsOf t).zipIdx.filter (fun x =>
        !([missingRequest t].any (fun r => valueIndex t r.key == some x.2)))).Perm
        [((NearSpecV3.valsOf t)[i], i)] := by
      apply (List.perm_ext_iff_of_nodup ((zipIdx_nodup _).filter _) (by simp)).2
      intro x
      rw [List.mem_filter, zipIdx_mem, List.mem_singleton]
      constructor
      · rintro ⟨hx, hk⟩
        have hj := (List.getElem?_eq_some_iff.mp hx).1
        obtain ⟨k, hk', hik⟩ := hg x.2 hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
        rcases hk' with rfl | rfl
        · simp [missingRequest, hik] at hk
        · have hxi : x.2 = i := by rw [hi] at hik; exact (Option.some.inj hik).symm
          obtain ⟨b, j⟩ := x
          simp only at hxi hx
          subst hxi
          simp only [List.getElem?_eq_getElem hil, Option.some.injEq] at hx
          rw [hx]
      · rintro rfl
        refine ⟨by simp [List.getElem?_eq_getElem hil], ?_⟩
        simp only [missingRequest, List.any_cons, List.any_nil, Bool.or_false, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq]
        intro hd
        exact hne (valueIndex_key_unique t _ _ i hd hi)
    rw [cnt_perm (List.Perm.flatMap_right _ hp)]
    simp [E, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]

theorem remaining_bw (ts : List PTrie) (hg : ∀ t ∈ ts, Good t [keyDelayedIdx, keyBwState]) (m : List Fp) :
    ∀ base, cnt (NativeQueueForestPartition.forestRemaining (ts.map fun t => (t, [missingRequest t])) base) m =
      cnt (bwForest base ts) m := by
  induction ts with
  | nil => intro base; rfl
  | cons t ts ih =>
    intro base
    simp only [List.map_cons, NativeQueueForestPartition.forestRemaining, bwForest, cnt, List.map_append,
      List.count_append] at ih ⊢
    rw [ih (fun t ht => hg t (List.mem_cons_of_mem _ ht))]
    have := implicit_remaining t base (hg t List.mem_cons_self) m
    simp only [cnt] at this
    omega

/-- **Implicit forest**: queue providers and the codec's shares send every value once. -/
theorem forest_partition_bw (ts : List PTrie) (hg : ∀ t ∈ ts, Good t [keyDelayedIdx, keyBwState])
    (tau base : Nat) (m : List Fp) :
    cnt ((queueForestProviders tau base (ts.map fun t => (t, [missingRequest t]))).flatMap
      (fun p => emitAt p.vid 0 (p.bytes.map UInt8.toNat))) m + cnt (bwForest base ts) m =
    cnt (NativeValueByteInventory.requests base (forestBytes ts)) m := by
  have h := NativeQueueForestPartition.forest_partition (ts.map fun t => (t, [missingRequest t])) tau base m
  have hfst : (ts.map fun t => (t, [missingRequest t])).map Prod.fst = ts := by
    simp [List.map_map, Function.comp_def]
  rw [hfst] at h
  rw [← remaining_bw ts hg m base]
  exact h


/-! ## The main pre-trie: account, access key, queue, codec -/

/-- The occurrence `j` of tree `pre` at global id `j`. -/
def Ej (pre : PTrie) (j : Nat) : List Msg :=
  emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat)

/-- The codec's ids of the main pre-trie. -/
def bwIds (pre : PTrie) : List Nat :=
  match valueIndex pre keyBwState with
  | some i => [i]
  | none => []

/-- **After accounts, access keys and queue reads, only the `keyBwState` value is left.** -/
theorem main_final {pre : PTrie} {rs : List Receipt} {writes : List (List Nat × Bytes)} {v : MainValues}
    {shards : List Nat} (hg : Good pre (mainKeys rs shards))
    (hw : writes.map Prod.fst = rs.map (fun r => accountKeyPath r.receiverId))
    (hsh : ∀ s ∈ shards, s ∈ v.shards) :
    (NativePriorOwnership.remainingIds pre rs writes v).Perm (bwIds pre) := by
  have hnd : (NativePriorOwnership.remainingIds pre rs writes v).Nodup :=
    (((List.nodup_range).filter _).filter _).filter _
  have hnd2 : (bwIds pre).Nodup := by unfold bwIds; split <;> simp
  apply (List.perm_ext_iff_of_nodup hnd hnd2).2
  intro j
  constructor
  · intro hj
    simp only [NativePriorOwnership.remainingIds, NativeQueuePartition.residual,
      NativeAccessBytePartition.remaining, List.mem_filter, List.mem_range, Bool.not_eq_true',
      decide_eq_false_iff_not] at hj
    obtain ⟨⟨⟨hjl, hW⟩, hS⟩, hQ⟩ := hj
    obtain ⟨key, hkey, hik⟩ := hg j hjl
    have hq : ∀ r ∈ mainRequests pre v, r.key = key → False := by
      intro r hr hrk
      apply hQ
      have hb : (NearSpecV3.valsOf pre)[j]? = some (NearSpecV3.valsOf pre)[j] := List.getElem?_eq_getElem hjl
      have hsel : ((NearSpecV3.valsOf pre)[j], j) ∈ queueSelected pre (mainRequests pre v) :=
        queueSelected_mem.mpr ⟨hb, r, hr, by rw [hrk]; exact hik⟩
      simp only [NativeQueuePartition.ids, queueProviders, List.map_map, List.mem_map]
      exact ⟨_, hsel, by simp⟩
    simp only [mainKeys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_filter] at hkey
    rcases hkey with ((((rfl | rfl | rfl | rfl) | ⟨s, hs, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, ⟨hr, hp⟩, rfl⟩)
    · exact (hq ⟨keyDelayedIdx, v.delayed, .empty⟩ (by simp [mainRequests]) rfl).elim
    · simp [bwIds, hik]
    · exact (hq ⟨keyBufferedIdx, v.buffered, .buffered v.shards⟩ (by simp [mainRequests]) rfl).elim
    · exact (hq ⟨keyYieldIdx, v.yielded, .empty⟩ (by simp [mainRequests]) rfl).elim
    · exact (hq _ (by simp only [mainRequests, List.mem_append, List.mem_map]; exact Or.inr ⟨s, hsh s hs, rfl⟩)
        rfl).elim
    · exfalso; apply hW
      have hm : accountKeyPath r.receiverId ∈ writes.map Prod.fst := by
        rw [hw]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
      obtain ⟨w, hwm, hwk⟩ := List.mem_map.mp hm
      exact List.mem_filterMap.mpr ⟨w, hwm, by rw [hwk]; exact hik⟩
    · exfalso; apply hS
      exact List.mem_filterMap.mpr ⟨r, List.mem_filter.mpr ⟨hr, hp⟩, hik⟩
  · intro hj
    unfold bwIds at hj
    split at hj
    · rename_i i hi
      simp only [List.mem_singleton] at hj
      subst hj
      exact NativePriorOwnership.main_remaining hi hw v
    · simp at hj

theorem bwIds_msgs (pre : PTrie) : (bwIds pre).flatMap (Ej pre) = bwMsgs 0 pre := by
  unfold bwIds bwMsgs
  split <;> simp [Ej, E]

/-- **Main pre-trie partition**: account, access-key and queue sends plus the codec's share send every
value occurrence once. -/
theorem main_partition {pre post : PTrie} {rs : List Receipt} {writes : List (List Nat × Bytes)} {v : MainValues}
    {shards : List Nat} {as : List AcctV} (hg : Good pre (mainKeys rs shards))
    (hw : writes.map Prod.fst = rs.map (fun r => accountKeyPath r.receiverId))
    (hsh : ∀ s ∈ shards, s ∈ v.shards)
    (hviews : nativeAccountViews pre post rs = some as)
    (hvalid : ∀ r ∈ rs, r.predecessorId = AccountId.system → r.signerId = r.receiverId →
      ∀ bytes, pre.find (keyAccessKey r.receiverId r.signerPk) = some (some bytes) →
        bytes.length = 9 ∧ bytes.getD 8 0 = 1)
    (m : List Fp) :
    cnt (acctV3Sends as B_VBYTES) m + cnt (akeySends (NativeAccessKeyProviders.providers pre rs) B_VBYTES) m +
      cnt ((queueProviders pre (mainRequests pre v) 0 0).flatMap
        (fun p => emitAt p.vid 0 (p.bytes.map UInt8.toNat))) m + cnt (bwMsgs 0 pre) m =
    cnt (NativeValueByteInventory.requests 0 (NearSpecV3.valsOf pre)) m := by
  have hE : Ej pre = fun j => emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat) := rfl
  have hreq : NativeValueByteInventory.requests 0 (NearSpecV3.valsOf pre) =
      (List.range (NearSpecV3.valsOf pre).length).flatMap (Ej pre) := by
    rw [NativeValueByteInventory.indexed, hE]
    simp only [Nat.zero_add]
  have p1 := List.filter_append_perm (fun i => decide (i ∈ writtenValueIds pre writes))
    (List.range (NearSpecV3.valsOf pre).length)
  have p2 := List.filter_append_perm (fun i => decide (i ∈ NativeAccessKeyProviders.selected pre rs))
    (NativeAccessBytePartition.remaining pre writes)
  have p3 := List.filter_append_perm (fun i => decide (i ∈ NativeQueuePartition.ids pre v))
    (NativeQueuePartition.residual pre rs writes)
  have c1 := cnt_perm (p1.flatMap_right (Ej pre)) m
  have c2 := cnt_perm (p2.flatMap_right (Ej pre)) m
  have c3 := cnt_perm (p3.flatMap_right (Ej pre)) m
  have ca := cnt_perm (NativeAccountPreBytes.bytes_perm hw hviews) m
  have ck := cnt_perm ((NativeAccessBytePartition.selected_permutation (pre := pre) hw).flatMap_right (Ej pre)) m
  have cq := cnt_perm ((NativeQueuePartition.selected_permutation (pre := pre) (v := v) hw).flatMap_right (Ej pre)) m
  have cf := cnt_perm ((main_final hg hw hsh).flatMap_right (Ej pre)) m
  rw [NativeAccessKeyProviders.byte_inventory hvalid, NativeQueuePartition.byte_inventory, hreq,
    ← bwIds_msgs]
  have e1 : (List.range (NearSpecV3.valsOf pre).length).filter
      (fun i => !decide (i ∈ writtenValueIds pre writes)) = NativeAccessBytePartition.remaining pre writes := rfl
  have e2 : (NativeAccessBytePartition.remaining pre writes).filter
      (fun i => !decide (i ∈ NativeAccessKeyProviders.selected pre rs)) =
      NativeQueuePartition.residual pre rs writes := rfl
  have e3 : (NativeQueuePartition.residual pre rs writes).filter
      (fun i => !decide (i ∈ NativeQueuePartition.ids pre v)) =
      NativePriorOwnership.remainingIds pre rs writes v := rfl
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3
  rw [hE] at c1 c2 c3 ck cq cf ⊢
  simp only [List.flatMap_append, cnt, List.map_append, List.count_append] at c1 c2 c3 ca ck cq cf ⊢
  omega

end ZkFormal.NearV3.Assembly.VbytesPart
