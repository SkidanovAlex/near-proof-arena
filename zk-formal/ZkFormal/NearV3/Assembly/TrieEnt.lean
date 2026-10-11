import ZkFormal.NearV3.Assembly.TrieParent
import ZkFormal.NearV3.Link.Uniq3Ent
import ZkFormal.NearV3.Candidates.NativeByteFaithfulness

/-!
# ZkFormal.NearV3.Assembly.TrieEnt — `ENT` balance of the honest trie entries

`ENT` copies the message bytes of a store entry along its equal-content class: a record with
`hd` sends `(eid, len, pos, byte)` for its bytes, a record with `dup` receives the same rows
under its predecessor's id `repE`.  The honest metadata (`TrieNative.chain`,
`StoreClassPartition.chain` over all node and value occurrences, keyed by `(τ, bytes)`) is a
chain per class (`StoreDuplicateChain`), whose sends and receives agree (`total_ent`).

* `chain_ent` — for any occurrence list with distinct ids, the per-occurrence sends `Fs` and
  receives `Fr` (driven by the chain metadata) are permutations of each other;
* `nodeSends_ent` / `valSends_ent` (and the receive versions) — the node and value tables' `ENT`
  traffic of the honest records is exactly `Fs` / `Fr` over the node and value occurrences
  (canonical non-empty node bytes, value shape);
* **`entBal_accepted`** — `Link3.EntBal` for `TrieNative.nodes … q` and `TrieNative.vals`;
  `balancedAt_ent` — the bundle level.
-/

namespace ZkFormal.NearV3.Assembly.TrieEnt

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives

abbrev M := ZkFormal.Near.Msg

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- `ENT` rows of a byte string (the empty value has the single marker row). -/
def entPay (X : List Nat) : List M :=
  if X = [] then [[0, 0, 0]] else (List.range X.length).map fun p => [X.length, p, X.getD p 0]

def payK (key : Key) : List M := entPay (key.2.map UInt8.toNat)

/-- Sends of one occurrence under chain metadata `cs`. -/
def Fs (cs : List StoreDuplicateChain.Entry) (o : Occurrence) : List M :=
  if (ChainMetadata.metadata cs o.eid).hd then (payK o.key).map (o.eid :: ·) else []

/-- Receives of one occurrence under chain metadata `cs`. -/
def Fr (cs : List StoreDuplicateChain.Entry) (o : Occurrence) : List M :=
  if (ChainMetadata.metadata cs o.eid).dup then
    (payK o.key).map ((ChainMetadata.metadata cs o.eid).repE :: ·) else []

open StoreClassPartition in
theorem entries_mem_chain (rs : List Occurrence) (key : Key) (hk : key ∈ keys rs)
    (e : StoreDuplicateChain.Entry) (he : e ∈ StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)) :
    e ∈ chain rs :=
  List.mem_flatMap.mpr ⟨key, hk, he⟩

open StoreClassPartition in
theorem class_sends (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) (key : Key)
    (hk : key ∈ keys rs) :
    StoreDuplicateChain.sends (StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)) (payK key) =
      (members rs key).flatMap (Fs (chain rs)) := by
  have hu := chain_unique rs hn
  unfold StoreDuplicateChain.sends
  rw [flatMap_congr_mem (g := fun e => if (ChainMetadata.metadata (chain rs) e.eid).hd then
      (payK key).map (e.eid :: ·) else []) (fun e he => by
        rw [ChainMetadata.metadata_exact _ hu e (entries_mem_chain rs key hk e he)])]
  rw [← List.flatMap_map (f := StoreDuplicateChain.Entry.eid)
    (g := fun eid => if (ChainMetadata.metadata (chain rs) eid).hd then (payK key).map (eid :: ·) else []),
    StoreDuplicateChain.entity_ids, List.flatMap_map]
  apply flatMap_congr_mem
  intro o ho
  have hok : o.key = key := by
    have := (List.mem_filter.mp ho).2
    simpa using this
  simp only [Fs, hok]

open StoreClassPartition in
theorem class_recvs (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) (key : Key)
    (hk : key ∈ keys rs) :
    StoreDuplicateChain.recvs (StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)) (payK key) =
      (members rs key).flatMap (Fr (chain rs)) := by
  have hu := chain_unique rs hn
  unfold StoreDuplicateChain.recvs
  rw [flatMap_congr_mem (g := fun e => if (ChainMetadata.metadata (chain rs) e.eid).dup then
      (payK key).map ((ChainMetadata.metadata (chain rs) e.eid).repE :: ·) else []) (fun e he => by
        rw [ChainMetadata.metadata_exact _ hu e (entries_mem_chain rs key hk e he)])]
  rw [← List.flatMap_map (f := StoreDuplicateChain.Entry.eid)
    (g := fun eid => if (ChainMetadata.metadata (chain rs) eid).dup then
      (payK key).map ((ChainMetadata.metadata (chain rs) eid).repE :: ·) else []),
    StoreDuplicateChain.entity_ids, List.flatMap_map]
  apply flatMap_congr_mem
  intro o ho
  have hok : o.key = key := by
    have := (List.mem_filter.mp ho).2
    simpa using this
  simp only [Fr, hok]

open StoreClassPartition in
/-- **Chain `ENT` conservation** over any occurrence list with distinct ids. -/
theorem chain_ent (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) :
    (rs.flatMap (Fs (chain rs))).Perm (rs.flatMap (Fr (chain rs))) := by
  have hg := grouped_perm rs
  have hs : (grouped rs).flatMap (Fs (chain rs)) = (grouped rs).flatMap (Fr (chain rs)) := by
    unfold grouped
    rw [List.flatMap_assoc, List.flatMap_assoc,
      flatMap_congr_mem (fun key hk => (class_sends rs hn key hk).symm),
      flatMap_congr_mem (l := keys rs) (fun key hk => (class_recvs rs hn key hk).symm)]
    exact total_ent rs payK
  exact ((hg.flatMap_right _).symm.trans (hs ▸ List.Perm.refl _)).trans (hg.flatMap_right _)

/-! ## Node and value tables -/

/-- Node `ENT` sends of one record at position `n`. -/
def nS (s : NodeS3) (n : Nat) : List M :=
  if s.hd then (List.range (s.v.ser false).length).map fun p => [eidN n, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
  else []

def nR (s : NodeS3) : List M :=
  if s.dup then (List.range (s.v.ser false).length).map fun p => [s.repE, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
  else []

theorem nodeSends_ent' (vs : List NodeS3) :
    nodeSends3 vs B_ENT = (vs.zip (List.range vs.length)).flatMap fun x => nS x.1 x.2 := by
  simp [nodeSends3, nS, B_ENT, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS]

theorem nodeRecvs_ent' (vs : List NodeS3) :
    nodeRecvs3 vs B_ENT = (vs.zip (List.range vs.length)).flatMap fun x => nR x.1 := by
  simp [nodeRecvs3, nR, B_ENT, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP]

/-- Node bytes are canonical and non-empty (`ser false` of a revealed node). -/
def NodeBytesOk (s : NodeS3) : Prop :=
  s.v.ser false ≠ [] ∧ NativeByteFaithfulness.Canonical (s.v.ser false)

theorem payK_node (s : NodeS3) (h : NodeBytesOk s) :
    payK (nodeKey s) = (List.range (s.v.ser false).length).map fun p =>
      [(s.v.ser false).length, p, (s.v.ser false).getD p 0] := by
  simp only [payK, nodeKey, NativeByteFaithfulness.decode_encode _ h.2, entPay, if_neg h.1]

/-- The honest node `ENT` sends, index by index. -/
theorem node_sends_shift (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests) :
    ∀ (k : Nat) (ss : List NodeS3), (∀ s ∈ ss, NodeBytesOk s) →
      ((assignList q k (records u (ChainMetadata.assign cs k ss))).zip
          (List.range' k ss.length)).flatMap (fun x => nS x.1 x.2) =
        ((ss.zip (List.range' k ss.length)).map fun x => (⟨nodeKey x.1, eidN x.2⟩ : Occurrence)).flatMap (Fs cs) ∧
      ((assignList q k (records u (ChainMetadata.assign cs k ss))).zip
          (List.range' k ss.length)).flatMap (fun x => nR x.1) =
        ((ss.zip (List.range' k ss.length)).map fun x => (⟨nodeKey x.1, eidN x.2⟩ : Occurrence)).flatMap (Fr cs)
  | _, [], _ => ⟨rfl, rfl⟩
  | k, s :: ss, hok => by
    obtain ⟨ih1, ih2⟩ := node_sends_shift cs u q (k + 1) ss (fun x hx => hok x (by simp [hx]))
    have hs := hok s (by simp)
    have hser : (assignUses q k (record u (ChainMetadata.patch cs k s))).v.ser false = s.v.ser false :=
      node_pre u s.v
    simp only [ChainMetadata.assign, records, List.map_cons, assignList, List.length_cons,
      List.range'_succ, List.zip_cons_cons, List.flatMap_cons, List.map_cons] at *
    refine ⟨?_, ?_⟩
    · rw [ih1]
      congr 1
      simp only [nS, Fs, hser, payK_node s hs, List.map_map]
      rfl
    · rw [ih2]
      congr 1
      simp only [nR, Fr, hser, payK_node s hs, List.map_map]
      rfl

/-- Value records: the shape and canonical bytes the `ENT` rows need. -/
def ValBytesOk (e : ValE) : Prop :=
  (e.vz = true → e.len = 0 ∧ e.bytes = []) ∧ (e.vz = false → e.bytes.length = e.len ∧ 0 < e.len) ∧
    NativeByteFaithfulness.Canonical e.bytes

theorem entRows_pay (e : ValE) (tau : Nat) (h : ValBytesOk e) :
    e.entRows = payK (tau, toBytes e.bytes) := by
  simp only [payK, NativeByteFaithfulness.decode_encode _ h.2.2, entPay, ValE.entRows]
  cases hv : e.vz
  · obtain ⟨hl, hp⟩ := h.2.1 hv
    have hne : e.bytes ≠ [] := by intro h0; rw [h0] at hl; simp at hl; omega
    simp [hne, hl]
  · obtain ⟨hl, hb⟩ := h.1 hv
    simp [hb]

theorem val_sends (cs : List StoreDuplicateChain.Entry) (tau : ValE → Nat) (es : List ValE)
    (hok : ∀ e ∈ es, ValBytesOk e) :
    valSends (ChainMetadata.assignValues cs es) B_ENT =
      (CombinedStoreOccurrences.valueOccurrences tau es).flatMap (Fs cs) ∧
    valRecvs (ChainMetadata.assignValues cs es) B_ENT =
      (CombinedStoreOccurrences.valueOccurrences tau es).flatMap (Fr cs) := by
  simp only [valSends, valRecvs, B_ENT, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, ite_false, ite_true,
    Nat.reduceEqDiff, ChainMetadata.assignValues, CombinedStoreOccurrences.valueOccurrences,
    List.flatMap_map]
  refine ⟨flatMap_congr_mem fun e he => ?_, flatMap_congr_mem fun e he => ?_⟩
  · simp only [Fs, ChainMetadata.patchValue, eidV]
    rw [← entRows_pay e (tau e) (hok e he)]
    rfl
  · simp only [Fr, ChainMetadata.patchValue, eidV]
    rw [← entRows_pay e (tau e) (hok e he)]
    rfl

theorem zip_range_zipIdx {α : Type} (l : List α) :
    (l.zip (List.range' 0 l.length)).map (fun x => (x.1, x.2)) = l.zipIdx := by
  rw [List.zipIdx_eq_zip_range']
  simp

/-- **`ENT` balance of honest node and value records** from the byte facts and distinct ids. -/
theorem entBal_of (ss : List NodeS3) (es : List ValE) (tau : ValE → Nat) (u : Inputs) (q : UseRequests)
    (hn : ∀ s ∈ ss, NodeBytesOk s) (hv : ∀ e ∈ es, ValBytesOk e)
    (hid : ((CombinedStoreOccurrences.allOccurrences ss tau es).map Occurrence.eid).Nodup) :
    let cs := StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences ss tau es)
    Link3.EntBal (assignList q 0 (records u (ChainMetadata.assign cs 0 ss)))
      (ChainMetadata.assignValues cs es) := by
  intro cs
  have hlen : (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))).length = ss.length := by
    simp [assignList_length, records, ChainMetadata.assign_length]
  have hnode := node_sends_shift cs u q 0 ss hn
  have hval := val_sends cs tau es hv
  have hocc : CombinedStoreOccurrences.nodeOccurrences ss =
      (ss.zip (List.range' 0 ss.length)).map fun x => (⟨nodeKey x.1, eidN x.2⟩ : Occurrence) := by
    unfold CombinedStoreOccurrences.nodeOccurrences
    rw [← zip_range_zipIdx, List.map_map]
    rfl
  unfold Link3.EntBal
  rw [nodeSends_ent', nodeRecvs_ent', hlen, List.range_eq_range', hnode.1, hnode.2, hval.1, hval.2,
    ← hocc, ← List.flatMap_append, ← List.flatMap_append]
  exact (chain_ent _ hid).map _

end ZkFormal.NearV3.Assembly.TrieEnt

namespace ZkFormal.NearV3.Assembly.TrieEnt

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives

theorem initializeList_mem : ∀ (n : Nat) (ss : List NodeS3) (s : NodeS3),
    s ∈ initializeList n ss → ∃ o ∈ ss, s.v = o.v
  | _, [], _, h => by simp [initializeList] at h
  | n, o :: ss, s, h => by
    simp only [initializeList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨o, by simp, rfl⟩
    · obtain ⟨o', ho', he⟩ := initializeList_mem (n + 1) ss s h
      exact ⟨o', by simp [ho'], he⟩

theorem seedNodes_bytesOk (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (hw : ∀ t ∈ TrieNative.forest m steps, t.wf = true) :
    ∀ s ∈ TrieNative.seedNodes m steps, NodeBytesOk s := by
  intro s hs
  obtain ⟨o, ho, hv⟩ := initializeList_mem 0 _ s hs
  have hser : s.v.ser false = o.v.ser false := by rw [hv]
  refine ⟨?_, ?_⟩
  · have hm : o.v.ser false ∈ (forestNodes 0 0 0 (TrieNative.forest m steps)).map (fun s => s.v.ser false) :=
      List.mem_map.mpr ⟨o, ho, rfl⟩
    rw [forestNodes_bytes false 0 0 0 _ hw] at hm
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    obtain ⟨tr, -, hto⟩ := List.mem_flatMap.mp ht
    have hpos := revealed_node_positive t (occs_isNode tr t hto)
    rw [hser, ← he]
    exact List.ne_nil_of_length_pos (by simpa using hpos)
  · rw [hser]
    exact NativeByteFaithfulness.node_canonical _ hw o ho

/-- **`ENT` balance of the honest node and value records from acceptance** (any `oldPost`,
`writes`, `q`). -/
theorem entBal_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests) :
    Link3.EntBal (TrieNative.nodes m steps oldPost writes q) (TrieNative.vals m steps) := by
  have hwf : ∀ t ∈ TrieNative.forest m steps, t.wf = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  obtain ⟨-, hval⟩ := NativeExecutionUsage.inputs hk hw h (by decide) hm hv
  have hvb : ∀ e ∈ TrieNative.seedVals m steps, ValBytesOk e := by
    intro e he
    exact ⟨fun h1 => (hval.shape e he).1 h1, fun h1 => (hval.shape e he).2 h1,
      NativeByteFaithfulness.value_canonical _ e he⟩
  exact entBal_of (TrieNative.seedNodes m steps) (TrieNative.seedVals m steps)
    (NativeStoreProvenance.valueTau (TrieNative.forest m steps))
    (forestOldInputs (nativeReplayForest m steps oldPost writes)) q
    (seedNodes_bytesOk m steps hwf) hvb
    (StoreSelectedClasses.combined_ids _ _ _ hval)

end ZkFormal.NearV3.Assembly.TrieEnt

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

theorem covers_ent (s : Bool) : Covers B_ENT s (fun t => t == 2 || t == 4) = true := by
  cases s <;> decide +kernel
theorem pub_ent (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_ENT s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`ENT` balance of a bundle** from the record-level `EntBal` of its node and value components. -/
theorem balancedAt_ent (vs : List NodeS3) (es : List ValE)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs)) (hv : ExtOf (R ⟨T_VAL, by decide⟩).tf (valTraffic es))
    (hbal : Link3.EntBal vs es) : R.BalancedAt B_ENT := by
  intro m
  rw [R.sum_tables true _ m _ (covers_ent true), R.sum_tables false _ m _ (covers_ent false),
    pub_ent, pub_ent]
  have e2 := R.tf_ext 2 (by decide) hn B_ENT (by decide) (by decide) (by decide)
  have e4 := R.tf_ext 4 (by decide) hv B_ENT (by decide) (by decide) (by decide)
  have hf : (List.range 25).filter (fun t => t == 2 || t == 4) = [2, 4] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2.1, e2.2, e4.1, e4.2, sel,
    ite_true, Bool.false_eq_true, ite_false, cnt, nodeTraffic3, valTraffic]
  have := hbal.count_eq m
  simp only [List.map_append, List.count_append] at this
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
