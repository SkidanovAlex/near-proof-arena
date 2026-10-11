import ZkFormal.NearV3.Assembly.TrieUniqOcc

/-!
# ZkFormal.NearV3.Assembly.TrieUniqDup — the class-ordered `uniqV3` entries and `DUP`

`uniqBlocks rs`: the `uniq` entries of the store occurrences `rs`, one block per equal-content
class (`StoreClassPartition.members`, in occurrence order), the classes sorted by
`(τ, le256 SHA-256(content))`.  Inside a block every entry has the same instance and digest, so
`uniqV3` flags it `eq` and sends `DUP (eid, previous eid)`: exactly the chain links of the class
(`StoreDuplicateChain.links`), which the node and value records receive through their chain
metadata (`dup_links`).  Distinct classes have distinct `(τ, digest)` when the contents of one
instance are hash-functional (`HF`), so no `DUP` crosses a block boundary.

* `uniqSends_blocks` — the honest `DUP` sends are the class links;
* `dupRecvs_eq` — the honest node/value `DUP` receives are the class links (chain metadata);
* **`dupBal_of`** — `Link3.DupBal` for the honest records and `uniqBlocks`, given `HF`;
* `uniqBlocks_perm` — `uniqBlocks rs ~ rs.map occEnt` (so `DIGS` carries over).
-/

namespace ZkFormal.NearV3.Assembly.TrieUniqDup

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives StoreClassPartition TrieUniqOcc TrieEnt

/-- Digest bytes (as naturals) of a content. -/
def dig (b : Bytes) : List Nat := (sha256 b).map UInt8.toNat

/-- The class order: instance, then digest. -/
def kle (a b : Key) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ le256 (dig a.2) ≤ le256 (dig b.2)))

theorem kle_trans (a b c : Key) (h1 : kle a b = true) (h2 : kle b c = true) : kle a c = true := by
  simp only [kle, decide_eq_true_eq] at *; omega

theorem kle_total (a b : Key) : (kle a b || kle b a) = true := by
  simp only [kle, Bool.or_eq_true, decide_eq_true_eq]; omega

/-- The sorted classes. -/
def sortedKeys (rs : List Occurrence) : List Key := (keys rs).mergeSort kle

/-- The block of class `K`. -/
def blk (rs : List Occurrence) (K : Key) : List UEnt := (members rs K).map occEnt

/-- **The honest `uniqV3` entries, class by class.** -/
def uniqBlocks (rs : List Occurrence) : List UEnt := (sortedKeys rs).flatMap (blk rs)

theorem uniqBlocks_perm (rs : List Occurrence) : (uniqBlocks rs).Perm (rs.map occEnt) := by
  have h1 : (uniqBlocks rs).Perm ((keys rs).flatMap (blk rs)) :=
    (List.mergeSort_perm _ _).flatMap_right _
  refine h1.trans ?_
  have h2 : (keys rs).flatMap (blk rs) = (grouped rs).map occEnt := by
    simp only [grouped, List.map_flatMap]
    rfl
  rw [h2]
  exact (grouped_perm rs).map _

/-! ## `DUP` sends of a list -/

/-- Instance and digest of an entry. -/
def kap (e : UEnt) : Nat × List Nat := (e.tau, e.bytes)

/-- `DUP` sends along a list, given the previous entry. -/
def dupAux : Option UEnt → List UEnt → List ZkFormal.Near.Msg
  | _, [] => []
  | none, e :: es => dupAux (some e) es
  | some p, e :: es => (if e.tau = p.tau ∧ e.bytes = p.bytes then [[e.eid, p.eid]] else []) ++ dupAux (some e) es

def mkU (e q : UEnt) : UniqE :=
  ⟨e.eid, q.eid, e.tau, (if e.tau = q.tau then 0 else 1), (if e.tau = q.tau ∧ e.bytes = q.bytes then 1 else 0),
    e.bytes⟩

def mkU0 (e : UEnt) : UniqE := ⟨e.eid, 0, e.tau, 0, 0, e.bytes⟩

/-- Recursive form of `uniqEntries`. -/
def ueAux : Option UEnt → List UEnt → List UniqE
  | _, [] => []
  | none, e :: es => mkU0 e :: ueAux (some e) es
  | some p, e :: es => mkU e p :: ueAux (some e) es

theorem ueAux_length : ∀ (o : Option UEnt) (L : List UEnt), (ueAux o L).length = L.length
  | _, [] => rfl
  | none, e :: es => by simp [ueAux, ueAux_length (some e) es]
  | some p, e :: es => by simp [ueAux, ueAux_length (some e) es]

theorem ueAux_getD : ∀ (p : UEnt) (L : List UEnt) (t : Nat), t < L.length →
    (ueAux (some p) L).getD t default = mkU (UniqGen.ent L t) (if t = 0 then p else UniqGen.ent L (t - 1))
  | p, [], t, ht => by simp at ht
  | p, e :: es, 0, _ => by simp [ueAux, UniqGen.ent]
  | p, e :: es, s + 1, ht => by
    simp only [ueAux, List.getD_cons_succ]
    rw [ueAux_getD e es s (by simpa using ht)]
    cases s with
    | zero => simp [UniqGen.ent]
    | succ s => simp [UniqGen.ent, List.getD_cons_succ]

theorem uniqEntries_eq (L : List UEnt) : uniqEntries L = ueAux none L := by
  apply List.ext_getElem
  · simp [uniqEntries, ueAux_length]
  · intro t h1 h2
    have hlt : t < L.length := by simpa [uniqEntries] using h1
    have hg : (ueAux none L)[t] = (ueAux none L).getD t default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    rw [hg]
    simp only [uniqEntries, List.getElem_map, List.getElem_range]
    cases L with
    | nil => simp at hlt
    | cons e es =>
      cases t with
      | zero =>
        simp [ueAux, mkU0, UniqGen.ent, UniqGen.peidOf, UniqGen.stOf, UniqGen.eqOf, UniqGen.same]
      | succ t =>
        simp only [ueAux, List.getD_cons_succ]
        rw [ueAux_getD e es t (by simpa using hlt)]
        have hprev : (if t = 0 then e else UniqGen.ent es (t - 1)) = UniqGen.ent (e :: es) t := by
          cases t <;> simp [UniqGen.ent, List.getD_cons_succ]
        have hcur : UniqGen.ent es t = UniqGen.ent (e :: es) (t + 1) := by
          simp [UniqGen.ent, List.getD_cons_succ]
        rw [hprev, hcur]
        simp only [mkU, UniqGen.peidOf, UniqGen.stOf, UniqGen.eqOf, UniqGen.same, Nat.add_one_ne_zero,
          ite_false, Nat.add_sub_cancel]
        by_cases h0 : (UniqGen.ent (e :: es) (t + 1)).tau = (UniqGen.ent (e :: es) t).tau <;> simp [h0]

theorem uniqSends_ueAux : ∀ (o : Option UEnt) (L : List UEnt), uniqSends (ueAux o L) B_DUP = dupAux o L
  | _, [] => by simp [ueAux, dupAux, uniqSends]
  | none, e :: es => by
    have ih := uniqSends_ueAux (some e) es
    simp only [uniqSends, ite_true] at ih ⊢
    simp [ueAux, dupAux, mkU0, ih]
  | some p, e :: es => by
    have ih := uniqSends_ueAux (some e) es
    simp only [uniqSends, ite_true] at ih ⊢
    simp only [ueAux, dupAux, List.filter_cons]
    by_cases h : e.tau = p.tau ∧ e.bytes = p.bytes <;> simp [h, mkU] <;> exact ih

/-! ## Blocks -/

theorem dupAux_const : ∀ (bs : List UEnt) (b : UEnt) (rest : List UEnt), (∀ e ∈ bs, kap e = kap b) →
    dupAux (some b) (bs ++ rest) =
      StoreDuplicateChain.links ((b :: bs).map UEnt.eid) ++ dupAux (some ((b :: bs).getLast (by simp))) rest
  | [], b, rest, _ => by simp [StoreDuplicateChain.links]
  | c :: cs, b, rest, h => by
    have hc : kap c = kap b := h c (by simp)
    simp only [kap, Prod.mk.injEq] at hc
    have ih := dupAux_const cs c rest (fun e he => by rw [h e (by simp [he]), h c (by simp)])
    simp only [List.cons_append, dupAux, hc, and_self, ite_true, ih, List.map_cons,
      StoreDuplicateChain.links, List.getLast_cons_cons]
    rfl

theorem dupAux_blocks (rs : List Occurrence) (g : Key → Nat × List Nat) :
    ∀ (Ks : List Key) (o : Option UEnt),
      (∀ K ∈ Ks, blk rs K ≠ [] ∧ ∀ e ∈ blk rs K, kap e = g K) → (Ks.map g).Nodup →
      (∀ p, o = some p → kap p ∉ Ks.map g) →
      dupAux o (Ks.flatMap (blk rs)) = Ks.flatMap fun K => StoreDuplicateChain.links ((blk rs K).map UEnt.eid)
  | [], o, _, _, _ => by cases o <;> simp [dupAux]
  | K :: Ks, o, hb, hn, ho => by
    obtain ⟨hne, hk⟩ := hb K (by simp)
    obtain ⟨b, bs, hbs⟩ : ∃ b bs, blk rs K = b :: bs := by
      cases h : blk rs K with
      | nil => exact absurd h hne
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hbK : kap b = g K := hk b (by simp [hbs])
    have hconst : ∀ e ∈ bs, kap e = kap b := fun e he => by rw [hk e (by simp [hbs, he]), hbK]
    rw [List.map_cons] at hn
    have hn' := List.nodup_cons.mp hn
    have ih := dupAux_blocks rs g Ks (some ((b :: bs).getLast (by simp)))
      (fun K' hK' => hb K' (by simp [hK'])) hn'.2
      (by
        intro p hp
        simp only [Option.some.injEq] at hp
        subst hp
        rw [hk _ (by rw [hbs]; exact List.getLast_mem _)]
        exact hn'.1)
    simp only [List.flatMap_cons, hbs, List.cons_append]
    have hfirst : dupAux o (b :: (bs ++ Ks.flatMap (blk rs))) = dupAux (some b) (bs ++ Ks.flatMap (blk rs)) := by
      cases o with
      | none => rfl
      | some p =>
        have hp := ho p rfl
        have hpk : ¬ (b.tau = p.tau ∧ b.bytes = p.bytes) := by
          intro ⟨h1, h2⟩
          apply hp
          rw [show kap p = kap b by simp [kap, h1, h2], hbK]
          simp
        simp [dupAux, hpk]
    rw [hfirst, dupAux_const bs b _ hconst, ih]

/-- Contents of one instance are hash-functional over the occurrence keys. -/
def HF (rs : List Occurrence) : Prop :=
  ∀ o ∈ rs, ∀ o' ∈ rs, o.key.1 = o'.key.1 → sha256 o.key.2 = sha256 o'.key.2 → o.key.2 = o'.key.2

theorem dig_inj {a b : Bytes} (h : dig a = dig b) : sha256 a = sha256 b := by
  unfold dig at h
  have := congrArg (List.map UInt8.ofNat) h
  simpa [List.map_map, Function.comp_def] using this

/-- **The honest `DUP` sends are the class links.** -/
theorem uniqSends_blocks (rs : List Occurrence) (hf : HF rs) :
    (uniqSends (uniqEntries (uniqBlocks rs)) B_DUP).Perm
      ((keys rs).flatMap fun K => StoreDuplicateChain.links ((members rs K).map Occurrence.eid)) := by
  rw [uniqEntries_eq, uniqSends_ueAux]
  have hmem : ∀ K ∈ keys rs, ∀ o ∈ members rs K, o.key = K := by
    intro K _ o ho
    have := (List.mem_filter.mp ho).2
    simpa using this
  have hsk : ∀ K ∈ sortedKeys rs, K ∈ keys rs := fun K hK => List.mem_mergeSort.mp hK
  have h := dupAux_blocks rs (fun K => (K.1, dig K.2)) (sortedKeys rs) none
    (by
      intro K hK
      refine ⟨?_, ?_⟩
      · simp only [blk, ne_eq, List.map_eq_nil_iff]
        exact group_nonempty rs K (hsk K hK)
      · intro e he
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
        rw [← hmem K (hsk K hK) o ho]
        rfl)
    (by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      have hnd : (sortedKeys rs).Nodup := ((List.mergeSort_perm _ _).nodup_iff).mpr (distinct _)
      refine (List.nodup_iff_pairwise_ne.mp hnd).imp_of_mem ?_
      intro K K' hK hK' hne heq
      apply hne
      simp only [Prod.mk.injEq] at heq
      obtain ⟨o, ho, hok⟩ := List.mem_map.mp ((covers _ _).mp (hsk K hK))
      obtain ⟨o', ho', hok'⟩ := List.mem_map.mp ((covers _ _).mp (hsk K' hK'))
      have h2 := hf o ho o' ho' (by rw [hok, hok']; exact heq.1) (by rw [hok, hok']; exact dig_inj heq.2)
      rw [← hok, ← hok', Prod.ext_iff]
      exact ⟨by rw [hok, hok']; exact heq.1, h2⟩)
    (by intro p hp; cases hp)
  rw [uniqBlocks, h]
  have hblk : ∀ K, (blk rs K).map UEnt.eid = (members rs K).map Occurrence.eid := by
    intro K; simp [blk, List.map_map, Function.comp_def, occEnt]
  simp only [hblk]
  exact (List.mergeSort_perm _ _).flatMap_right _

/-! ## `DUP` receives -/

/-- Receive of one occurrence under the chain metadata. -/
def Dr (cs : List StoreDuplicateChain.Entry) (o : Occurrence) : List ZkFormal.Near.Msg :=
  if (ChainMetadata.metadata cs o.eid).dup then [[o.eid, (ChainMetadata.metadata cs o.eid).repE]] else []

theorem class_dup (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) (K : Key) (hk : K ∈ keys rs) :
    (members rs K).flatMap (Dr (chain rs)) = StoreDuplicateChain.links ((members rs K).map Occurrence.eid) := by
  have hu := chain_unique rs hn
  rw [← StoreDuplicateChain.dup_links]
  have h1 : ((StoreDuplicateChain.entries ((members rs K).map Occurrence.eid)).filter (fun e => e.dup)).map
      (fun e => [e.eid, e.repE]) =
      (StoreDuplicateChain.entries ((members rs K).map Occurrence.eid)).flatMap
        (fun e => if e.dup then [[e.eid, e.repE]] else []) := by
    generalize StoreDuplicateChain.entries ((members rs K).map Occurrence.eid) = l
    induction l with
    | nil => rfl
    | cons a l ih => by_cases h : a.dup <;> simp [List.filter_cons, h, ih]
  rw [h1]
  symm
  rw [flatMap_congr_mem (g := fun e => if (ChainMetadata.metadata (chain rs) e.eid).dup then
      [[e.eid, (ChainMetadata.metadata (chain rs) e.eid).repE]] else []) (fun e he => by
        rw [ChainMetadata.metadata_exact _ hu e (entries_mem_chain rs K hk e he)])]
  rw [← List.flatMap_map (f := StoreDuplicateChain.Entry.eid)
    (g := fun eid => if (ChainMetadata.metadata (chain rs) eid).dup then
      [[eid, (ChainMetadata.metadata (chain rs) eid).repE]] else []),
    StoreDuplicateChain.entity_ids, List.flatMap_map]
  rfl

theorem chain_dup (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) :
    (rs.flatMap (Dr (chain rs))).Perm
      ((keys rs).flatMap fun K => StoreDuplicateChain.links ((members rs K).map Occurrence.eid)) := by
  refine ((grouped_perm rs).flatMap_right _).symm.trans ?_
  unfold grouped
  rw [List.flatMap_assoc, flatMap_congr_mem (fun K hK => class_dup rs hn K hK)]

/-- Node `DUP` receives of records. -/
theorem node_dup_shift (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests) :
    ∀ (k : Nat) (ss : List NodeS3),
      ((assignList q k (records u (ChainMetadata.assign cs k ss))).zip (List.range' k ss.length)).filterMap
          (fun x => if x.1.dup then some [eidN x.2, x.1.repE] else none) =
        ((ss.zip (List.range' k ss.length)).map fun x => (⟨nodeKey x.1, eidN x.2⟩ : Occurrence)).flatMap (Dr cs)
  | _, [] => rfl
  | k, s :: ss => by
    have ih := node_dup_shift cs u q (k + 1) ss
    simp only [ChainMetadata.assign, records, List.map_cons, assignList, List.length_cons,
      List.range'_succ, List.zip_cons_cons, List.filterMap_cons, List.flatMap_cons] at *
    rw [← ih]
    simp only [Dr, ChainMetadata.patch, assignUses, record]
    by_cases h : (ChainMetadata.metadata cs (eidN k)).dup <;> simp [h]

theorem nodeRecvs_dup (vs : List NodeS3) :
    nodeRecvs3 vs B_DUP = (vs.zip (List.range vs.length)).filterMap
      (fun x => if x.1.dup then some [eidN x.2, x.1.repE] else none) := by
  simp [nodeRecvs3, B_DUP, B_DIGEST, B_PARENT, B_EDGE, B_BMAP]

theorem val_dup (cs : List StoreDuplicateChain.Entry) (tau : ValE → Nat) (es : List ValE) :
    valRecvs (ChainMetadata.assignValues cs es) B_DUP =
      (CombinedStoreOccurrences.valueOccurrences tau es).flatMap (Dr cs) := by
  simp only [valRecvs, B_DUP, B_VBYTES, B_VPARENT, ite_false, ite_true, Nat.reduceEqDiff,
    ChainMetadata.assignValues, CombinedStoreOccurrences.valueOccurrences, List.flatMap_map]
  apply flatMap_congr_mem
  intro e _
  simp only [Dr, ChainMetadata.patchValue, eidV]
  rfl

/-- The honest node/value `DUP` receives are the per-occurrence chain receives. -/
theorem dupRecvs_eq (ss : List NodeS3) (es : List ValE) (tau : ValE → Nat) (u : Inputs) (q : UseRequests) :
    let cs := chain (CombinedStoreOccurrences.allOccurrences ss tau es)
    nodeRecvs3 (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))) B_DUP ++
      valRecvs (ChainMetadata.assignValues cs es) B_DUP =
      (CombinedStoreOccurrences.allOccurrences ss tau es).flatMap (Dr cs) := by
  intro cs
  have hlen : (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))).length = ss.length := by
    simp [assignList_length, records, ChainMetadata.assign_length]
  have hocc : CombinedStoreOccurrences.nodeOccurrences ss =
      (ss.zip (List.range' 0 ss.length)).map fun x => (⟨nodeKey x.1, eidN x.2⟩ : Occurrence) := by
    unfold CombinedStoreOccurrences.nodeOccurrences
    rw [← zip_range_zipIdx, List.map_map]
    rfl
  rw [nodeRecvs_dup, hlen, List.range_eq_range', node_dup_shift, val_dup cs tau es, ← hocc,
    CombinedStoreOccurrences.allOccurrences, List.flatMap_append]

/-- **`DUP` balance of the honest records and class-ordered `uniq` entries** (given `HF`). -/
theorem dupBal_of (ss : List NodeS3) (es : List ValE) (tau : ValE → Nat) (u : Inputs) (q : UseRequests)
    (hid : ((CombinedStoreOccurrences.allOccurrences ss tau es).map Occurrence.eid).Nodup)
    (hf : HF (CombinedStoreOccurrences.allOccurrences ss tau es)) :
    let rs := CombinedStoreOccurrences.allOccurrences ss tau es
    let cs := chain rs
    Link3.DupBal (uniqEntries (uniqBlocks rs)) (assignList q 0 (records u (ChainMetadata.assign cs 0 ss)))
      (ChainMetadata.assignValues cs es) := by
  intro rs cs
  unfold Link3.DupBal
  rw [dupRecvs_eq ss es tau u q]
  exact ((uniqSends_blocks rs hf).trans (chain_dup rs hid).symm).map _

end ZkFormal.NearV3.Assembly.TrieUniqDup

namespace ZkFormal.NearV3.Assembly.TrieUniqDup

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives StoreClassPartition TrieUniqOcc TrieEnt

/-- The store occurrences of the honest pre forest. -/
def occsOf (m : MainExecutionV3) (steps : List ImplicitStepV3) : List Occurrence :=
  CombinedStoreOccurrences.allOccurrences (TrieNative.seedNodes m steps)
    (NativeStoreProvenance.valueTau (TrieNative.forest m steps)) (TrieNative.seedVals m steps)

/-- **Honest `uniqV3` entries (class-ordered).** -/
def uniqNative (m : MainExecutionV3) (steps : List ImplicitStepV3) : List UEnt := uniqBlocks (occsOf m steps)

theorem nodeOccurrences_initialize (ss : List NodeS3) :
    CombinedStoreOccurrences.nodeOccurrences (initializeList 0 ss) = CombinedStoreOccurrences.nodeOccurrences ss := by
  unfold CombinedStoreOccurrences.nodeOccurrences
  suffices h : ∀ n (ss : List NodeS3), ((initializeList n ss).zipIdx n).map (fun p => (⟨nodeKey p.1, eidN p.2⟩ : Occurrence)) =
      (ss.zipIdx n).map (fun p => (⟨nodeKey p.1, eidN p.2⟩ : Occurrence)) by
    simpa using h 0 ss
  intro n ss
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp only [initializeList, List.zipIdx_cons, List.map_cons, ih (n + 1)]; rfl

/-- Every pre tree of an accepted witness is stored in its witness store. -/
theorem forest_stored {k : WalkD0} {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3}
    {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∀ t ∈ TrieNative.forest m steps, ∃ s, Stored s t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · rw [hm.pre]; exact ⟨_, (built_spec _ trieFuel _ _ hm.root_length).2.2.1⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hp, hr, -⟩ := hv.input_facts e he
    rw [hp]
    exact ⟨_, (built_spec _ trieFuel _ _ hr).2.2.1⟩

/-- **Hash functionality of the honest occurrences** (no SHA-256 injectivity: the contents of
one instance all come from one witness store, which returns one blob per digest). -/
theorem hf_native {k : WalkD0} {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3}
    {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hw : ∀ t ∈ TrieNative.forest m steps, t.wf = true) : HF (occsOf m steps) := by
  have hk := NativeStoreProvenance.combined_keys (TrieNative.forest m steps) hw
  have hocc : occsOf m steps = CombinedStoreOccurrences.allOccurrences (forestNodes 0 0 0 (TrieNative.forest m steps))
      (NativeStoreProvenance.valueTau (TrieNative.forest m steps))
      (seedValuesFrom 0 (forestBytes (TrieNative.forest m steps))) := by
    unfold occsOf CombinedStoreOccurrences.allOccurrences TrieNative.seedNodes TrieNative.seedVals
    rw [nodeOccurrences_initialize]
  have hst := forest_stored hm hv
  intro o ho o' ho' h1 h2
  rw [hocc] at ho ho'
  have hko := hk (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hko' := hk (List.mem_map.mpr ⟨o', ho', rfl⟩)
  simp only [NativeStoreProvenance.nativeKeys, List.mem_flatMap, List.mem_map] at hko hko'
  obtain ⟨⟨t, i⟩, hti, b, hb, hbk⟩ := hko
  obtain ⟨⟨t', i'⟩, hti', b', hb', hbk'⟩ := hko'
  have hi : i = i' := by rw [← hbk, ← hbk'] at h1; exact h1
  subst hi
  have htt : t = t' := by
    have e1 := List.mem_zipIdx_iff_getElem?.mp hti
    have e2 := List.mem_zipIdx_iff_getElem?.mp hti'
    simp only [Nat.zero_add] at e1 e2
    exact Option.some.inj (e1.symm.trans e2)
  subst htt
  obtain ⟨s, hs⟩ := hst t (List.fst_mem_of_mem_zipIdx hti)
  have hfun := normalStore_hashFunctional hs
  rw [← hbk, ← hbk'] at h2 ⊢
  exact hfun b hb b' hb' h2

theorem occsOf_ids {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ((occsOf m steps).map Occurrence.eid).Nodup := by
  obtain ⟨-, hval⟩ := NativeExecutionUsage.inputs hk hw h (by decide) hm hv
  exact StoreSelectedClasses.combined_ids _ _ _ hval

theorem forest_wf {k : WalkD0} {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3}
    {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∀ t ∈ TrieNative.forest m steps, t.wf = true := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact (hv.input_facts s hs).2.2

/-- **`DUP` balance of the honest node, value and uniq entries from acceptance.** -/
theorem dupBal_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests) :
    Link3.DupBal (uniqEntries (uniqNative m steps)) (TrieNative.nodes m steps oldPost writes q)
      (TrieNative.vals m steps) :=
  dupBal_of _ _ _ _ q (occsOf_ids hk hw h hm hv) (hf_native hm hv (forest_wf hm hv))

/-- **`DIGS` balance of the honest node, head and class-ordered uniq entries from acceptance.** -/
theorem digsBal_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg) :
    Link3.DigsBal (TrieNative.nodes m steps oldPost writes q) (TrieNative.heads m steps oldPost writes keys)
      (uniqEntries (uniqNative m steps)) := by
  have hp := rawEnts_perm_occ m steps oldPost writes q keys (forest_wf hm hv)
    (TrieParent.accepted_forest_isNode hk hw h hm hv)
  have hu := uniqBlocks_perm (occsOf m steps)
  unfold Link3.DigsBal
  rw [UniqNative.uniqEntries_digs, ← UniqNative.rawEnts_digs]
  exact ((hp.trans hu.symm).flatMap_right _).map _

end ZkFormal.NearV3.Assembly.TrieUniqDup
