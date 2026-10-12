import ZkFormal.NearV3.Assembly.A9Native
import ZkFormal.NearV3.Assembly.CanonicalReplay

/-!
# ZkFormal.NearV3.Assembly.LinkCanon — `RestFieldsV3.canonicalScheduler` (Canon0f)

`reads0f k sw` reads the `0x0f` value of every applied pre-state (main, then each implicit one)
through a *singleton* partial trie of the witness store.  For the reconstruction `xOf r d`:

* `singleton_find` — a key the full build determines is answered alike by the singleton build
  (`buildFor_spec`); `root_len` — a determinate lookup needs a 32-byte root;
* `itv_reads` — along an implicit trace, the singleton reads are the steps' pre-trie lookups;
* `reads_prevOf` — every read is the codec's previous state `prevOf tr T_CODEC τ` of an
  instance `τ ≤ K` (`A9Native.prev_of_step`, `implicit_prev`, `LinkSched0.pre_find_key`);
* `canonical_of_prevCanon` — the scheduler core's `PrevCanon` (`LinkSchedCore.schedCore_v3`: the
  previous state is absent or the canonical link list of the instance's shard ids) is
  `canonical0f` for the layout (`canonLinks_pairs`: the canonical link order is `layoutLinks`);
* **`canonicalScheduler_xOf`** — `(reads0f k (stateWitnessOfV3 k (xOf r d))).all (canonical0f k.L)`,
  given the `shape` and `source.applied` fields (as `A9Native.chachaWords_xOf`).
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace LinkCanon

/-! ## Singleton lookups -/

theorem storeGet_len {ws : List Bytes} {h b : Bytes} (hg : storeGet (mkStore ws) h = some b) :
    h.length = 32 := by
  unfold storeGet at hg
  split at hg
  · rename_i q hq
    have hm := List.mem_of_find?_eq_some hq
    have he := List.find?_some hq
    simp only [mkStore, List.mem_map] at hm
    obtain ⟨v, -, rfl⟩ := hm
    simp only [beq_iff_eq] at he
    rw [← he]
    exact ArenaCore.sha256_length v
  · cases hg

/-- A determinate lookup on a built partial trie needs a 32-byte root. -/
theorem root_len {ws : List Bytes} {root : Bytes} {keys : List (List Nat)} {key : List Nat}
    (hk : (partialTrie ws root keys).find key ≠ none) : root.length = 32 := by
  unfold partialTrie at hk
  generalize trieFuel = f at hk
  cases f with
  | zero => exact absurd (find_hash_none root key) (by simpa [buildFor] using hk)
  | succ f =>
    simp only [buildFor] at hk
    split at hk
    · exact absurd (find_hash_none root key) hk
    · split at hk
      · exact absurd (find_hash_none root key) hk
      · rename_i node hg
        exact storeGet_len hg

/-- **The singleton build answers a determinate key like the full build.** -/
theorem singleton_find {ws : List Bytes} {root : Bytes} {keys : List (List Nat)} {key : List Nat}
    (hk : (partialTrie ws root keys).find key ≠ none) :
    (partialTrie ws root [key]).find key = (partialTrie ws root keys).find key := by
  have hr := root_len hk
  have hb := built_spec ws trieFuel root keys hr
  have hroot : (partialTrie ws root keys).hashOf = root := hb.1
  have hkeys : ∀ k ∈ [key], (partialTrie ws root keys).find k ≠ none := by
    intro k h
    have : k = key := by simpa using h
    subst k
    exact hk
  have ho := buildFor_spec (mkStore ws) trieFuel (partialTrie ws root keys) [key]
    hb.2.1 hb.2.2.1 hkeys
  rw [hroot] at ho
  exact ho.2 key (by simp) (hb.2.2.2 key)

/-- The main read is the native main pre trie's `0x0f` lookup. -/
theorem main_read {k : WalkD0} {x : ExtV3} {m : MainExecutionV3} (hm : m.Valid k x) :
    bwRead (x.store 0) k.slotB2.prevStateRoot = (m.pre.find keyBwState).getD none := by
  have hf := applyNewChunk_bw_find hm.run
  rw [hm.pre] at hf ⊢
  unfold bwRead
  rw [singleton_find hf]

/-- Along an implicit trace, the singleton reads are the steps' pre-trie lookups. -/
theorem itv_reads {k : WalkD0} {root last : Bytes} {pairs : List (Blk × Transition)}
    {steps : List ImplicitStepV3} (h : ImplicitTraceValid k root pairs steps last) :
    bwReadsFrom root (pairs.map Prod.snd) =
      steps.map (fun s => (s.pre.find keyBwState).getD none) := by
  induction h with
  | nil => rfl
  | cons root b t rest steps post last hrun hpost htail ih =>
    have hf := applyMissingChunk_bw_find hrun
    simp only [List.map_cons, bwReadsFrom]
    rw [← hpost, ih]
    unfold bwRead
    rw [singleton_find hf]

/-! ## The canonical link order -/

theorem range_getD_self (B : List Nat) : (List.range B.length).map (fun l => B.getD l 0) = B := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem map_range_getD {β : Type} (f : Nat → β) (B : List Nat) :
    B.map f = (List.range B.length).map (fun l => f (B.getD l 0)) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1 : i < B.length)]

theorem grid_pairs (B : List Nat) : ∀ A : List Nat,
    (List.range (A.length * B.length)).map
        (fun l => (A.getD (l / B.length) 0, B.getD (l % B.length) 0)) =
      A.flatMap (fun s => B.map (fun r => (s, r)))
  | [] => by simp
  | a :: A => by
    have ih := grid_pairs B A
    rcases Nat.eq_zero_or_pos B.length with hB | hB
    · have : B = [] := List.eq_nil_of_length_eq_zero hB
      subst this
      simp
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm, List.range_add, List.map_append,
      List.flatMap_cons, List.map_map, ← ih, map_range_getD (fun r => (a, r)) B]
    congr 1
    · apply List.map_congr_left
      intro l hl
      have hl' := List.mem_range.mp hl
      simp [Nat.div_eq_of_lt hl', Nat.mod_eq_of_lt hl']
    · apply List.map_congr_left
      intro l hl
      have e1 : (B.length + l) / B.length = l / B.length + 1 := by
        rw [Nat.add_comm, Nat.add_div_right _ hB]
      have e2 : (B.length + l) % B.length = l % B.length := by
        rw [Nat.add_comm, Nat.add_mod_right]
      simp [e1, e2]

theorem canonLinks_pairs (ids : List Nat) (a : Nat → Nat) :
    (Sched.canonLinks ids a).map (fun la => (la.sender, la.receiver)) =
      ids.flatMap fun s => ids.map fun r => (s, r) := by
  unfold Sched.canonLinks
  rw [List.map_map]
  exact grid_pairs ids ids

/-- **`PrevCanon` is `canonical0f`.** -/
theorem canonical_of_prevCanon {L : Layout} {prev : Option Bytes} {a0 : Nat → Nat} {h0 : Bytes}
    (hn64 : L.shardIds.length ≤ 64) (hids : ∀ x ∈ L.shardIds, x < 2 ^ 64)
    (h : Sched.PrevCanon L.shardIds prev a0 h0) : canonical0f L prev = true := by
  rcases h with ⟨rfl, -, -⟩ | ⟨rfl, hh, ha⟩
  · rfl
  · have hid0 : ∀ i, L.shardIds.getD i 0 < 2 ^ 64 := by
      intro i
      rw [List.getD_eq_getElem?_getD]
      cases hi : L.shardIds[i]? with
      | none => simp
      | some v => exact hids v (List.mem_of_getElem? hi)
    have hd := Sched.decode_encode ⟨Sched.canonLinks L.shardIds a0, h0⟩
      (by
        intro la hla
        simp only [Sched.canonLinks, List.mem_map, List.mem_range] at hla
        obtain ⟨l, -, rfl⟩ := hla
        exact ⟨hid0 _, hid0 _, ha l⟩)
      hh
      (by
        simp only [Sched.canonLinks, List.length_map, List.length_range]
        have : L.shardIds.length * L.shardIds.length ≤ 64 * 64 := Nat.mul_le_mul hn64 hn64
        omega)
    simp only [canonical0f, hd, beq_iff_eq]
    exact canonLinks_pairs L.shardIds a0

end LinkCanon

/-! ## The reads of the reconstruction -/

namespace LinkCanon

section Rec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
  ZkFormal.NearV3.UpsRows LinkImplicit A7Native A9Native

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **Every `0x0f` read of the reconstruction is a codec previous state** of an instance `τ ≤ K`
with a prepared scheduler context. -/
theorem reads_prevOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    ∀ v ∈ reads0f k (stateWitnessOfV3 k (xOf r d)), ∃ τ, ∃ hτ : τ < p.sched.length,
      v = Sched.prevOf tr T_CODEC τ ∧ p.sched[τ].ids = k.L.shardIds := by
  have hcount := receiptCount_of_records hp W.lists (xOf r d) rfl
  have hn : h.n = (flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  obtain ⟨m, last, hm, hi, -⟩ :=
    RcptLink.executions_holdsP hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl rfl hmb hmp
  have hsb := mainStoreBytes_ext hp hsz hH T W (xOf r d) rfl rfl
  obtain ⟨steps, hv, -⟩ := triesD0_xOf hw hs happ hsb hm hi
  have hroot : m.result.trie.hashOf = rootAt p r 1 := by
    rw [hm.postRoot, post0_eq hp hsz hH T W (x := xOf r d) rfl]
  have hv' := hv
  rw [hroot] at hv'
  have hIP := implicit_prev hp hsz hH T W hw hm.block hm.previous
    (LinkPostRec.postPreOff0_holds hp hsz hH T W) (LinkDelayed.delayedCovered_holds hp hsz hH T W)
    (x := xOf r d) rfl rfl rfl p.hdr.K 1 (by omega) (Nat.le_refl 1) steps last (by simpa using hv')
  -- the prepared scheduler context of index `τ`
  have hctx : ∀ τ, τ ≤ k.implicitBlks.length →
      ∃ hτ : τ < p.sched.length, p.sched[τ].ids = k.L.shardIds := by
    intro τ hτ
    have hc : ∃ ctx, (schedulerContexts k m)[τ]? = some ctx ∧ ctx.layout = k.L := by
      cases τ with
      | zero => exact ⟨m.ctx k, by simp [schedulerContexts], rfl⟩
      | succ j =>
        have hj : j < k.implicitBlks.length := by omega
        exact ⟨blockCtx k.L k.H.shardId k.slotB2.gasLimit k.implicitBlks[j]
          k.implicitBlks[j].hdr.nextGasPrice, by simp [schedulerContexts, List.getElem?_eq_getElem hj], rfl⟩
    obtain ⟨ctx, hci, hL⟩ := hc
    obtain ⟨sp, hsp, hpub⟩ := prepD0_context_index_of hp hw hm.block hm.previous τ ctx hci
    obtain ⟨hτ', hsp'⟩ := List.getElem?_eq_some_iff.mp hsp
    refine ⟨hτ', ?_⟩
    rw [hsp']
    unfold schedPub Scheduler.pubOf at hpub
    simp only [bind, Option.bind] at hpub
    split at hpub
    · cases hpub
    · split at hpub
      · cases hpub
      · simp only [Option.some.injEq] at hpub
        rw [← hpub, hL]
  have hKk : p.hdr.K = k.implicitBlks.length := (prepD0_root_endpoints hp hw).2.2
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length, implicitPairs, List.length_map, List.length_zipIdx]
  -- main
  have hmain : m.pre.find keyBwState = some (Sched.prevOf tr T_CODEC 0) := by
    obtain ⟨h1, -⟩ := main_refined hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl hm
    obtain ⟨h0, -⟩ := hctx 0 (Nat.zero_le _)
    obtain ⟨Q, so, hst⟩ := main_step hm.run
    have hF := LinkSched0.pre_find_key hp hsz hH T W h0 (Nat.zero_le _)
    rw [← LinkVBytes.keyBwState_eq] at hF
    exact prev_of_step h1 hst hF
  -- the implicit reads
  have himp : (stateWitnessOfV3 k (xOf r d)).implicit =
      (implicitPairs (xOf r d) 1 k.implicitBlks).map Prod.snd := by
    rw [← stateWitnessOfV3_implicit_pairs, List.map_snd_zip]
    rw [stateWitnessOfV3_implicit_length]; exact Nat.le_refl _
  have hpost0 : (stateWitnessOfV3 k (xOf r d)).main.postStateRoot = m.result.trie.hashOf := by
    show (xOf r d).post 0 = _
    exact hm.postRoot.symm
  rw [reads0f_eq, hpost0, himp, itv_reads hv]
  intro v hvm
  rcases List.mem_cons.mp hvm with hv0 | hv1
  · -- main
    refine ⟨0, (hctx 0 (Nat.zero_le _)).1, ?_, (hctx 0 (Nat.zero_le _)).2⟩
    rw [hv0]
    show bwRead ((xOf r d).store 0) k.slotB2.prevStateRoot = _
    rw [main_read hm, hmain]
    rfl
  · obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hv1
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsm
    obtain ⟨hτ, hids⟩ := hctx (1 + j) (by omega)
    refine ⟨1 + j, hτ, ?_, hids⟩
    rw [hIP j hj]
    rfl

/-- **`RestFieldsV3.canonicalScheduler`** for the reconstruction (with the `shape` and
`source.applied` fields). -/
theorem canonicalScheduler_xOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    (reads0f k (stateWitnessOfV3 k (xOf r d))).all (canonical0f k.L) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨τ, hτ, rfl, hids⟩ := reads_prevOf hp hw hsz hH W T d hs happ v hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hprev, -⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W hτ
  have hP := Sched.instOk_of hp τ (by rw [List.length_map]; exact hτ)
  rw [Sched.getD_map_instOf _ hτ] at hP
  have hn64 : p.sched[τ].ids.length ≤ 64 := hP.n64
  have hids64 : ∀ x ∈ p.sched[τ].ids, x < 2 ^ 64 := hP.ids64
  rw [hids] at hprev hn64 hids64
  exact canonical_of_prevCanon hn64 hids64 hprev

end Rec

end LinkCanon

end ZkFormal.NearV3.Assembly
