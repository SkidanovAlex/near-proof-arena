import ZkFormal.NearV3.Assembly.LinkWitness
import ZkFormal.NearV3.Rcpt.Candidates.PreparedNativeOwner

/-!
# ZkFormal.NearV3.Assembly.LinkShape — `RestFieldsV3.shape` (`D0Shape`) for the reconstruction

`D0Shape.wf` lists the conditions under which the strict decoders invert the encoders.  For
`xOf r (dictOf p r)`:

* claim fields: the epoch hash width (`walk_claim_epoch_length`), the chunk inner is its own
  re-encoding and well-formed (`decodeChunkInner_shape_bytes`);
* transitions: zero block hash, 32-byte post roots (`LinkWitness.post_len`), and the value
  vectors fit (`encodeSW_transition_shapes`, from `witnessBytes`);
* dictionary entries (`dict_entryWf`): fillers are trivially well formed; a first occurrence
  has a 32-byte source key, receipts well formed (`RcptE.Wf`: valid ids, named receiver, key and
  integer widths), its `from_shard` from a decoded chunk inner (`< 2^64`), `to_shard` the own
  shard, a path of `≤ 32` items with 32-byte siblings and directions `0/1`;
* no transactions, `≤ 33` transitions, and the size bound from `witnessBytes`.

**`shape_xOf`**.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace LinkShape

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3

/-! ## Claim-side facts -/

theorem decodeBlk_inners {r : BlockRec} {b : Blk} (h : decodeBlk r = .ok b) :
    ∀ q ∈ b.slots, decodeChunkInner q.1.inner = .ok q.2 := by
  unfold decodeBlk at h
  obtain ⟨hdr, -, h⟩ := Sched.bind_ok h
  obtain ⟨slots, hs, h⟩ := Sched.bind_ok h
  obtain ⟨u, -, h⟩ := Sched.bind_ok h
  cases h
  intro q hq
  obtain ⟨s, -, he⟩ := Sched.mapM_ok _ _ _ hs q hq
  obtain ⟨ci, hci, he⟩ := Sched.bind_ok he
  cases he
  exact hci

set_option maxHeartbeats 4000000 in
theorem walk_blocks {cb : Bytes} {k : WalkD0} (hw : walkD0 cb = .ok k) :
    ∀ b ∈ k.blks, ∃ r, decodeBlk r = .ok b := by
  unfold walkD0 at hw
  repeat' (first
    | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := Sched.bind_ok hh; clear hh)
    | (split at hw)
    | (dsimp only at hw))
  all_goals try (cases hw; done)
  all_goals try (exfalso; exact Sched.throw_ne (by assumption))
  all_goals
    cases hw
    intro b hb
    obtain ⟨r, -, hr⟩ := Sched.mapM_ok _ _ _ (by assumption) b hb
    exact ⟨r, hr⟩

set_option maxHeartbeats 4000000 in
theorem walk_source_sub {cb : Bytes} {k : WalkD0} (hw : walkD0 cb = .ok k) :
    ∀ b ∈ k.sourceBlks, b ∈ k.blks := by
  unfold walkD0 at hw
  repeat' (first
    | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := Sched.bind_ok hh; clear hh)
    | (split at hw)
    | (dsimp only at hw))
  all_goals try (cases hw; done)
  all_goals try (exfalso; exact Sched.throw_ne (by assumption))
  all_goals
    cases hw
    intro b hb
    exact List.mem_of_mem_drop (List.mem_of_mem_take hb)

theorem shardId_lt {bs : Bytes} {ci : ChunkInner} (h : decodeChunkInner bs = .ok ci) :
    ci.shardId < 18446744073709551616 := by
  have hwf := (decodeChunkInner_shape_bytes h).1
  simp only [V3.innerWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  exact hwf.1.1.1.1.1.1.1.1.1.1.1.2

/-- Every prepared source's `from_shard` is a decoded `u64`. -/
theorem source_fromShard {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint = .ok p) (hw : walkD0 cb = .ok k) :
    ∀ s ∈ p.lists, s.fromShard < 18446744073709551616 := by
  apply Rcpt.Candidates.preparedSourceLists_property (fun s => s.fromShard < 18446744073709551616)
    k.sourceBlks ?_ (prepD0_source_lists hp hw)
  intro B hB s hs
  obtain ⟨q, hq, hs⟩ := List.mem_flatMap.mp hs
  split at hs
  · simp only [List.mem_singleton] at hs
    subst s
    have hBk : B ∈ k.blks := walk_source_sub hw B hB
    obtain ⟨r, hr⟩ := walk_blocks hw B hBk
    exact shardId_lt (decodeBlk_inners hr q hq)
  · simp at hs

/-! ## Receipts -/

theorem receipt_wf {x : RcptE} {r : Nat} {bg : List Nat} {tok tok' : Nat} (w : x.Wf r bg tok tok') :
    V3.receiptWfD0 x.toRcptV.toReceipt = true := by
  obtain ⟨hrid, hpk, hkt, hgp, hdep, -⟩ := w.lens
  obtain ⟨hp, hv, hs, -⟩ := w.ids
  have hn := w.named
  have hg := Link.leN'_lt hgp
  have hd := Link.leN'_lt hdep
  have e128 : (256 : Nat) ^ 16 = Params.two128 := by decide
  have hpkw : PublicKey.wf ⟨x.kt, toBytes x.pk⟩ = true := by
    rcases (by omega : x.kt = 0 ∨ x.kt = 1) with h0 | h0 <;>
      simp [PublicKey.wf, Link.toBytes_length, hpk, h0]
  simp only [V3.receiptWfD0, Receipt.wf, RcptV.toReceipt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hp, hv⟩, hs⟩, hpkw⟩, by rw [Link.toBytes_length, hrid]⟩, decide_eq_true hg⟩, decide_eq_true hd⟩, hn⟩

/-! ## The dictionary -/

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

theorem dict_entryWf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ((dictOf p r).map DictionaryEntryV3.entry).all V3.entryWf = true := by
  apply List.all_eq_true.mpr
  intro e he
  unfold dictOf at he
  rw [Rcpt.Candidates.nativeDictionary_entries, List.mem_append] at he
  rcases he with he | he
  · simp only [Rcpt.Candidates.firstNativeEntries, Rcpt.Candidates.firstNativeSources, List.map_map,
      List.mem_map] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hil := Rcpt.Candidates.firstSourceIndices_lt p.lists hi
    have hs : p.lists.getD i ⟨[], 0, []⟩ ∈ p.lists := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
      exact List.getElem_mem hil
    have hkey := Rcpt.Candidates.prepD0_source_key_shape hp hw _ hs
    have hfrom := source_fromShard hp hw _ hs
    have hown : p.hdr.own < 18446744073709551616 := by
      rw [prepD0_source_owner hp hw]
      exact shardId_lt (walkD0_header_decode hw)
    -- receipts of the list
    have hrs : ∀ x ∈ (r.lists.getD i default).rs, x ∈ flatR r.lists := by
      intro x hx
      rw [List.getD_eq_getElem?_getD] at hx
      cases hl : r.lists[i]? with
      | none =>
        rw [hl] at hx
        exact absurd hx (by show x ∉ ([] : List RcptE); simp)
      | some L =>
        rw [hl, Option.getD_some] at hx
        exact List.mem_flatMap.mpr ⟨L, List.mem_of_getElem? hl, hx⟩
    have hrlen : (r.lists.getD i default).rs.length ≤ (flatR r.lists).length := by
      rw [List.getD_eq_getElem?_getD]
      cases hl : r.lists[i]? with
      | none => show ([] : List RcptE).length ≤ _; simp
      | some L =>
        rw [Option.getD_some]
        have hL := List.mem_of_getElem? hl
        simp only [flatR, List.length_flatMap]
        exact LinkRidBytes.le_sum_of_mem' (List.mem_map_of_mem (f := fun L : ListV3 => L.rs.length) hL)
    have hcnt := W.listsCount.2
    obtain ⟨toks, -, -, hwfs, -⟩ := W.lists.toks
    have hwf : ∀ x ∈ (r.lists.getD i default).rs, V3.receiptWfD0 x.toRcptV.toReceipt = true := by
      intro x hx
      obtain ⟨j, hj, he⟩ := List.getElem_of_mem (hrs x hx)
      have := receipt_wf (hwfs j hj)
      rwa [he] at this
    -- the path
    have hpath : ∀ it ∈ (r.srcp.getD i default).path, it.sib.length = 32 := by
      intro it hit
      rw [List.getD_eq_getElem?_getD] at hit
      cases hb : r.srcp[i]? with
      | none =>
        rw [hb] at hit
        exact absurd hit (by show it ∉ ([] : List SrcpItem); simp)
      | some B =>
        rw [hb, Option.getD_some] at hit
        have hB := W.srcp.block B (List.mem_of_getElem? hb)
        split at hB
        · rw [hB.2.1] at hit; simp at hit
        · exact (hB.len.2.2 it hit).1
    have hdepth : (r.srcp.getD i default).path.length ≤ 32 := by
      rw [List.getD_eq_getElem?_getD]
      cases hb : r.srcp[i]? with
      | none => show ([] : List SrcpItem).length ≤ 32; simp
      | some B => exact W.srcpDepth B (List.mem_of_getElem? hb)
    simp only [Function.comp_apply, Rcpt.Candidates.nativeEntryAt, Rcpt.Candidates.DedupProof.nativeSourceEntry,
      SourceEntryV3.entry, V3.entryWf, V3.h32, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.length_map, List.all_eq_true, List.mem_map]
    refine ⟨⟨⟨⟨⟨⟨hkey, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · first | omega | exact decide_eq_true (by omega)
    · rintro _ ⟨x, hx, rfl⟩
      exact hwf x hx
    · first | exact hfrom | exact decide_eq_true hfrom
    · first | exact hown | exact decide_eq_true hown
    · first | omega | exact decide_eq_true (by omega)
    · rintro _ ⟨it, hit, rfl⟩
      simp only [V3.pathWf, V3.h32, Link3.toB, List.length_map, hpath it hit, Bool.and_eq_true,
        beq_self_eq_true, decide_eq_true_eq, true_and]
      split <;> omega
  · obtain ⟨key, hk, rfl⟩ := List.mem_map.mp he
    have hkl := Rcpt.Candidates.nativeFillers_key_length p.lists he
    simp only [Rcpt.Candidates.fillerEntry] at hkl
    simp [V3.entryWf, Rcpt.Candidates.fillerEntry, V3.h32, hkl]

/-! ## Transitions -/

/-- Zero block hashes and 32-byte post roots on every transition of the reconstruction. -/
theorem trans_hashes (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) :
    TransitionHashes (stateWitnessOfV3 k (xOf r d)).main ∧
      ∀ t ∈ (stateWitnessOfV3 k (xOf r d)).implicit, TransitionHashes t := by
  have hKk : p.hdr.K = k.implicitBlks.length := (prepD0_root_endpoints hp hw).2.2
  have L := trieLink_of hp hsz hH T W
  have hpost : ∀ τ, τ ≤ p.hdr.K → ((xOf r d).post τ).length = 32 := by
    intro τ hτ
    rw [LinkImplicit.post_xHeads (x := xOf r d) rfl (L.chain.ups_mem τ hτ)]
    obtain ⟨hmem, -⟩ := L.chain.ups_mem τ hτ
    obtain ⟨s, -, hs⟩ := List.mem_map.mp hmem
    rw [← hs]
    simp [toB, UpsRows.upsE, UpsRows.regN_len]
  have hil : (stateWitnessOfV3 k (xOf r d)).implicit =
      (List.range p.hdr.K).map fun i => (xOf r d).transition (i + 1) := by
    rw [hKk]
    exact LinkWitness.zipIdx_map_range (fun i => (xOf r d).transition (i + 1)) k.implicitBlks
  refine ⟨⟨by simp [stateWitnessOfV3, ExtV3.transition], hpost 0 (Nat.zero_le _)⟩, ?_⟩
  intro t ht
  rw [hil] at ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  exact ⟨by simp [ExtV3.transition], hpost (i + 1) (by have := List.mem_range.mp hi; omega)⟩

/-- **`RestFieldsV3.shape`** for the reconstruction. -/
theorem shape_xOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (C : ClaimFieldsV3 k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r) :
    V3.D0Shape (stateWitnessOfV3 k (xOf r (dictOf p r))) := by
  have hb := LinkWitness.witnessBytes_xOf hp hw C hsz hH W T
  obtain ⟨hm, hi⟩ := trans_hashes hp hw hsz hH W T (dictOf p r)
  have htw := encodeSW_transition_shapes hb hm hi
  have hhead := decodeChunkInner_shape_bytes (walkD0_header_decode hw)
  have he := Rcpt.Candidates.SizeCount.walk_claim_epoch_length hw
  have hbound : lenT (V3.encodeSW (stateWitnessOfV3 k (xOf r (dictOf p r)))) ≤ MAX_WITNESS := by
    rw [ReexecV3D0.lenT_eq]
    unfold MAX_WITNESS
    omega
  have hsrc := Rcpt.Candidates.prepD0_source_count hp
  have hec : ((dictOf p r).map DictionaryEntryV3.entry).length < 4294967296 := by
    unfold dictOf
    rw [Rcpt.Candidates.nativeDictionary_entries, List.length_append,
      Rcpt.Candidates.nativeFillers_length _ hsrc]
    have hl : (Rcpt.Candidates.firstNativeEntries p.lists p.hdr.own r.lists r.srcp).length =
        (Rcpt.Candidates.firstSourceIndices p.lists).length := by
      simp [Rcpt.Candidates.firstNativeEntries, Rcpt.Candidates.firstNativeSources]
    have hfl : (Rcpt.Candidates.firstSourceIndices p.lists).length ≤ p.lists.length := by
      simpa only [Rcpt.Candidates.firstSourceIndices, List.length_range] using
        List.length_filter_le (fun j => !Public.sourceDup p.lists j) (List.range p.lists.length)
    omega
  have hea := dict_entryWf (oh := oh) hp hw W
  -- the implicit count
  have hcount := receiptCount_of_records hp W.lists (xOf r (dictOf p r)) rfl
  have hn : h.n = (flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  obtain ⟨m, last, hmv, -, -⟩ :=
    RcptLink.executions_holdsP hp hsz hH T W hw hn (x := xOf r (dictOf p r)) rfl rfl rfl rfl hmb hmp
  have hicount : (stateWitnessOfV3 k (xOf r (dictOf p r))).implicit.length < 4294967296 := by
    rw [stateWitnessOfV3_implicit_length]
    have hlen : k.implicitBlks.length < (schedulerContexts k m).length := by
      simp [schedulerContexts]
    obtain ⟨sp, hsp, -⟩ := prepD0_context_index_of hp hw hmv.block hmv.previous _ _
      (List.getElem?_eq_getElem hlen)
    have := (List.getElem?_eq_some_iff.mp hsp).1
    have := Sched.prepD0_len hp
    omega
  simp only [V3.D0Shape, V3.D0Shape.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hhead.2⟩, hhead.1⟩, htw.1⟩, hec⟩, hea⟩, ?_⟩, rfl⟩, hicount⟩, htw.2⟩, rfl⟩, hbound⟩
  · simp [stateWitnessOfV3, V3.h32, he]
  · simp [stateWitnessOfV3, V3.h32, ArenaCore.sha256_length]

end LinkShape

end ZkFormal.NearV3.Assembly
