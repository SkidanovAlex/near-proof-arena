import ZkFormal.NearV3.Assembly.A9Words
import ZkFormal.NearV3.Assembly.A7Native

/-!
# ZkFormal.NearV3.Assembly.A9Native — the native alignment of the scheduler inputs; `chachaWords`

For the reconstruction `xOf r d` (with the `shape` and `source.applied` fields of `RestFieldsV3`, as
`A7Native.unfold_le_records`), every scheduler input of `schedInsD0` is the claim-only part
`p.sched[τ]` of instance `τ` on the codec's previous state:

* `find_refinedBy`: a pruning answers a revealed lookup like the full trie;
* `prev_of_step`: a successful `schedStep` on a pruning of `F` reads `F`'s `0x0f` value;
* `implicit_prev`: the native implicit pre tries read `prevOf tr T_CODEC τ` (induction as
  `A7Native.implicit_sum`);
* **`a9Native_xOf`**: `A9Words.A9Native cb (witnessOfV3 k (xOf r d)) p tr`;
* **`chachaWords_xOf`**: `RestFieldsV3.chachaWords` (`chachaWords … ≤ W0`).
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace A9Native

/-! ## Lookups on a pruning -/

mutual
theorem find_refinedBy : ∀ (t₁ t₂ : PTrie) (key : List Nat) (v : Option Bytes), t₁.refinedBy t₂ →
    t₁.find key = some v → t₂.find key = some v
  | .hash _, _, _, _, _, hf => by simp [PTrie.find] at hf
  | .leaf k s m, t₂, key, v, hr, hf => by
    cases t₂ with
    | leaf k' s' m' =>
      obtain ⟨rfl, rfl, hs⟩ := hr
      simp only [PTrie.find] at hf ⊢
      split
      · rename_i hk
        rw [if_pos hk] at hf
        rcases hs with rfl | ⟨w, rfl, rfl⟩
        · exact hf
        · simp [Slot.get] at hf
      · rename_i hk; rw [if_neg hk] at hf; exact hf
    | _ => simp [PTrie.refinedBy] at hr
  | .ext k c m, t₂, key, v, hr, hf => by
    cases t₂ with
    | ext k' c' m' =>
      obtain ⟨rfl, rfl, hc⟩ := hr
      simp only [PTrie.find] at hf ⊢
      split
      · rename_i hp
        rw [if_pos hp] at hf
        exact find_refinedBy c c' _ v hc hf
      · rename_i hp; rw [if_neg hp] at hf; exact hf
    | _ => simp [PTrie.refinedBy] at hr
  | .branch o cs m, t₂, key, v, hr, hf => by
    cases t₂ with
    | branch o' cs' m' =>
      obtain ⟨-, ho, hcs⟩ := hr
      cases key with
      | nil =>
        simp only [PTrie.find] at hf ⊢
        cases o with
        | none =>
          cases o' with
          | none => exact hf
          | some _ => simp [OptSlotRefines] at ho
        | some s =>
          cases o' with
          | none => simp [OptSlotRefines] at ho
          | some s' =>
            simp only [OptSlotRefines] at ho
            rcases ho with rfl | ⟨w, rfl, rfl⟩
            · exact hf
            · simp [Slot.get] at hf
      | cons n rest =>
        simp only [PTrie.find] at hf ⊢
        exact kfind_refinedBy cs cs' n rest v hcs hf
    | _ => simp [PTrie.refinedBy] at hr
theorem kfind_refinedBy : ∀ (cs cs' : Kids) (n : Nat) (key : List Nat) (v : Option Bytes),
    Kids.refinedBy cs cs' → Kids.find cs n key = some v → Kids.find cs' n key = some v
  | .nil, cs', n, key, v, hr, hf => by cases cs' <;> simp_all [Kids.refinedBy, Kids.find]
  | .none a, cs', n, key, v, hr, hf => by
    cases cs' with
    | none a' =>
      cases n with
      | zero => simpa [Kids.find] using hf
      | succ n => simp only [Kids.find] at hf ⊢; exact kfind_refinedBy a a' n key v hr hf
    | _ => simp [Kids.refinedBy] at hr
  | .some c a, cs', n, key, v, hr, hf => by
    cases cs' with
    | some c' a' =>
      cases n with
      | zero => simp only [Kids.find] at hf ⊢; exact find_refinedBy c c' key v hr.1 hf
      | succ n => simp only [Kids.find] at hf ⊢; exact kfind_refinedBy a a' n key v hr.2 hf
    | _ => simp [Kids.refinedBy] at hr
end

/-- A successful scheduler step on a pruning of `F` reads `F`'s `0x0f` value. -/
theorem prev_of_step {ctx : ApplyCtx} {P F Q : PTrie} {so : SchedOut} {v : Option Bytes}
    (hr : P.refinedBy F) (hs : schedStep prims ctx P = .ok (Q, so))
    (hF : F.find keyBwState = some v) : P.find keyBwState = some v := by
  obtain ⟨prev, -, -, hrd, -⟩ := schedStep_complete hs
  unfold readKey at hrd
  split at hrd
  · rename_i w hw
    have := find_refinedBy P F _ _ hr hw
    rw [hF] at this
    rw [hw, this]
  · cases hrd

theorem missing_step {ctx : ApplyCtx} {P post : PTrie} (h : applyMissingChunk prims ctx P = .ok post) :
    ∃ Q so, schedStep prims ctx P = .ok (Q, so) := by
  unfold applyMissingChunk at h
  obtain ⟨_, _, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  obtain ⟨⟨Q, so⟩, hs, _⟩ := ZkFormal.NearV3.Sched.bind_ok h
  exact ⟨Q, so, hs⟩

theorem main_step {ctx : ApplyCtx} {P : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx P rs = .ok out) : ∃ Q so, schedStep prims ctx P = .ok (Q, so) := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  obtain ⟨_, _, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  obtain ⟨⟨Q, so⟩, hs, _⟩ := ZkFormal.NearV3.Sched.bind_ok h
  exact ⟨Q, so, hs⟩

/-! ## The implicit pre tries -/

section Rec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
  ZkFormal.NearV3.UpsRows LinkImplicit A7Native

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **The native implicit pre tries read the codec's previous states.** -/
theorem implicit_prev (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) {m : MainExecutionV3}
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE)) :
    ∀ n τ, τ + n = p.hdr.K + 1 → 1 ≤ τ → ∀ steps last,
      ImplicitTraceValid k (rootAt p r τ) (implicitPairs x τ (k.implicitBlks.drop (τ - 1))) steps last →
      ∀ j (hj : j < steps.length),
        steps[j].pre.find NearSpecV3.keyBwState = some (Sched.prevOf tr T_CODEC (τ + j)) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨-, -, hKk⟩ := prepD0_root_endpoints hp hw
  intro n
  induction n with
  | zero =>
    intro τ hτ h1 steps last hv j hj
    have hd : k.implicitBlks.drop (τ - 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd] at hv
    simp [implicitPairs] at hv
    rw [itv_nil_inv hv] at hj
    simp at hj
  | succ n ih =>
    intro τ hτ h1 steps last hv j hj
    obtain ⟨j0, rfl⟩ : ∃ j0, τ = j0 + 1 := ⟨τ - 1, by omega⟩
    have hlt : j0 < k.implicitBlks.length := by omega
    simp only [Nat.add_sub_cancel] at hv
    rw [List.drop_eq_getElem_cons hlt, implicitPairs_cons] at hv
    obtain ⟨steps', post, hrun, hroot, htail, rfl⟩ := itv_cons_inv hv
    have hci : (schedulerContexts k m)[j0 + 1]? = some (NearSpecV3.blockCtx k.L k.H.shardId
        k.slotB2.gasLimit k.implicitBlks[j0] k.implicitBlks[j0].hdr.nextGasPrice) := by
      simp [schedulerContexts, List.getElem?_eq_getElem hlt]
    obtain ⟨sp, hsp, hpub⟩ := prepD0_context_index_of hp hw hmb hmp (j0 + 1) _ hci
    obtain ⟨hτs, hsp'⟩ := List.getElem?_eq_some_iff.mp hsp
    cases j with
    | zero =>
      obtain ⟨hpre, -⟩ := implicit_refined hp hsz hH T W Hpp Hdel hxn hxv (τ := j0 + 1) (by omega)
        (by omega) hτs (by rw [hsp']; exact hpub) hrun
      obtain ⟨Q, so, hs⟩ := missing_step hrun
      have hF := LinkSched0.pre_find_key hp hsz hH T W hτs (by omega)
      rw [← LinkVBytes.keyBwState_eq] at hF
      exact prev_of_step hpre hs hF
    | succ j =>
      have hnext : post.hashOf = rootAt p r (j0 + 1 + 1) := by
        rw [hroot]
        show x.post (j0 + 1) = _
        rw [post_xHeads hxh (L.chain.ups_mem (j0 + 1) (by omega)),
          LinkImplicit.ups_post hp hsz hH T W (by omega)]
      rw [hnext] at htail
      have := ih (j0 + 1 + 1) (by omega) (by omega) steps' last (by simpa using htail) j
        (by simpa using hj)
      rw [show j0 + 1 + (j + 1) = j0 + 1 + 1 + j by omega]
      simpa using this

/-- **The native alignment of the reconstruction.** -/
theorem a9Native_xOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    A9Words.A9Native cb (witnessOfV3 k (xOf r d)) p tr := by
  intro l hl
  have hcount := receiptCount_of_records hp W.lists (xOf r d) rfl
  have hn : h.n = (flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  obtain ⟨m, last, hm, hi, -⟩ :=
    RcptLink.executions_holdsP hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl rfl hmb hmp
  have hsb := mainStoreBytes_ext hp hsz hH T W (xOf r d) rfl rfl
  obtain ⟨steps, hv, htr⟩ := triesD0_xOf hw hs happ hsb hm hi
  obtain ⟨h1, -⟩ := main_refined hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl hm
  have hroot : m.result.trie.hashOf = rootAt p r 1 := by
    rw [hm.postRoot, post0_eq hp hsz hH T W (x := xOf r d) rfl]
  rw [hroot] at hv
  have hIP := implicit_prev hp hsz hH T W hw hm.block hm.previous
    (LinkPostRec.postPreOff0_holds hp hsz hH T W) (LinkDelayed.delayedCovered_holds hp hsz hH T W)
    (x := xOf r d) rfl rfl rfl p.hdr.K 1 (by omega) (Nat.le_refl 1) steps last (by simpa using hv)
  unfold schedInsD0 at hl
  simp only [hw, decode_of_shape hs, hm.block, hm.previous, htr, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hl
  subst hl
  generalize hZ : (blockCtx k.L k.H.shardId k.slotB2.gasLimit m.block m.previous.hdr.nextGasPrice ::
      List.map (fun x => blockCtx k.L k.H.shardId k.slotB2.gasLimit x.fst x.fst.hdr.nextGasPrice)
        (k.implicitBlks.zip (stateWitnessOfV3 k (xOf r d)).implicit)).zip
      ((m.pre, m.result.trie) :: unfoldedPairs steps) = Z
  -- per index: the context is the prepared one, the pre trie reads `prevOf`
  have key : ∀ τ (hτ : τ < Z.length), (schedulerContexts k m)[τ]? = some Z[τ].1 ∧
      Z[τ].2.1.find keyBwState = some (Sched.prevOf tr T_CODEC τ) := by
    intro τ hτ
    subst hZ
    cases τ with
    | zero =>
      simp only [List.zip_cons_cons, List.getElem_cons_zero]
      refine ⟨by simp [schedulerContexts, MainExecutionV3.ctx], ?_⟩
      obtain ⟨sp, hsp, -⟩ := prepD0_context_index_of hp hw hm.block hm.previous 0 (m.ctx k)
        (by simp [schedulerContexts])
      have h0 : 0 < p.sched.length := (List.getElem?_eq_some_iff.mp hsp).1
      obtain ⟨Q, so, hs⟩ := main_step hm.run
      have hF := LinkSched0.pre_find_key hp hsz hH T W h0 (Nat.zero_le _)
      rw [← LinkVBytes.keyBwState_eq] at hF
      exact prev_of_step h1 hs hF
    | succ j =>
      simp only [List.zip_cons_cons, List.getElem_cons_succ, List.getElem_zip, List.getElem_map]
      simp only [List.length_zip, List.length_cons, List.length_map] at hτ
      have hj1 : j < k.implicitBlks.length := by omega
      have hj2 : j < steps.length := by simp only [unfoldedPairs, List.length_map] at hτ; omega
      refine ⟨?_, ?_⟩
      · simp [schedulerContexts, List.getElem?_eq_getElem hj1]
      · simp only [unfoldedPairs, List.getElem_map]
        have := hIP j hj2
        rwa [Nat.add_comm 1 j] at this
  have hpub : ∀ τ (hτ : τ < Z.length), ∃ hτ' : τ < p.sched.length, schedPub Z[τ].1 = some p.sched[τ] := by
    intro τ hτ
    obtain ⟨sp, hsp, hpub⟩ := prepD0_context_index_of hp hw hm.block hm.previous τ _ (key τ hτ).1
    obtain ⟨hτ', hsp'⟩ := List.getElem?_eq_some_iff.mp hsp
    exact ⟨hτ', by rw [hsp']; exact hpub⟩
  refine ⟨?_, ?_⟩
  · rw [List.length_map]
    rcases Nat.eq_zero_or_pos Z.length with h0 | h0
    · omega
    · have := (hpub (Z.length - 1) (by omega)).1; omega
  · intro τ hτ hτ'
    rw [List.length_map] at hτ
    simp only [List.getElem_map]
    refine ⟨(hpub τ hτ).2, ?_⟩
    rw [(key τ hτ).2]
    rfl

/-- **`RestFieldsV3.chachaWords`** for the reconstruction (with the `shape` and `source.applied`
fields): `chachaWords cb (witnessOfV3 k (xOf r d)) ≤ W0`. -/
theorem chachaWords_xOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    chachaWords cb (witnessOfV3 k (xOf r d)) ≤ W0 :=
  A9Words.chachaWords_of_native hp hsz hH T W (a9Native_xOf hp hw hsz hH W T d hs happ)

end Rec

end A9Native

end ZkFormal.NearV3.Assembly
