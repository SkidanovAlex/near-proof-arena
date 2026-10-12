import ZkFormal.NearV3.Render.CodecTriePin
import ZkFormal.NearV3.Render.CodecAllow
import ZkFormal.NearV3.Assembly.CanonicalReplay

/-!
# Canonical priors of the codec blocks (acceptance check `canon0f`)

`single_find`: a key's read on a multi-key partial trie equals its read on the single-key one.
`reads_trace`: the `0x0f` reads of the accepted witness are the native trace's state reads (main pre-trie,
then each implicit pre-trie).  **`prior_canonical`**: every `PriorCore` block on `A`'s trace with a present
prior has the layout's link pairs `ids × ids` — the premise of `CdcAllow.allowances_canon`/`a0s_canon`.
-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem single_find (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (key : List Nat)
    (hr : root.length = 32) (hk : (partialTrie ws root keys).find key ≠ none) :
    (partialTrie ws root [key]).find key = (partialTrie ws root keys).find key := by
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

end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest

theorem implicit_reads {k : WalkD0} {root : Bytes} {pairs : List (NearSpecV3.Blk × Transition)}
    {steps : List ImplicitStepV3} {last : Bytes} (h : ImplicitTraceValid k root pairs steps last) :
    bwReadsFrom root (pairs.map Prod.snd) = steps.map fun e => bwRead e.witness.values e.root := by
  induction h with
  | nil => rfl
  | cons root b t rest steps post last hrun hpost htail ih =>
    simp only [List.map_cons, bwReadsFrom, ← hpost, ih]

theorem implicit_found {k : WalkD0} {root : Bytes} {pairs : List (NearSpecV3.Blk × Transition)}
    {steps : List ImplicitStepV3} {last : Bytes} (h : ImplicitTraceValid k root pairs steps last) :
    ∀ e ∈ steps, e.pre.find keyBwState ≠ none := by
  induction h with
  | nil => intro e he; simp at he
  | cons root b t rest steps post last hrun hpost htail ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact applyMissingChunk_bw_find hrun
    · exact ih e he

/-- The `0x0f` reads of the accepted witness are the native trace's state reads. -/
theorem reads_trace {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    reads0f A.k A.w = (A.m.pre.find keyBwState).getD none ::
      A.steps.map (fun e => (e.pre.find keyBwState).getD none) := by
  have hc : checkD0 cb wb = .ok () := by
    have hh := ((relD0a_iff B0 cb wb).mpr A.h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨-, -, -, -, hcount, -⟩ := checkD0_native_steps A.hk A.hw hc
  rw [reads0f_eq]
  congr 1
  · unfold bwRead
    have hpre := A.hm.pre
    rw [single_find _ _ _ _ A.hm.root_length (by rw [← hpre]; exact applyNewChunk_bw_find A.hm.run), ← hpre]
  · rw [← A.hm.postRoot]
    have hz : (A.k.implicitBlks.zip A.w.implicit).map Prod.snd = A.w.implicit :=
      List.map_snd_zip (by omega)
    rw [← hz, implicit_reads A.hv]
    apply List.map_congr_left
    intro e he
    obtain ⟨hp, hr, -⟩ := A.hv.input_facts e he
    unfold bwRead
    rw [single_find _ _ _ _ hr (by rw [← hp]; exact implicit_found A.hv e he), ← hp]

/-- **Canonical priors**: every `PriorCore` block on `A`'s trace with a present prior has the layout's
link pairs (`canon0f`), in the form `CdcAllow.allowances_canon` takes. -/
theorem prior_canonical {cb wb : Bytes} (A : AcceptedV3 cb wb) {p : Prep} {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore p B bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre))) :
    ∀ b ∈ bs, b.prior.isSome = true →
      b.old.links.map (fun la => (la.sender, la.receiver)) = b.pub.ids.flatMap fun s => b.pub.ids.map fun r => (s, r) := by
  intro b hb hpres
  have hval := (hc.valid b hb).1
  have canon : (reads0f A.k A.w).all (canonical0f A.k.L) = true := by
    have hr := (relD0a_iff B0 cb wb).mpr A.h
    simpa only [canon0f, A.hk, A.hw] using hr.2.2.2.1
  rw [reads_trace] at canon
  have hmem : (b.witness.ctx, b.witness.pre) ∈
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) := by
    rw [← hctx]; exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hfind : b.witness.pre.find keyBwState = some b.prior := by
    have h1 := hval.2.1
    unfold readKey at h1
    split at h1 <;> simp_all
  -- the read is canonical, the layout is `A.k.L`
  have hcan : canonical0f A.k.L b.prior = true ∧ b.witness.ctx.layout = A.k.L := by
    rcases List.mem_cons.mp hmem with h0 | h0
    · simp only [Prod.mk.injEq] at h0
      have hc0 := (List.all_eq_true.mp canon) _ List.mem_cons_self
      rw [← h0.2, hfind] at hc0
      exact ⟨hc0, by rw [h0.1]; rfl⟩
    · obtain ⟨e, he, hee⟩ := List.mem_map.mp h0
      simp only [Prod.mk.injEq] at hee
      have hc0 := (List.all_eq_true.mp canon) _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩))
      rw [hee.2, hfind] at hc0
      exact ⟨hc0, by rw [← hee.1]; rfl⟩
  obtain ⟨hcan, hlay⟩ := hcan
  have hids : b.pub.ids = A.k.L.shardIds := by
    rw [ZkFormal.NearV3.Sched.schedPub_ids hval.2.2.1, hlay]
  cases hq : b.prior with
  | none => simp [hq] at hpres
  | some v =>
    have hd := hval.2.2.2.1
    rw [hq] at hd hcan
    simp only [canonical0f, hd, beq_iff_eq] at hcan
    rw [hcan, hids]
    rfl

/-- **The frozen codec's prior allowances are the repaired process allowances** on every block of `A`'s
trace (present priors; absent ones have `a0s = 0` and empty process allowances input). -/
theorem a0s_accepted {cb wb : Bytes} (A : AcceptedV3 cb wb) {p : Prep} {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore p B bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre))) :
    ∀ b ∈ bs, b.prior.isSome = true → ∀ kk < b.pub.ids.length * b.pub.ids.length,
      ((Render.Cdc.blkOf b).recs kk).a0s = (ProcActualInput.allowances b.pub.ids b.old)[kk]! := by
  intro b hb hpres kk hk
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨-, hr⟩, -, -⟩ := hc.indexed i b hi
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  exact CdcAllow.a0s_canon b hpres (prior_canonical A hc hctx b hb hpres) hn kk hk

end ZkFormal.NearV3.Render.CdcGrant
