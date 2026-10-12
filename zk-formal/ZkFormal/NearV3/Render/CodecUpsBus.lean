import ZkFormal.NearV3.Render.CodecTriePin
import ZkFormal.NearV3.Assembly.TrieUpsSched

/-!
# Codec (table 11) ↔ ups (table 7) buses: `SPLEN`

`value_len`: a block's new state value has `37 + 24·n²` bytes.  **`balancedAt_splen`**: a bundle whose
table 11 is the codec over the `PriorCore` blocks and whose table 7 extends the ups view of `Js`, with
`Js`'s `(τ, v)` the trie side's upsert witnesses `us` (in order) and `us`'s values the blocks' values,
balances `SPLEN`.
-/
namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render.Cdc

theorem value_len (b : NativeBlock) (hb : b.Valid) (i : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) i = .ok b.run) :
    b.witness.value.length = 37 + 24 * (b.run.n * b.run.n) := by
  obtain ⟨so, hs, hval⟩ := hb.1.2
  obtain ⟨prev, p, o, -, hp, hc, ho, -⟩ := schedStep_complete hs
  have h1 := scheduler_core_state_length hc
  have hp' : p = b.pub := Option.some.inj (hp.symm.trans hb.2.2.1)
  subst hp'
  have hn := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  simp only [ProcPreparedSequence.input] at hn
  rw [hn, ← hval, ← ho, ← h1]
  rfl

end ZkFormal.NearV3.Render.CdcGrant

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

theorem covers_splen_send : Covers ZkFormal.NearV3.B_SPLEN true (fun t => t == 11) = true := by decide +kernel
theorem covers_splen_recv : Covers ZkFormal.NearV3.B_SPLEN false (fun t => t == 7) = true := by decide +kernel
theorem pub_splen (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub ZkFormal.NearV3.B_SPLEN s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

/-- Per-index form of the ups link. -/
theorem link_at {Js : List UpsInst} {us : List SchedulerUpsertWitness}
    (hlink : Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)))
    (i : Nat) (hi : i < Js.length) :
    ∃ hu : i < us.length, Js[i].tau = i ∧ Js[i].v = us[i].value.map UInt8.toNat := by
  have hl := congrArg List.length hlink
  simp only [List.length_map, List.length_mapIdx] at hl
  have h := congrArg (fun l => l[i]?) hlink
  simp only [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show i < us.length by omega), Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h
  exact ⟨by omega, h.1, h.2⟩

namespace RenderBundleV3
variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem balancedAt_splen {p : NearSpecV3.Prep} {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub)
    (Js : List UpsInst) (hok : UpsRenderOk Js)
    (hu : ExtOf (R ⟨7, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (us : List SchedulerUpsertWitness)
    (hlink : Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)))
    (hval : us.map (·.value) = bs.map (·.witness.value)) :
    R.BalancedAt ZkFormal.NearV3.B_SPLEN := by
  intro m
  rw [R.sum_tables true _ m _ covers_splen_send, R.sum_tables false _ m _ covers_splen_recv, pub_splen, pub_splen]
  have e7 := R.tf_ext 7 (by decide) hu ZkFormal.NearV3.B_SPLEN (by decide) (by decide) (by decide)
  have hf11 : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf11, hf7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e7.2, sel, ite_true,
    Bool.false_eq_true, ite_false, upsTraffic, Nat.add_zero]
  have hs : (R.tf 11).sends ZkFormal.NearV3.B_SPLEN =
      natMsgs (bs.map fun b => [Fp.ofNat b.run.tau, Fp.ofNat (37 + 24 * (b.run.n * b.run.n))]) := by
    rw [h11]
    unfold rowsTraffic
    dsimp only
    rw [codec_splen_native hc 11 pub]
  rw [hs, TrieUpsSched.view_splen_recv Js hok T_UPS]
  have hl1 := congrArg List.length hlink
  have hl2 := congrArg List.length hval
  simp only [List.length_map, List.length_mapIdx] at hl1 hl2
  unfold cnt
  rw [natMsgs_toFp, List.map_map]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map] at h1 h2
  obtain ⟨hui, ht, hv⟩ := link_at hlink i h2
  have hvi : us[i].value = bs[i].witness.value := by
    have := congrArg (fun l => l[i]?) hval
    simpa [List.getElem?_eq_getElem hui, List.getElem?_eq_getElem h1] using this
  have hbi : bs[i]? = some bs[i] := List.getElem?_eq_getElem h1
  obtain ⟨⟨-, hrun⟩, htau, -⟩ := hc.indexed i bs[i] hbi
  have hlen := value_len bs[i] (hc.valid _ (List.getElem_mem h1)).1 i hrun
  simp only [List.getElem_map, Function.comp_apply, Rcpt.Candidates.NodePostUpdate.reduceMessage_toFp]
  simp only [Msg.toFp, List.map_cons, List.map_nil, UpsGen.L, ht, hv, List.length_map, hvi, hlen, htau]

end RenderBundleV3

theorem map_some_inj {α : Type} : ∀ {l l' : List α}, l.map some = l'.map some → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, map_some_inj h.2]

/-- The trie side's pinned witnesses and the codec blocks have the same new state values. -/
theorem vals_eq {cb wb : NearSpec.Bytes} {A : AcceptedV3 cb wb} {us : List SchedulerUpsertWitness} {p : NearSpecV3.Prep}
    {B : Nat} {bs : List NativeBlock}
    (hpin : CallPin A.k A.m A.steps us) (hus : ∀ u ∈ us, u.Valid) (hc : PriorCore p B bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre))) :
    us.map (·.value) = bs.map (·.witness.value) := by
  have h1 := hpin.values hus
  have h2 := (calls_of_pairs bs hctx).values (by
    intro u hu
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hu
    exact (hc.valid b hb).1.1)
  rw [← h2, List.map_map] at h1
  apply map_some_inj
  rw [List.map_map, List.map_map]
  exact h1

end ZkFormal.NearV3.Assembly
