import ZkFormal.NearV3.Render.CodecUpsBus
import ZkFormal.NearV3.Assembly.UpsS0FRebase

/-!
# Codec (table 11) ↔ ups (table 7): `S0F`

The codec receives one `S0F (τ, pres, vid)` per block (`codec_s0f_native`: `pres = [prior present]`,
`vid = priorValueId` of the block's pre tree over the native forest prefix); the ups table sends one
per instance (`view_s0f_send`: `(presN, vidN) = s0fOf`).  `s0fPair_read`: the codec's payload is the
`s0fPair` of the block's pre tree.  **`balancedAt_s0f`**: with the trie side's
`Js.map s0fOf = F.mapIdx (s0fPair (F.take i))` for the codec blocks' pre forest `F`, `S0F` balances.
-/
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

theorem covers_s0f_send : Covers ZkFormal.NearV3.B_S0F true (fun t => t == 7) = true := by decide +kernel
theorem covers_s0f_recv : Covers ZkFormal.NearV3.B_S0F false (fun t => t == 11) = true := by decide +kernel
theorem pub_s0f (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub ZkFormal.NearV3.B_S0F s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

/-- The codec's `S0F` payload of a block whose pre tree reads `prior` is the tree's `s0fPair`. -/
theorem s0fPair_read {before : List NearSpec.PTrie} {pre : NearSpec.PTrie} {prior : Option NearSpec.Bytes}
    {what : String} (hr : NearSpecV3.readKey pre NearSpecV3.keyBwState what = .ok prior) :
    UpsS0F.s0fPair before pre = (if prior.isSome then 1 else 0, priorValueId before pre) := by
  unfold NearSpecV3.readKey at hr
  cases hf : pre.find NearSpecV3.keyBwState with
  | none => simp [hf] at hr
  | some x =>
    simp only [hf, Except.ok.injEq] at hr
    subst hr
    cases x with
    | none =>
      have h0 := CodecDigest.absent before pre (by simp [NearSpecV3.readKey, hf])
      simp [UpsS0F.s0fPair, hf, h0]
    | some b => simp [UpsS0F.s0fPair, hf]

namespace RenderBundleV3
variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem balancedAt_s0f {p : NearSpecV3.Prep} {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub)
    (Js : List UpsInst) (hok : UpsRenderOk Js)
    (hu : ExtOf (R ⟨7, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (us : List SchedulerUpsertWitness)
    (hlink : Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)))
    (F : List NearSpec.PTrie) (hF : bs.map (·.witness.pre) = F)
    (hs0 : Js.map UpsS0F.s0fOf = F.mapIdx (fun i t => UpsS0F.s0fPair (F.take i) t)) :
    R.BalancedAt ZkFormal.NearV3.B_S0F := by
  intro m
  rw [R.sum_tables true _ m _ covers_s0f_send, R.sum_tables false _ m _ covers_s0f_recv, pub_s0f, pub_s0f]
  have e7 := R.tf_ext 7 (by decide) hu ZkFormal.NearV3.B_S0F (by decide) (by decide) (by decide)
  have hf11 : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf11, hf7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e7.1, sel, ite_true,
    Bool.false_eq_true, ite_false, upsTraffic, Nat.add_zero]
  have hs : (R.tf 11).recvs ZkFormal.NearV3.B_S0F =
      natMsgs (bs.map fun b => [Fp.ofNat b.run.tau, Fp.ofNat (Sched.Gen.b2n b.prior.isSome), Fp.ofNat b.vid]) := by
    rw [h11]
    unfold rowsTraffic
    dsimp only
    rw [codec_s0f_native hc 11 pub]
  rw [hs, TrieUpsSched.view_s0f_send Js hok T_UPS]
  have hl1 := congrArg List.length hlink
  have hl3 := congrArg List.length hs0
  have hl4 := congrArg List.length hF
  simp only [List.length_map, List.length_mapIdx] at hl1 hl3 hl4
  unfold cnt
  rw [natMsgs_toFp, List.map_map]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map] at h1 h2
  obtain ⟨hui, ht, -⟩ := link_at hlink i h1
  have hbi : bs[i]? = some bs[i] := List.getElem?_eq_getElem h2
  obtain ⟨-, htau, hvid⟩ := hc.indexed i bs[i] hbi
  have hrd := (hc.valid _ (List.getElem_mem h2)).1.2.1
  have hJ := congrArg (fun l => l[i]?) hs0
  simp only [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem (show i < F.length by omega), Option.map_some, Option.some.injEq] at hJ
  have hFi : F[i] = bs[i].witness.pre := by subst hF; simp
  have hFt : F.take i = (bs.map (·.witness.pre)).take i := by rw [hF]
  rw [hFi, hFt, s0fPair_read hrd, ← hvid] at hJ
  have hp : TrieUpsSched.presN Js[i] = Sched.Gen.b2n bs[i].prior.isSome := by
    have := congrArg Prod.fst hJ
    simp only [UpsS0F.s0fOf] at this
    simp only [TrieUpsSched.presN, Sched.Gen.b2n, this]
  have hd : TrieUpsSched.vidN Js[i] = bs[i].vid := by
    have := congrArg Prod.snd hJ
    simp only [UpsS0F.s0fOf] at this
    simp only [TrieUpsSched.vidN, this]
  simp only [List.getElem_map, Function.comp_apply, Rcpt.Candidates.NodePostUpdate.reduceMessage_toFp]
  simp only [Msg.toFp, List.map_cons, List.map_nil, ht, hp, hd, htau]

end RenderBundleV3
end ZkFormal.NearV3.Assembly
