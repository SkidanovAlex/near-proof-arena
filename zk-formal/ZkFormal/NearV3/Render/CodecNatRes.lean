import ZkFormal.NearV3.Render.CodecGrantCore
import ZkFormal.NearV3.Render.CodecNative
import ZkFormal.NearV3.Candidates.ProcPriorCodecGrantCap
import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardSuccess
import ZkFormal.NearV3.Candidates.ProcCodecCarryPosition
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestLookup

/-!
# `NatRes` from acceptance

`natRes_block`: every block of a `PriorCore` list carrying its distribution witness (`GrantWit`)
satisfies the residual codec premises `NatRes`:
* grants and final grant values: `wfin + gd[k] ≤ 4.5M` (`ProcPriorCodecGrantCap.native`);
* instance-0 forwarding demand: the successful terminal record step of the block's own codec
  generator passed `demand ≤ wfin + gd[k]` (`ProcPriorCodecForwardSuccess.bound`);
* value id: `priorValueId` lies inside the prestate forest's value range (`forest_lookup_offsets`).

`codec_accepted_full`: table 11 from `checkD0a B0` acceptance with no residual premise.
-/
namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open Render.UpsGen Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render.Cdc

theorem vid_lt (l : List PTrie) (i : Nat) (t : PTrie) (hi : l[i]? = some t)
    (hb : preBytes l ≤ 2000000) : priorValueId (l.take i) t < ZkFormal.Algebra.P := by
  have hil : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have ht : l[i] = t := (List.getElem?_eq_some_iff.mp hi).2
  have hl : l = l.take i ++ t :: l.drop (i+1) := by
    conv => lhs; rw [← List.take_append_drop i l]
    rw [← ht, List.getElem_cons_drop]
  rw [hl] at hb
  have hf := (forest_lookup_offsets (l.take i) (l.drop (i+1)) t hb).2
  cases hv : valueIndex t keyBwState with
  | none => simp only [priorValueId, hv]; unfold ZkFormal.Algebra.P; omega
  | some j =>
    have := valueIndex_bound hv
    rw [native_valsOf_eq] at this
    simp only [priorValueId, hv]
    omega

theorem natRes_block {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {B : Nat} (hB : B ≤ 2000000) {bs : List NativeBlock} (hc : PriorCore p B bs)
    (b : NativeBlock) (hm : b ∈ bs) (hg : GrantWit b) : NatRes b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨⟨hsch, hr⟩, htau, hvid⟩ := hc.indexed i b hi
  have hval := (hc.valid b hm).1
  have hs := prepD0_sched hp b.pub (List.mem_of_getElem? hsch)
  have ha := (ProcActualPublic.schedPub_fields b.witness.ctx b.pub hval.2.2.1).1
  obtain ⟨cv, st, rs, ev, sord, rord, hprefix, hgd⟩ := hg
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  have hcap : ∀ kk < b.run.n * b.run.n, (b.run.segs.getD kk default).wfin + b.grants[kk]! ≤ 4500000 := by
    intro kk hk
    rw [hn] at hk
    exact ProcPriorCodecGrantCap.native b.pub hs ha b.old i cv rs st ev b.run b.grants sord rord
      hprefix hr hgd kk hk
  refine ⟨?_, fun kk hk => ?_, fun kk hk => ?_, fun ht0 kk hk => ?_⟩
  · rw [hvid]
    have hpre : (bs.map (fun b => b.witness.pre))[i]? = some b.witness.pre := by
      rw [List.getElem?_map, hi]; rfl
    exact vid_lt _ i _ hpre (Nat.le_trans hc.forest hB)
  · have := hcap kk hk; omega
  · have := hcap kk hk; omega
  · have hgen := hval.2.2.2.2
    rw [← coreLayout_eq] at hgen
    cases hcl : coreLayout (ProcPreparedSequence.input b.pub b.old) b.run b.prior.isSome b.vid
        b.grants b.forwarded with
    | error e => rw [hcl] at hgen; cases hgen
    | ok o =>
      obtain ⟨before, after, _, _, hstep, _⟩ :=
        ProcCodecCarryPosition.core _ b.run b.prior.isSome b.vid b.grants b.forwarded o hcl kk 2 7 hk
          (by decide) (by decide)
      have hf := ProcPriorCodecForwardSuccess.bound _ b.run b.prior.isSome b.grants b.forwarded _ kk
        before after ht0 hstep
      unfold ProcPriorCodecRecordTotal.Forward at hf
      have := hcap kk hk
      unfold demand
      omega

/-- **Table 11 from acceptance, no residual premise.** -/
theorem codec_accepted_full {cb wb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {k : WalkD0} {w : StateWitness} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B0 cb wb = .ok ()) (pub : List Fp) :
    ∃ bs : List NativeBlock, PriorCore p B0 bs ∧ (∀ b ∈ bs, GrantWit b) ∧ (∀ b ∈ bs, NatRes b) ∧
      ∃ R : TableRenderV3 pub 11 (by decide), R.tr = codecTrace (allDescs (bs.map blkOf)) ∧
        R.tf = rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub := by
  obtain ⟨bs, hc, hg⟩ := accepted_prior_core_grants hp hk hw h (by decide)
  have hres : ∀ b ∈ bs, NatRes b := fun b hb => natRes_block hp (by decide) hc b hb (hg b hb)
  refine ⟨bs, hc, hg, hres, ?_⟩
  have hok : ∀ B ∈ bs.map blkOf, B.Ok := by
    intro B hB
    simp only [List.mem_map] at hB
    obtain ⟨b, hb, rfl⟩ := hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨⟨hsch, hrun⟩, _, _⟩ := hc.indexed i b hi
    have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
    exact blkOf_ok b (hc.valid b hb).2 i (by have := hc.length; omega) hrun
      (prepD0_sched hp b.pub (List.mem_of_getElem? hsch)) (hres b hb)
  have hcap : (allDescs (bs.map blkOf)).length < 2 ^ 22 := by
    have := blocks_length bs (fun b hb => (hc.valid b hb).2)
    have := hc.length
    omega
  exact ⟨codecRenderV3 pub (bs.map blkOf) hok hcap, rfl, rfl⟩

end ZkFormal.NearV3.Render.CdcGrant
