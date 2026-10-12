import ZkFormal.NearV3.Render.CodecUpsBus
import ZkFormal.NearV3.Render.CodecS0F
import ZkFormal.NearV3.Candidates.ProcActualOutputAgreement
import ZkFormal.NearV3.Candidates.ProcActualStateAgreement
import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
import ZkFormal.NearV3.Extract.Ups.PartBytes

/-!
# Codec `SPOST` closed form

`spT`/`rt_spost`: the per-row `SPOST` sends; `posMsgs τ off L`: the messages `[τ, off + i, L[i]]`;
**`blk_spost`**: a block's `SPOST` sends are `posMsgs τ 0 (stateBytes ids afin dig)` (header bytes, the
24-byte records, the digest), under `N = n²`, `N < 65536`, `afin < 2^24`, `|dig| = 32`.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec

def spT : Desc → List (List Fp)
  | .hdr I p => [[Fp.ofNat I.tv, Fp.ofNat p, Fp.ofNat ((hdrBytes I).getD p 0)]]
  | .record I R f gg bpo _ _ _ _ => [[Fp.ofNat I.tv, Fp.ofNat (5 + 24 * R.kk + 8 * f + gg), Fp.ofNat bpo]]
  | .hash I dig _ j => [[Fp.ofNat I.tv, Fp.ofNat (5 + 24 * I.N + j), Fp.ofNat (dig.getD j 0)]]
  | .ash .. => []

theorem rt_spost (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPOST true = spT d := by
  cases d <;> simp only [spT, spost_hdr, spost_rec, spost_hash, spost_ash]

def posMsgs (tv off : Nat) (L : List Nat) : List (List Fp) :=
  (List.range L.length).map fun i => [Fp.ofNat tv, Fp.ofNat (off + i), Fp.ofNat (L.getD i 0)]

theorem posMsgs_append (tv off : Nat) (A B : List Nat) :
    posMsgs tv off (A ++ B) = posMsgs tv off A ++ posMsgs tv (off + A.length) B := by
  unfold posMsgs
  rw [List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [ZkFormal.Sha.Complete.getD_append_left' _ _ _ (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [ZkFormal.Sha.Complete.getD_append_right' _ _ _ (by omega), Nat.add_sub_cancel_left, Nat.add_assoc]

theorem posMsgs_flat (tv off m : Nat) (F : Nat → List Nat) (hF : ∀ k, (F k).length = m) :
    ∀ N, posMsgs tv off ((List.range N).flatMap F) =
      (List.range N).flatMap fun k => posMsgs tv (off + m * k) (F k)
  | 0 => rfl
  | N + 1 => by
    have hl : ∀ N, ((List.range N).flatMap F).length = m * N := by
      intro N
      induction N with
      | zero => rfl
      | succ N ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hF, Nat.mul_succ]
    have hl := hl N
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, posMsgs_append, posMsgs_flat tv off m F hF N, hl]
    simp

theorem div_big (a g : Nat) (ha : a < 2 ^ 24) (hg : 3 ≤ g) : a / 256 ^ g % 256 = 0 := by
  have : 256 ^ 3 ≤ 256 ^ g := Nat.pow_le_pow_right (by decide) hg
  rw [Nat.div_eq_of_lt (by omega)]

theorem hdr_part (I : Inst) (hN : I.N < 65536) :
    ((List.range 5).map (Desc.hdr I)).flatMap spT = posMsgs I.tv 0 ([0] ++ bytesLE I.N 4) := by
  have h1 : I.N / 256 ^ 2 = 0 := Nat.div_eq_of_lt (by simpa using hN)
  have h2 : I.N / 256 ^ 3 = 0 := Nat.div_eq_of_lt (by have : (256:Nat) ^ 3 = 16777216 := rfl; omega)
  simp [posMsgs, spT, hdrBytes, bytesLE, List.range_succ, h1, h2]

theorem rec_part (B : Blk) (kk : Nat) (hk : (B.recs kk).kk = kk) (ha : (B.recs kk).afin < 2 ^ 24) :
    (B.recordDescs kk).flatMap spT = posMsgs B.I.tv (5 + 24 * kk)
      (bytesLE (B.ids.getD (kk / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (kk % B.ids.length) 0) 8 ++
        bytesLE (B.recs kk).afin 8) := by
  have dz : ∀ g, 3 ≤ g → (B.recs kk).afin / 256 ^ g = 0 := fun g hg =>
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by simpa using ha) (Nat.pow_le_pow_right (by decide) hg))
  have d3 := dz 3 (by decide)
  have d4 := dz 4 (by decide)
  have d5 := dz 5 (by decide)
  have d6 := dz 6 (by decide)
  have d7 := dz 7 (by decide)
  simp only [Blk.recordDescs, Blk.fieldDescs, Blk.recD, List.flatMap_append, List.flatMap_map, spT, hk,
    posMsgs, bytesLE, List.length_append, List.length_map, List.length_range, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.append_nil]
  have r24 : List.range 24 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := rfl
  simp [Blk.bpo, idByte, d3, d4, d5, d6, d7, List.getD_eq_getElem?_getD, Nat.add_assoc, r24]

theorem hash_part (I : Inst) (dig hpre : List Nat) (hd : dig.length = 32) :
    ((List.range 32).map (Desc.hash I dig hpre)).flatMap spT = posMsgs I.tv (5 + 24 * I.N) dig := by
  simp only [List.flatMap_map, spT, posMsgs, hd]
  induction (List.range 32) <;> simp_all

theorem flatten_flatMap {α β : Type} (L : List Nat) (f : Nat → List α) (g : α → List β) :
    (L.map f).flatten.flatMap g = L.flatMap fun x => (f x).flatMap g := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [List.flatMap_append, ih]

theorem blk_spost (B : Blk) (hOk : B.Ok) (hN : B.I.N = B.ids.length * B.ids.length) (hd : B.dig.length = 32) :
    B.descs.flatMap spT = posMsgs B.I.tv 0 (stateBytes B.ids (fun k => (B.recs k).afin) B.dig) := by
  have hN6 : B.I.N < 65536 := hOk.inst.2.1
  have hF : ∀ k, (bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++
      bytesLE (B.recs k).afin 8).length = 24 := fun k => by simp [bytesLE]
  have hX : ((List.range (B.ids.length * B.ids.length)).flatMap fun k =>
      bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++
        bytesLE (B.recs k).afin 8).length = 24 * (B.ids.length * B.ids.length) := by
    rw [List.length_flatMap]
    have : ∀ L : List Nat, (L.map fun k => (bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++
        bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++ bytesLE (B.recs k).afin 8).length).sum = 24 * L.length := by
      intro L; induction L with
      | nil => rfl
      | cons x L ih => rw [List.map_cons, List.sum_cons, ih, hF, List.length_cons]; omega
    exact (this _).trans (by rw [List.length_range])
  unfold Blk.descs stateBytes
  simp only [List.flatMap_append]
  have hash0 : ((List.range 32).map (Desc.ash B.I B.ash)).flatMap spT = [] := by
    simp [spT]
  rw [hash0, List.append_nil, hdr_part B.I hN6, hash_part B.I B.dig B.hpre hd, Blk.records, flatten_flatMap]
  conv => rhs; rw [posMsgs_append, posMsgs_append, posMsgs_flat _ _ 24 _ hF]
  have hb4 : (bytesLE (B.ids.length * B.ids.length) 4).length = 4 := by simp [bytesLE]
  simp only [List.length_append, hX, hb4, List.length_cons, List.length_nil]
  rw [← hN]
  congr 1
  · congr 1
    apply flatMap_congr_rt
    intro kk hkk
    have hk := List.mem_range.mp hkk
    rw [rec_part B kk (hOk.kk kk hk) (hOk.afin kk hk)]
  · congr 1
    omega

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render.Cdc

theorem concat_encode (ls : List Bandwidth.LinkAllowance) :
    (concatAll (ls.map Bandwidth.LinkAllowance.encode)).map UInt8.toNat =
      ls.flatMap fun la => bytesLE la.sender 8 ++ bytesLE la.receiver 8 ++ bytesLE la.allowance 8 := by
  induction ls with
  | nil => rfl
  | cons la ls ih =>
    simp only [List.map_cons, concatAll, List.map_append, ih, List.flatMap_cons, Bandwidth.LinkAllowance.encode,
      u64, UpsRows.toNats_leN, bytesLE]

theorem encode_bytes (st : Bandwidth.State) :
    st.encode.map UInt8.toNat = [0] ++ bytesLE st.links.length 4 ++
      st.links.flatMap (fun la => bytesLE la.sender 8 ++ bytesLE la.receiver 8 ++ bytesLE la.allowance 8) ++
      st.sanityHash.map UInt8.toNat := by
  simp only [Bandwidth.State.encode, List.map_append, concat_encode, u32, UpsRows.toNats_leN, bytesLE]
  rfl

/-- **The block's new state value is the codec's post bytes.** -/
theorem value_stateBytes {cb : Bytes} {hint : Hint} {p : Prep} {B : Nat} {bs : List NativeBlock} (hp : prepD0 cb hint = .ok p)
    (hc : PriorCore p B bs) (b : NativeBlock) (hb : b ∈ bs) (hg : GrantWit b) :
    b.witness.value.map UInt8.toNat =
      stateBytes (blkOf b).ids (fun k => ((blkOf b).recs k).afin) (blkOf b).dig := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨hsch, hr⟩, -, -⟩ := hc.indexed i b hi
  have hval := (hc.valid b hb).1
  have hs := prepD0_sched hp b.pub (List.mem_of_getElem? hsch)
  have ha := (ProcActualPublic.schedPub_fields b.witness.ctx b.pub hval.2.2.1).1
  obtain ⟨cv, st, rs, ev, sord, rord, hprefix, hgd⟩ := hg
  obtain ⟨-, hproc⟩ := ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix
  -- the native output
  obtain ⟨so, hss, hsv⟩ := hval.1.2
  obtain ⟨prior, p', o, hread, hp', hcore, ho, -⟩ := schedStep_complete hss
  have hp'' : p' = b.pub := Option.some.inj (hp'.symm.trans hval.2.2.1)
  subst hp''
  have hprior : prior = b.prior := by
    have h1 := hval.2.1
    rw [hread] at h1
    exact Except.ok.inj h1
  subst hprior
  obtain ⟨prev, ev', hdec, hce, hst⟩ :=
    ProcActualOutputAgreement.scheduled_output_exists b.witness.ctx b.pub hs hval.2.2.1 _ o hcore
  have hprev : prev = b.old := by
    have h2 := hval.2.2.2.1
    unfold ProcActualCore.decodePrevious at hdec
    cases hq : b.prior <;> simp only [hq] at h2 hdec <;> exact Option.some.inj (hdec.symm.trans h2)
  subst hprev
  have hcs := ProcActualStateAgreement.core_state b.pub b.old st rs ev' hproc hce
  -- the value
  have hv : b.witness.value = (ProcActualNativeResult.finish b.pub b.old (ProcNativeGrant.native st)).state := by
    rw [← hsv, ← ho]; show o.state = _; rw [← hst.1, hcs]
  rw [hv]
  unfold ProcActualNativeResult.finish
  simp only [ProcActualStateAgreement.distribute_allowance]
  rw [encode_bytes]
  have hdig : (sha256 (b.old.sanityHash ++ b.pub.allShardsHash)).map UInt8.toNat = (blkOf b).dig := by
    simp only [blkOf]
    congr 2
    rw [List.map_append]
    unfold hpreOf
    split
    · rename_i hq
      rw [UpsRows.map_ofNat_toNat, UpsRows.map_ofNat_toNat]; rfl
    · rename_i hq
      have h2 := hval.2.2.2.1
      cases hpr : b.prior with
      | some _ => simp [hpr] at hq
      | none =>
        rw [hpr] at h2
        simp only [Option.some.injEq] at h2
        rw [← h2, UpsRows.map_ofNat_toNat]; rfl
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  unfold stateBytes
  simp only [List.length_map, List.length_range, List.flatMap_map, hdig]
  congr 2
  apply flatMap_congr_rt
  intro k hk
  have hk' := List.mem_range.mp hk
  have hf := (ProcActualMemoryFinal.run_link_final b.pub hs b.old i cv rs st ev b.run k hk' hprefix hr).1
  simp only [blkOf, hf]
  rfl

theorem codec_spost_native {cb : Bytes} {hint : Hint} {p : Prep} {B : Nat} {bs : List NativeBlock}
    (hp : prepD0 cb hint = .ok p) (hc : PriorCore p B bs) (hg : ∀ b ∈ bs, GrantWit b)
    (hres : ∀ b ∈ bs, NatRes b) (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub B_SPOST true =
      bs.flatMap fun b => posMsgs b.run.tau 0 (b.witness.value.map UInt8.toNat) := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ spT (rt_spost · · t pub), List.flatMap_map]
  apply flatMap_congr_rt
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨hsch, hr⟩, _, _⟩ := hc.indexed i b hi
  have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hok := blkOf_ok b (hc.valid b hb).2 i (by have := hc.length; omega) hr
    (prepD0_sched hp b.pub (List.mem_of_getElem? hsch)) (hres b hb)
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  rw [blk_spost (blkOf b) hok (by simp only [blkOf, hn]; rfl) (by simp [blkOf]),
    value_stateBytes hp hc b hb (hg b hb)]
  rfl

end ZkFormal.NearV3.Render.CdcGrant

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

theorem covers_spost_send : Covers ZkFormal.NearV3.B_SPOST true (fun t => t == 11) = true := by decide +kernel
theorem covers_spost_recv : Covers ZkFormal.NearV3.B_SPOST false (fun t => t == 7) = true := by decide +kernel
theorem pub_spost (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub ZkFormal.NearV3.B_SPOST s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

/-- The blocks' `(τ, value)` are the pinned witnesses' in order. -/
theorem blocks_pairs {p : NearSpecV3.Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    {us : List SchedulerUpsertWitness} (hval : us.map (·.value) = bs.map (·.witness.value)) :
    bs.map (fun b => (b.run.tau, b.witness.value.map UInt8.toNat)) =
      us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)) := by
  have hl := congrArg List.length hval
  simp only [List.length_map] at hl
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.length_map] at h1
  have hvi : us[i].value = bs[i].witness.value := by
    have := congrArg (fun l => l[i]?) hval
    simpa [List.getElem?_eq_getElem (show i < us.length by omega), List.getElem?_eq_getElem h1] using this
  obtain ⟨-, htau, -⟩ := hc.indexed i bs[i] (List.getElem?_eq_getElem h1)
  simp [htau, hvi]

namespace RenderBundleV3
variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem balancedAt_spost {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep} {B : Nat}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) (bs : List NativeBlock) (hc : PriorCore p B bs)
    (hg : ∀ b ∈ bs, GrantWit b) (hres : ∀ b ∈ bs, NatRes b)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub)
    (Js : List UpsInst) (hok : UpsRenderOk Js)
    (hu : ExtOf (R ⟨7, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (us : List SchedulerUpsertWitness)
    (hlink : Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)))
    (hval : us.map (·.value) = bs.map (·.witness.value)) :
    R.BalancedAt ZkFormal.NearV3.B_SPOST := by
  intro m
  rw [R.sum_tables true _ m _ covers_spost_send, R.sum_tables false _ m _ covers_spost_recv, pub_spost, pub_spost]
  have e7 := R.tf_ext 7 (by decide) hu ZkFormal.NearV3.B_SPOST (by decide) (by decide) (by decide)
  have hf11 : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf11, hf7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e7.2, sel, ite_true,
    Bool.false_eq_true, ite_false, upsTraffic, Nat.add_zero]
  have hs : (R.tf 11).sends ZkFormal.NearV3.B_SPOST =
      natMsgs (bs.flatMap fun b => posMsgs b.run.tau 0 (b.witness.value.map UInt8.toNat)) := by
    rw [h11]
    unfold rowsTraffic
    dsimp only
    rw [codec_spost_native hp hc hg hres 11 pub]
  rw [hs, TrieUpsSched.view_spost_recv Js hok T_UPS]
  unfold cnt
  rw [natMsgs_toFp]
  congr 1
  have hq : ∀ (L : List (Nat × List Nat)), L.flatMap (fun q => posMsgs q.1 0 q.2) =
      (L.flatMap fun q => (List.range q.2.length).map fun p =>
        Rcpt.Candidates.NodePostUpdate.reduceMessage [q.1, p, q.2.getD p 0]).map Msg.toFp := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
      congr 1
      simp only [posMsgs, List.map_map]
      apply List.map_congr_left
      intro x _
      simp only [Function.comp_apply, Rcpt.Candidates.NodePostUpdate.reduceMessage_toFp]
      simp [Msg.toFp]
  have e1 := hq (bs.map fun b => (b.run.tau, b.witness.value.map UInt8.toNat))
  have e2 := hq (Js.map fun I => (I.tau, I.v))
  rw [List.flatMap_map] at e1 e2
  rw [e1]
  simp only [List.flatMap_map] at e2
  rw [blocks_pairs hc hval, ← hlink, List.flatMap_map]
  rfl

end RenderBundleV3
end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.Assembly.RcptTrieSide
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate RcptSkeleton RcptBal ZkFormal.NearV3.UnfoldA7 TrieA7
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

/-- `rcpt_trie_codec` plus the codec ↔ ups buses `SPLEN`, `SPOST`, `S0F`. -/
theorem rcpt_trie_sched {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (hovh : TrieSide.SizeBudget A) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide))
      (r11 : TableRenderV3 A.pub 11 (by decide)) (bs : List NativeBlock),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
      CallPin A.k A.m A.steps us ∧
      (∃ (Js : List UpsInst) (hok : UpsRenderOk Js), r7 = upsRenderV3 A.pub Js hok ∧
        ExtOf r7.tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))) ∧
        Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)) ∧
        Js.map Assembly.UpsS0F.s0fOf = (A.m.pre :: A.steps.map ImplicitStepV3.pre).mapIdx
          (fun i t => Assembly.UpsS0F.s0fPair ((A.m.pre :: A.steps.map ImplicitStepV3.pre).take i) t)) ∧ PriorCore A.p NearSpecV3.B0 bs ∧ (∀ b ∈ bs, GrantWit b) ∧ (∀ b ∈ bs, NatRes b) ∧
      bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
        (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) ∧
      r11.tr = codecTrace (allDescs (bs.map blkOf)) ∧
      r11.tf = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨0, by decide⟩ = r0 → R ⟨1, by decide⟩ = r1 → R ⟨2, by decide⟩ = r2 → R ⟨3, by decide⟩ = r3 →
        R ⟨4, by decide⟩ = r4 → R ⟨5, by decide⟩ = r5 → R ⟨6, by decide⟩ = r6 → R ⟨7, by decide⟩ = r7 →
        R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨17, by decide⟩ = A.rcptRenders.acct →
        R ⟨18, by decide⟩ = A.rcptRenders.akey → R ⟨19, by decide⟩ = A.rcptRenders.bnd →
        R ⟨20, by decide⟩ = A.rcptRenders.srcp → R ⟨21, by decide⟩ = r21 →
        R ⟨22, by decide⟩ = A.rcptRenders.qv → R ⟨23, by decide⟩ = A.mrkAcc →
        R ⟨11, by decide⟩ = r11 →
        R.tf 24 = sortTraffic (Candidates.NativeSortIds.input (A.rcptInput.lists.flatten.map Input.receipt)) →
        ((-- receipt-side buses
        (BusBalanced R B_SREC ∧ BusBalanced R B_RCL ∧ BusBalanced R B_AKC ∧ BusBalanced R B_RIDS ∧
          BusBalanced R B_MEM ∧ BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC ∧
          BusBalanced R B_QSH ∧ BusBalanced R B_SRC ∧ BusBalanced R B_BNDP ∧ BusBalanced R B_BND) ∧
        -- trie-side buses
        (R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧ R.BalancedAt B_DIGS ∧
          R.BalancedAt B_DUP ∧ R.BalancedAt B_EDGE ∧ R.BalancedAt B_BMAP ∧ R.BalancedAt B_MIDROOT ∧
          R.BalancedAt B_ROOT ∧ R.BalancedAt B_UPB ∧ R.BalancedAt B_MEMD ∧ R.BalancedAt B_RPL ∧
          R.BalancedAt B_RPLV) ∧
        -- shared buses
        R.BalancedAt B_SIZE ∧ R.BalancedAt B_VSLOT ∧ R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL ∧
        R.BalancedAt B_BYTES ∧ R.BalancedAt B_DIGEST) ∧
        R.BalancedAt ZkFormal.NearV3.B_SPLEN ∧ R.BalancedAt ZkFormal.NearV3.B_SPOST ∧
        R.BalancedAt ZkFormal.NearV3.B_S0F) := by
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hc, hg, hres,
    hctx, htr, htf, hall⟩ := rcpt_trie_codec A hovh
  refine ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hc, hg, hres,
    hctx, htr, htf, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 e11 h24
  refine ⟨hall R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 e11 h24, ?_⟩
  obtain ⟨Js, hok, hr7, hext, hlink, hs0⟩ := hups
  have hu : ExtOf (R ⟨7, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))) := by
    rw [e7, hr7] at *; exact hext
  have h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub := by
    rw [bundle_tf_eq R 11 _ e11, htf]
  have hv := vals_eq hpin hus hc hctx
  have hF : bs.map (·.witness.pre) = A.m.pre :: A.steps.map ImplicitStepV3.pre := by
    have h := congrArg (List.map Prod.snd) hctx
    simpa [List.map_map, Function.comp_def] using h
  exact ⟨R.balancedAt_splen bs hc h11 Js hok hu us hlink hv,
    R.balancedAt_spost A.hp bs hc hg hres h11 Js hok hu us hlink hv,
    R.balancedAt_s0f bs hc h11 Js hok hu us hlink _ hF hs0⟩

end ZkFormal.NearV3.Assembly.RcptTrieSide
