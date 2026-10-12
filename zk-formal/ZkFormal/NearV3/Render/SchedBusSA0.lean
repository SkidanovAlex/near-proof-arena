import ZkFormal.NearV3.Render.SchedBusCodecBlk
import ZkFormal.NearV3.Render.CodecScmpBus

/-!
# `SA0` (bus 62): the codec's source-map allowance bus balances

The codec sends `(τ, k, ap, big)` from every record `k` that is the source of some link (`useC`) and
receives `(τ, srcOf l, apR, bigR)` at every link `l` with a source (`hasC`).  `srcOf` is injective (a
record is the source of at most the link `tgt k`), so the two lists are permutations of each other
(`blk_sa0_perm`); the values agree because the received allowance of link `l` is the source record's
own prior allowance (`blkOf`), and a `u64` allowance has a nonzero byte above the third iff it is
`≥ 2^24`.  **`RenderBundleV3.balancedAt_sa0`**.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates

/-! ## The source map -/

theorem srcOf_spec {ids : List Nat} {l k : Nat} (h : srcOf ids l = some k) :
    k < ids.length * ids.length ∧ tgt ids k = l := by
  have hm := List.mem_of_getLast? h
  simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hm
  exact hm

theorem srcOf_inj {ids : List Nat} {l l' k : Nat} (h : srcOf ids l = some k) (h' : srcOf ids l' = some k) :
    l = l' := by
  rw [← (srcOf_spec h).2, (srcOf_spec h').2]

theorem nodup_filterMap' {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (∀ a a' b, f a = some b → f a' = some b → a = a') → (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    have ih := nodup_filterMap' hl.2 hinj
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih
    | some b =>
      rw [List.nodup_cons]
      refine ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
      exact hl.1 (by rw [hinj a a' b hfa hfa']; exact ha')

/-- The sources of the links are exactly the used records. -/
theorem src_perm (ids : List Nat) :
    ((List.range (ids.length * ids.length)).filterMap (srcOf ids)).Perm
      ((List.range (ids.length * ids.length)).filter fun k =>
        (List.range (ids.length * ids.length)).any fun l' => srcOf ids l' == some k) := by
  apply (List.perm_ext_iff_of_nodup (nodup_filterMap' List.nodup_range
    (fun a a' b h h' => srcOf_inj h h')) (List.nodup_range.filter _)).mpr
  intro k
  simp only [List.mem_filterMap, List.mem_range, List.mem_filter, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨l, hl, hs⟩
    exact ⟨(srcOf_spec hs).1, l, hl, hs⟩
  · rintro ⟨_, l, hl, hs⟩
    exact ⟨l, hl, hs⟩

/-! ## One block -/

/-- The `SA0` message of record `k`. -/
def sa0Msg (B : Blk) (k : Nat) : List Fp :=
  [Fp.ofNat B.I.tv, Fp.ofNat k, Fp.ofNat (if B.I.pres then B.a0 k % 16777216 else 0),
    Fp.ofNat (if B.I.pres ∧ 16777216 ≤ B.a0 k then 1 else 0)]

/-- The source-map shape of a block (as built by `blkOf`). -/
structure SrcShape (B : Blk) : Prop where
  N : B.I.N = B.ids.length * B.ids.length
  kk : ∀ kk, (B.recs kk).kk = kk
  srcS : ∀ kk, (B.recs kk).srcS = (srcOf B.ids kk).getD 0
  hasC : ∀ kk, (B.recs kk).hasC = (srcOf B.ids kk).isSome
  useC : ∀ kk, (B.recs kk).useC = (List.range B.I.N).any fun l' => srcOf B.ids l' == some kk
  a0s : ∀ kk, (B.recs kk).a0s = match srcOf B.ids kk with
    | some k' => if B.I.pres then B.a0 k' else 0
    | none => 0
  a0 : ∀ k, B.a0 k < 2 ^ 64

theorem apS_7 (B : Blk) (k : Nat) : B.apS k 7 = if B.I.pres then B.a0 k % 16777216 else 0 := by
  simp only [Blk.apS, Blk.bpr, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  cases B.I.pres <;> simp <;> omega

theorem big_7 (B : Blk) (k : Nat) (h : B.a0 k < 2 ^ 64) :
    (if B.bigS k 7 = 1 ∨ B.bpr k 2 7 ≠ 0 then 1 else 0) =
      if B.I.pres ∧ 16777216 ≤ B.a0 k then 1 else 0 := by
  simp only [Blk.bigS, Blk.bpr, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.any_cons, List.any_nil]
  by_cases hp : B.I.pres = true
  · have key : (16777216 ≤ B.a0 k) ↔ (B.a0 k / 16777216 % 256 ≠ 0 ∨ B.a0 k / 4294967296 % 256 ≠ 0 ∨
        B.a0 k / 1099511627776 % 256 ≠ 0 ∨ B.a0 k / 281474976710656 % 256 ≠ 0 ∨
        B.a0 k / 72057594037927936 % 256 ≠ 0) := by omega
    by_cases hb : 16777216 ≤ B.a0 k
    · have := key.mp hb
      simp only [hp, hb, ite_true, true_and, Nat.reducePow, Nat.reduceLT, ite_false] at this ⊢
      simp only [Nat.not_lt_zero, decide_false, Bool.false_or, Nat.reduceLeDiff]
      rcases this with h3 | h3 | h3 | h3 | h3 <;> simp [h3]
    · have := (not_congr key).mp hb
      simp only [hp, hb, ite_true, true_and, Nat.reducePow, Nat.reduceLT, ite_false] at this ⊢
      simp only [not_or, Decidable.not_not] at this
      simp [this]
  · simp [hp]

theorem flatMap_ite_single {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    l.flatMap (fun a => if p a = true then [f a] else []) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a = true <;> simp [List.filter_cons, h, ih]

theorem map_filterMap' {α β γ : Type} (l : List α) (g : α → Option β) (f : β → γ) :
    (l.filterMap g).map f = l.flatMap (fun a => match g a with | some b => [f b] | none => []) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : g a <;> simp [List.filterMap_cons, h, ih]

theorem blk_sa0s_eq (B : Blk) (h : SrcShape B) :
    B.descs.flatMap sa0sT = ((List.range B.I.N).filter fun k =>
      (List.range B.I.N).any fun l' => srcOf B.ids l' == some k).map (sa0Msg B) := by
  rw [blk_sa0s, ← flatMap_ite_single]
  apply flatMap_congr''
  intro k _
  rw [h.useC k]
  split
  · simp only [sa0Msg, h.kk k, apS_7, big_7 B k (h.a0 k)]
  · rfl

theorem blk_sa0r_eq (B : Blk) (h : SrcShape B) :
    B.descs.flatMap sa0rT = ((List.range B.I.N).filterMap (srcOf B.ids)).map (sa0Msg B) := by
  rw [blk_sa0r, map_filterMap']
  apply flatMap_congr''
  intro l _
  rw [h.hasC l]
  cases hs : srcOf B.ids l with
  | none => simp
  | some k =>
    simp only [Option.isSome_some, ite_true, sa0Msg, h.srcS l, hs, Option.getD_some, apRv, bigRv, h.a0s l]
    by_cases hp : B.I.pres = true <;> simp [hp]

theorem blk_sa0_perm (B : Blk) (h : SrcShape B) : (B.descs.flatMap sa0sT).Perm (B.descs.flatMap sa0rT) := by
  rw [blk_sa0s_eq B h, blk_sa0r_eq B h, h.N]
  exact ((src_perm B.ids).map _).symm

theorem flatMap_perm' {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (flatMap_perm' l (fun x hx => h x (by simp [hx])))

/-! ## The native blocks -/

theorem a0Canon_lt (n : Nat) (prev : NearSpec.Bandwidth.State)
    (h : ∀ la ∈ prev.links, la.allowance < 2 ^ 64) (k : Nat) : (a0Canon n prev)[k]! < 2 ^ 64 := by
  unfold a0Canon
  split
  · by_cases hk : k < (prev.links.map (·.allowance)).toArray.size
    · rw [getElem!_pos _ k hk]
      simp only [List.getElem_toArray, List.getElem_map]
      exact h _ (List.getElem_mem _)
    · rw [getElem!_neg _ k hk]; decide
  · by_cases hk : k < (Array.replicate (n * n) 0).size
    · rw [getElem!_pos _ k hk]; simp
    · rw [getElem!_neg _ k hk]; decide

theorem old_links_lt (b : NativeBlock) (hb : b.Valid) : ∀ la ∈ b.old.links, la.allowance < 2 ^ 64 := by
  have hd := hb.2.2.2.1
  cases hp : b.prior with
  | none =>
    rw [hp] at hd
    simp only [Option.some.injEq] at hd
    rw [← hd]; simp [NearSpec.Bandwidth.State.initial]
  | some raw =>
    rw [hp] at hd
    exact fun la hla => ((ProcPriorDecode.decode_exact raw b.old hd).2.1 la hla).2.2

theorem blkOf_shape (b : NativeBlock) (hb : b.Valid) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) : SrcShape (blkOf b) := by
  obtain ⟨_, hnI, _⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  refine ⟨?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun k => ?_⟩
  · simp only [blkOf]; rw [hnI]
  · exact a0Canon_lt _ _ (old_links_lt b hb) k

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly.CodecDigest

theorem covers_sa0_send : Covers Sched.B_SA0 true (fun t => t == 11) = true := by decide +kernel
theorem covers_sa0_recv : Covers Sched.B_SA0 false (fun t => t == 11) = true := by decide +kernel
theorem pub_sa0 (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SA0 s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem codec_sel (pub : List Fp) (Bs : List Blk) (hcap : (allDescs Bs).length ≤ 2 ^ 22) (b : Nat) (s : Bool)
    (G : Desc → List (List Fp)) (hG : ∀ d r, rowTraffic Codec.table.interactions (dRow d r) 11 r pub b s = G d)
    (m : List Fp) :
    cnt (sel s (rowsTraffic Sched.Codec.table.interactions (codecCell Bs) 22 11 pub) b) m =
      (Bs.flatMap fun B => B.descs.flatMap G).count m := by
  have h := codec_bus Bs hcap 11 pub b s G hG
  cases s
  · simp only [sel, Bool.false_eq_true, ite_false, rowsTraffic]
    unfold cnt; rw [natMsgs_toFp, h]
  · simp only [sel, ite_true, rowsTraffic]
    unfold cnt; rw [natMsgs_toFp, h]

namespace RenderBundleV3

/-- **`SA0` balance** of a bundle whose table 11 is the codec render of `PriorCore` blocks. -/
theorem balancedAt_sa0 {pub : List Fp} (R : RenderBundleV3 pub) {p : NearSpecV3.Prep} {B : Nat}
    {bs : List NativeBlock} (hc : PriorCore p B bs)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub) :
    R.BalancedAt Sched.B_SA0 := by
  intro m
  rw [R.sum_tables true _ m _ covers_sa0_send, R.sum_tables false _ m _ covers_sa0_recv, pub_sa0, pub_sa0]
  have hf : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [h11]
  have e1 := codec_sel pub _ (prior_cap hc) _ true sa0sT (rt_sa0s · · 11 pub) m
  have e2 := codec_sel pub _ (prior_cap hc) _ false sa0rT (rt_sa0r · · 11 pub) m
  rw [e1, e2]
  have hp : ((bs.map blkOf).flatMap fun B => B.descs.flatMap sa0sT).Perm
      ((bs.map blkOf).flatMap fun B => B.descs.flatMap sa0rT) := by
    apply flatMap_perm'
    intro Bk hB
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    exact blk_sa0_perm _ (blkOf_shape b (hc.valid b hb).1 i (hc.indexed i b hi).1.2)
  exact hp.count_eq m

end RenderBundleV3
end ZkFormal.NearV3.Assembly
