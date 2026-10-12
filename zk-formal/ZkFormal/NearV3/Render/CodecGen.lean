import ZkFormal.NearV3.Render.CodecChain
import ZkFormal.NearV3.Render.CodecVals
import ZkFormal.NearV3.Sched.Render

/-!
# Honest codec descriptors of one instance block, and their chain

`Blk`: the native data of one codec instance (instance constants `I`, shard ids, the prior
allowance of each record `a0`, per-link data `recs kk`, digest, previous hash and
`sha256(all_shards)` bytes).  `Blk.descs`: its `5 + 24·N + 64` descriptors (header, records with
their bytes and allowance accumulators in closed form, hash, `sha256(all_shards)`), exactly the frozen
generator's row values (`Gen.codecRows`).

`Blk.Ok`: the explicit native premises; `Blk.chain`: the descriptors are a valid chain from
`hdr _ 0` to `ash _ _ 31`; `allDescs_local`: concatenated instances give `TableLocal
Sched.Codec.table`.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.NearV3.Candidates.SchedSetAll

/-- One codec instance block. -/
structure Blk where
  I : Inst
  ids : List Nat
  a0 : Nat → Nat
  recs : Nat → Rec
  dig : List Nat
  hpre : List Nat
  ash : List Nat

namespace Blk
variable (B : Blk)

def bpo (kk f gg : Nat) : Nat :=
  if f < 2 then idByte B.ids kk (8 * f + gg) else if gg < 3 then (B.recs kk).afin / 256 ^ gg % 256 else 0

def bpr (kk f gg : Nat) : Nat :=
  if B.I.pres then (if f < 2 then B.bpo kk f gg else B.a0 kk / 256 ^ gg % 256) else 0

def apS (kk gg : Nat) : Nat :=
  ((List.range gg).map fun i => if i < 3 then 256 ^ i * B.bpr kk 2 i else 0).sum

def apostS (kk gg : Nat) : Nat :=
  ((List.range gg).map fun i => if i < 3 then 256 ^ i * B.bpo kk 2 i else 0).sum

def bigS (kk gg : Nat) : Nat :=
  if (List.range gg).any (fun i => decide (3 ≤ i ∧ B.bpr kk 2 i ≠ 0)) then 1 else 0

def recD (kk f gg : Nat) : Desc :=
  .record B.I (B.recs kk) f gg (B.bpo kk f gg) (B.bpr kk f gg)
    (if f = 2 then B.apS kk gg else 0) (if f = 2 then B.apostS kk gg else 0)
    (if f = 2 then B.bigS kk gg else 0)

def fieldDescs (kk f : Nat) : List Desc := (List.range 8).map (B.recD kk f)

def recordDescs (kk : Nat) : List Desc := B.fieldDescs kk 0 ++ B.fieldDescs kk 1 ++ B.fieldDescs kk 2

def records (m : Nat) : List Desc := ((List.range m).map B.recordDescs).flatten

def descs : List Desc :=
  (List.range 5).map (Desc.hdr B.I) ++ B.records B.I.N ++
    (List.range 32).map (Desc.hash B.I B.dig B.hpre) ++ (List.range 32).map (Desc.ash B.I B.ash)

/-- The explicit native premises of one block. -/
structure Ok : Prop where
  inst : InstOk B.I
  N1 : 1 ≤ B.I.N
  kk : ∀ kk < B.I.N, (B.recs kk).kk = kk
  ikl : ∀ kk < B.I.N, (B.recs kk).iklv = inv (fsub kk (B.I.N - 1))
  afin : ∀ kk < B.I.N, (B.recs kk).afin < 2 ^ 24
  hasC : ∀ kk < B.I.N, (B.recs kk).hasC = false → apRv (B.recs kk) = 0 ∧ bigRv (B.recs kk) = 0
  ft : ∀ kk < B.I.N, (B.recs kk).ft < 2 ^ 24
  al : ∀ kk < B.I.N, b2n (B.recs kk).al * B.I.base ≤ a1v B.I (B.recs kk)
  dig : ∀ x ∈ B.dig, x < 256
  hpre : ∀ x ∈ B.hpre, x < 256
  ashB : ∀ x ∈ B.ash, x < 256
  vid : B.I.vid < P
  n : B.I.n < 65536
  src : ∀ kk < B.I.N, (B.recs kk).srcS < P
  gb : ∀ kk < B.I.N, (B.recs kk).gb < 2 ^ 26
  gfin : ∀ kk < B.I.N, (B.recs kk).gfin < 2 ^ 26

/-! ## Accumulator recurrences -/

theorem apS_succ (kk gg : Nat) :
    B.apS kk (gg + 1) = B.apS kk gg + (if gg < 3 then 256 ^ gg * B.bpr kk 2 gg else 0) := by
  simp [apS, List.range_succ, List.map_append, List.sum_append]

theorem apostS_succ (kk gg : Nat) :
    B.apostS kk (gg + 1) = B.apostS kk gg + (if gg < 3 then 256 ^ gg * B.bpo kk 2 gg else 0) := by
  simp [apostS, List.range_succ, List.map_append, List.sum_append]

theorem bigS_succ (kk gg : Nat) :
    B.bigS kk (gg + 1) = if B.bigS kk gg = 1 ∨ (3 ≤ gg ∧ B.bpr kk 2 gg ≠ 0) then 1 else 0 := by
  unfold bigS
  simp only [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  by_cases h : (List.range gg).any (fun i => decide (3 ≤ i ∧ B.bpr kk 2 i ≠ 0)) = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem bigS_le (kk gg : Nat) : B.bigS kk gg ≤ 1 := by unfold bigS; split <;> omega

theorem apS_zero (kk : Nat) : B.apS kk 0 = 0 := rfl
theorem apostS_zero (kk : Nat) : B.apostS kk 0 = 0 := rfl
theorem bigS_zero (kk : Nat) : B.bigS kk 0 = 0 := rfl

theorem apostS_end (kk : Nat) (h : (B.recs kk).afin < 2 ^ 24) : B.apostS kk 7 = (B.recs kk).afin := by
  simp only [apostS, bpo, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [Nat.reduceLT, ite_true, ite_false, Nat.lt_irrefl, Nat.reducePow, Nat.pow_zero,
    Nat.div_one, Nat.one_mul, show ¬ (3 : Nat) < 3 from by decide, show ¬ (4 : Nat) < 3 from by decide,
    show ¬ (5 : Nat) < 3 from by decide, show ¬ (6 : Nat) < 3 from by decide,
    show ¬ (2 : Nat) < 2 from by decide]
  omega

/-! ## Row facts -/

theorem bpo_lt (kk f gg : Nat) : B.bpo kk f gg < 256 := by
  unfold bpo idByte; split
  · exact Nat.mod_lt _ (by decide)
  · split
    · exact Nat.mod_lt _ (by decide)
    · decide

theorem bpr_lt (kk f gg : Nat) : B.bpr kk f gg < 256 := by
  unfold bpr; split
  · split
    · exact B.bpo_lt kk f gg
    · exact Nat.mod_lt _ (by decide)
  · decide

theorem bpr_id (kk f gg : Nat) (hf : f < 2) : B.bpr kk f gg = b2n B.I.pres * B.bpo kk f gg := by
  unfold bpr; cases B.I.pres <;> simp [b2n, hf]

theorem bpr_abs (kk f gg : Nat) (h : B.I.pres = false) : B.bpr kk f gg = 0 := by
  unfold bpr; simp [h]

theorem bpo_hi (kk gg : Nat) (h : 3 ≤ gg) : B.bpo kk 2 gg = 0 := by
  unfold bpo; simp; omega

theorem apS_lt (kk : Nat) : ∀ gg, B.apS kk gg < 256 ^ (min gg 3)
  | 0 => by simp [apS]
  | gg + 1 => by
    have ih := apS_lt kk gg
    rw [apS_succ]
    have hb := B.bpr_lt kk 2 gg
    by_cases h : gg < 3
    · rw [if_pos h]
      rcases (show gg = 0 ∨ gg = 1 ∨ gg = 2 by omega) with rfl | rfl | rfl <;> simp at ih ⊢ <;> omega
    · rw [if_neg h, show min (gg + 1) 3 = min gg 3 by omega]; omega

theorem apostS_lt (kk : Nat) : ∀ gg, B.apostS kk gg < 256 ^ (min gg 3)
  | 0 => by simp [apostS]
  | gg + 1 => by
    have ih := apostS_lt kk gg
    rw [apostS_succ]
    have hb := B.bpo_lt kk 2 gg
    by_cases h : gg < 3
    · rw [if_pos h]
      rcases (show gg = 0 ∨ gg = 1 ∨ gg = 2 by omega) with rfl | rfl | rfl <;> simp at ih ⊢ <;> omega
    · rw [if_neg h, show min (gg + 1) 3 = min gg 3 by omega]; omega

theorem pow_min_le (gg : Nat) : 256 ^ (min gg 3) ≤ 2 ^ 24 := by
  have : 256 ^ (min gg 3) ≤ 256 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
  simpa using this


/-! ## The chain -/

theorem fieldDescs_eq (kk f : Nat) : B.fieldDescs kk f =
    [B.recD kk f 0, B.recD kk f 1, B.recD kk f 2, B.recD kk f 3, B.recD kk f 4, B.recD kk f 5,
     B.recD kk f 6, B.recD kk f 7] := rfl

theorem field_chain (kk f : Nat) : Chain (B.fieldDescs kk f) := by
  apply chain_map_range
  intro k hk
  simp only [recD, Desc.Adj]
  refine ⟨(by trivial), Or.inl ⟨by omega, (by trivial), (by trivial), (by trivial), fun h2 => ?_⟩⟩
  subst h2
  simp only [ite_true]
  exact ⟨B.apS_succ kk k, B.apostS_succ kk k, B.bigS_succ kk k⟩

theorem record_chain (kk : Nat) : Chain (B.recordDescs kk) := by
  unfold recordDescs
  refine chain_append _ _ (chain_append _ _ (B.field_chain kk 0) (B.field_chain kk 1) ?_)
    (B.field_chain kk 2) ?_
  · intro x y hx hy
    simp only [fieldDescs_eq, List.getLast?_cons_cons, List.getLast?_singleton, List.head?_cons,
      Option.some.injEq] at hx hy
    subst hx; subst hy
    simp only [recD, Desc.Adj]
    exact ⟨(by trivial), Or.inr (Or.inl ⟨(by trivial), by decide, (by trivial), (by trivial), (by trivial), fun h => absurd h (by decide)⟩)⟩
  · intro x y hx hy
    simp only [fieldDescs_eq, List.cons_append, List.nil_append, List.getLast?_cons_cons,
      List.getLast?_singleton, List.head?_cons, Option.some.injEq] at hx hy
    subst hx; subst hy
    simp only [recD, Desc.Adj]
    refine ⟨(by trivial), Or.inr (Or.inl ⟨(by trivial), by decide, (by trivial), (by trivial), (by trivial), fun _ => ?_⟩)⟩
    simp only [ite_true]
    exact ⟨(by trivial), (by trivial), (by trivial)⟩

theorem record_head (kk : Nat) : (B.recordDescs kk).head? = some (B.recD kk 0 0) := rfl

theorem record_last (kk : Nat) : (B.recordDescs kk).getLast? = some (B.recD kk 2 7) := by
  simp [recordDescs, fieldDescs_eq]

theorem records_chain (hok : B.Ok) : ∀ m, m ≤ B.I.N → Chain (B.records m) ∧
    (1 ≤ m → (B.records m).head? = some (B.recD 0 0 0) ∧
      (B.records m).getLast? = some (B.recD (m - 1) 2 7))
  | 0, _ => ⟨by simp [records]; exact chain_nil, fun h => absurd h (by omega)⟩
  | m + 1, hm => by
    have ih := records_chain hok m (by omega)
    have heq : B.records (m + 1) = B.records m ++ B.recordDescs m := by
      simp [records, List.range_succ, List.map_append, List.flatten_append]
    rw [heq]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simp only [records, List.range_zero, List.map_nil, List.flatten_nil, List.nil_append]
      exact ⟨B.record_chain 0, fun _ => ⟨B.record_head 0, B.record_last 0⟩⟩
    · obtain ⟨hc, hht⟩ := ih
      obtain ⟨hh, hl⟩ := hht hpos
      refine ⟨chain_append _ _ hc (B.record_chain m) ?_, fun _ => ⟨?_, ?_⟩⟩
      · intro x y hx hy
        rw [hl] at hx; rw [B.record_head m] at hy
        simp only [Option.some.injEq] at hx hy
        subst hx; subst hy
        simp only [recD, Desc.Adj]
        refine ⟨(by trivial), Or.inr (Or.inr ⟨(by trivial), (by trivial), (by trivial), (by trivial), ?_, ?_⟩)⟩
        · rw [hok.kk m (by omega), hok.kk (m - 1) (by omega)]; omega
        · rw [hok.kk (m - 1) (by omega)]; omega
      · rw [List.head?_append, hh]; rfl
      · rw [List.getLast?_append, B.record_last m]; simp

theorem descs_chain (hok : B.Ok) : Chain B.descs ∧ B.descs.head? = some (.hdr B.I 0) ∧
    B.descs.getLast? = some (.ash B.I B.ash 31) := by
  obtain ⟨rc, rht⟩ := B.records_chain hok B.I.N (Nat.le_refl _)
  obtain ⟨rh, rl⟩ := rht hok.N1
  have hc5 : Chain ((List.range 5).map (Desc.hdr B.I)) := chain_map_range 5 _ (fun k hk => by
    simp only [Desc.Adj]; exact ⟨by omega, (by trivial), (by trivial)⟩)
  have hz : Chain ((List.range 32).map (Desc.hash B.I B.dig B.hpre)) := chain_map_range 32 _ (fun k hk => by
    simp only [Desc.Adj]; exact ⟨by omega, (by trivial), (by trivial), (by trivial), (by trivial)⟩)
  have ha : Chain ((List.range 32).map (Desc.ash B.I B.ash)) := chain_map_range 32 _ (fun k hk => by
    simp only [Desc.Adj]; exact ⟨by omega, (by trivial), (by trivial), (by trivial)⟩)
  have hlast5 : ((List.range 5).map (Desc.hdr B.I)).getLast? = some (.hdr B.I 4) := by
    simp [List.range_succ]
  have hhead32 : ((List.range 32).map (Desc.hash B.I B.dig B.hpre)).head? = some (.hash B.I B.dig B.hpre 0) := by
    simp [List.range_succ_eq_map]
  have hlast32 : ((List.range 32).map (Desc.hash B.I B.dig B.hpre)).getLast? = some (.hash B.I B.dig B.hpre 31) := by
    simp [List.range_succ]
  have ahead : ((List.range 32).map (Desc.ash B.I B.ash)).head? = some (.ash B.I B.ash 0) := by
    simp [List.range_succ_eq_map]
  have alast : ((List.range 32).map (Desc.ash B.I B.ash)).getLast? = some (.ash B.I B.ash 31) := by
    simp [List.range_succ]
  have hNk := hok.kk (B.I.N - 1) (by have := hok.N1; omega)
  refine ⟨chain_append _ _ (chain_append _ _ (chain_append _ _ hc5 rc ?_) hz ?_) ha ?_, ?_, ?_⟩
  · intro x y hx hy
    rw [hlast5] at hx; rw [rh] at hy
    simp only [Option.some.injEq] at hx hy; subst hx; subst hy
    simp only [recD, Desc.Adj]
    exact ⟨(by trivial), (by trivial), hok.kk 0 hok.N1, (by trivial), (by trivial)⟩
  · intro x y hx hy
    rw [List.getLast?_append, rl] at hx; rw [hhead32] at hy
    simp only [Option.some_or, Option.some.injEq] at hx hy; subst hx; subst hy
    simp only [recD, Desc.Adj]
    refine ⟨(by trivial), (by trivial), (by trivial), ?_, (by trivial)⟩
    rw [hNk]; have := hok.N1; omega
  · intro x y hx hy
    rw [List.getLast?_append, hlast32] at hx; rw [ahead] at hy
    simp only [Option.some_or, Option.some.injEq] at hx hy; subst hx; subst hy
    simp only [Desc.Adj]
    exact ⟨(by trivial), (by trivial), (by trivial)⟩
  · simp [descs, List.range_succ_eq_map]
  · rw [descs, List.getLast?_append, alast]; simp

/-! ## Validity -/

theorem mem_records {d : Desc} {m : Nat} (h : d ∈ B.records m) :
    ∃ kk f gg, kk < m ∧ f < 3 ∧ gg < 8 ∧ d = B.recD kk f gg := by
  simp only [records, List.mem_flatten, List.mem_map, List.mem_range] at h
  obtain ⟨L, ⟨kk, hk, rfl⟩, hd⟩ := h
  simp only [recordDescs, fieldDescs, List.mem_append, List.mem_map, List.mem_range] at hd
  rcases hd with (⟨gg, hg, rfl⟩ | ⟨gg, hg, rfl⟩) | ⟨gg, hg, rfl⟩
  · exact ⟨kk, 0, gg, hk, by decide, hg, rfl⟩
  · exact ⟨kk, 1, gg, hk, by decide, hg, rfl⟩
  · exact ⟨kk, 2, gg, hk, by decide, hg, rfl⟩

theorem descs_valid (hok : B.Ok) : ∀ d ∈ B.descs, d.Valid := by
  intro d hd
  obtain ⟨htv, hN, hNN, hb, hfa⟩ := hok.inst
  have hIB : InstB B.I := ⟨by unfold P at htv; omega, by have := hok.vid; unfold P at this; omega,
    hok.n, hN, hb, hfa⟩
  simp only [descs, List.mem_append, List.mem_map, List.mem_range] at hd
  rcases hd with ((⟨p, hp, rfl⟩ | hr) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
  · exact ⟨hdr_vals B.I p (by omega) hIB, hok.inst, show p ≤ 4 by omega⟩
  · obtain ⟨kk, f, gg, hk, hf, hg, rfl⟩ := B.mem_records hr
    have hkk := hok.kk kk hk
    have hap := B.apS_lt kk gg
    have hapo := B.apostS_lt kk gg
    have hpm := pow_min_le gg
    refine ⟨rec_vals B.I (B.recs kk) f gg _ _ _ _ _ hIB hf hg (by rw [hkk]; omega) (B.bpo_lt kk f gg)
      (B.bpr_lt kk f gg) (by split <;> omega) (by split <;> omega)
      (by split; exact B.bigS_le kk gg; omega)
      (by rw [hok.ikl kk hk]; exact inv_lt' _) (by have := hok.src kk hk; unfold P at this; omega)
      (hok.gb kk hk) (by have := hok.afin kk hk; omega) (hok.gfin kk hk)
      (by have := hok.ft kk hk; omega), hok.inst, ?_⟩
    refine ⟨hf, hg, by rw [hkk]; exact hk, by rw [hok.ikl kk hk, hkk], B.bpo_lt kk f gg,
      B.bpr_lt kk f gg, B.bpr_id kk f gg, B.bpr_abs kk f gg, ?_, ?_, (hok.hasC kk hk · |>.1),
      (hok.hasC kk hk · |>.2), ?_⟩
    · intro h2 h3; subst h2; exact B.bpo_hi kk gg h3
    · split
      · exact B.bigS_le kk gg
      · omega
    · intro h2 h7; subst h2; subst h7
      simp only [ite_true]
      exact ⟨B.apostS_end kk (hok.afin kk hk), hok.ft kk hk, hok.al kk hk⟩
  · exact ⟨hash_vals B.I B.dig B.hpre j hj hIB hok.dig hok.hpre, hok.inst, hj,
      getD_lt hok.dig (by decide) j, getD_lt hok.hpre (by decide) j⟩
  · exact ⟨ash_vals B.I B.ash j hj hIB hok.ashB, hok.inst, hj⟩

theorem descs_length : B.descs.length = 5 + 24 * B.I.N + 64 := by
  have : ∀ m, (B.records m).length = 24 * m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have heq : B.records (m + 1) = B.records m ++ B.recordDescs m := by
        simp [records, List.range_succ, List.map_append, List.flatten_append]
      rw [heq, List.length_append, ih]
      simp [recordDescs, fieldDescs_eq]; omega
  simp [descs, this]; omega

end Blk

/-! ## Concatenated instances -/

def allDescs (Bs : List Blk) : List Desc := (Bs.map Blk.descs).flatten

theorem allDescs_chain (Bs : List Blk) (hok : ∀ B ∈ Bs, B.Ok) :
    Chain (allDescs Bs) ∧ (∀ x, (allDescs Bs).head? = some x → x.FirstOk) ∧
      (∀ x, (allDescs Bs).getLast? = some x → x.Final) := by
  have h := chain_flatten (Bs.map Blk.descs) (fun x => ∃ I, x = .hdr I 0) (fun x => ∃ I a, x = .ash I a 31)
    (fun x y ⟨I, a, hx⟩ ⟨I', hy⟩ => by subst hx; subst hy; exact ⟨rfl, rfl⟩)
    (fun L hL => by
      simp only [List.mem_map] at hL
      obtain ⟨B, hB, rfl⟩ := hL
      obtain ⟨c, hh, hl⟩ := B.descs_chain (hok B hB)
      exact ⟨c, fun x hx => ⟨B.I, by rw [hh] at hx; simp at hx; exact hx.symm⟩,
        fun x hx => ⟨B.I, B.ash, by rw [hl] at hx; simp at hx; exact hx.symm⟩⟩)
  obtain ⟨c, hh, hl⟩ := h
  refine ⟨c, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨I, rfl⟩ := hh x hx; rfl
  · obtain ⟨I, a, rfl⟩ := hl x hx; rfl

theorem allDescs_valid (Bs : List Blk) (hok : ∀ B ∈ Bs, B.Ok) : ∀ d ∈ allDescs Bs, d.Valid := by
  intro d hd
  simp only [allDescs, List.mem_flatten, List.mem_map] at hd
  obtain ⟨L, ⟨B, hB, rfl⟩, hd⟩ := hd
  exact B.descs_valid (hok B hB) d hd

/-- **`TableLocal Sched.Codec.table` for concatenated honest instance blocks.** -/
theorem allDescs_local (Bs : List Blk) (hok : ∀ B ∈ Bs, B.Ok) (hcap : (allDescs Bs).length < 2 ^ 22)
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal Codec.table (codecTrace (allDescs Bs)) t pub := by
  obtain ⟨c, hh, hl⟩ := allDescs_chain Bs hok
  exact table_local_chain _ hcap (allDescs_valid Bs hok) c hh hl t pub

end ZkFormal.NearV3.Render.Cdc
