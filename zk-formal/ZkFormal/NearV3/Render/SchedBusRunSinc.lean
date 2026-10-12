import ZkFormal.NearV3.Render.SchedBusRunFin
import ZkFormal.NearV3.Candidates.ProcShuffleReplay
import ZkFormal.NearV3.Candidates.ProcActualConverted

/-!
# Run-level `SINC` identity: processed increments are exactly the used bits, each once
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

def usedB (used : Array (Array Bool)) (c j : Nat) : Bool := (used.getD c #[]).getD j false

theorem usedB_modify (used : Array (Array Bool)) (c0 j0 c j : Nat) (hc : c0 < used.size)
    (hj : j0 < (used[c0]!).size) :
    usedB (used.modify c0 (·.set! j0 true)) c j = (usedB used c j || (c = c0 && j = j0)) := by
  unfold usedB
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  rw [getElem!_pos used c0 hc] at hj
  by_cases hcc : c0 = c
  · subst hcc
    rw [Array.getElem?_eq_getElem hc]
    simp only [ite_true, Option.map_some, Option.getD_some, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds]
    by_cases hjj : j0 = j
    · subst hjj; simp [hj]
    · simp [hjj, Ne.symm hjj]
  · simp [hcc, Ne.symm hcc]

theorem shuffle_perm (key : List Nat) (k : Nat) (vs sh : List Nat) (kend : Nat)
    (h : replayShuffle key k vs = .ok (sh, kend)) : sh.Perm vs := by
  rw [ProcShuffleReplay.replay_eq] at h
  cases hf : forIn (List.range (vs.length - 1)) (vs, k) (ProcShuffleReplay.step (vs.length - 1) key) with
  | error e => rw [hf] at h; cases h
  | ok out =>
    rw [hf] at h
    cases h
    have := ExceptLoop.invariant _ _ (fun s : List Nat × Nat => s.1.Perm vs) ?_ (vs, k) _ (List.Perm.refl _) hf
    · exact this
    · intro i _ b hb st hst
      unfold ProcShuffleReplay.step at hst
      split at hst
      · cases hst
      · cases hst
        exact (ZkFormal.NearV3.Sched.swapAt_perm _ _ _).trans hb

/-- Entry facts independent of the position. -/
structure EF (cv : Array CReq) (e : Entry) : Prop where
  hcid : e.eout / 64 < cv.size
  hj : e.eout % 64 < cv[e.eout / 64]!.incs.length
  hinc : e.inc = cv[e.eout / 64]!.incs[e.eout % 64]!
  hrem : e.rem = cv[e.eout / 64]!.incs.length - e.eout % 64 - 1
  hs : e.s = cv[e.eout / 64]!.s
  hr : e.r = cv[e.eout / 64]!.r
  hlink : e.link = cv[e.eout / 64]!.link
  hpush : e.push = (e.ok && e.rem != 0)

theorem EntryOk.ef {cv : Array CReq} {rd : Round} {sh : List Nat} {x : Nat} {e : Entry}
    (h : EntryOk cv rd sh x e) : EF cv e :=
  ⟨h.hcid, h.hj, h.hinc, h.hrem, h.hs, h.hr, h.hlink, h.hpush⟩

def hits (es : List Entry) (c j : Nat) : Bool := es.any fun e => e.eout / 64 == c && e.eout % 64 == j

def SIe (cv : Array CReq) (used0 : Array (Array Bool)) (rd : Round) (sh : List Nat)
    (a : ProcActualReplayEntry.Acc) : Prop :=
  a.2.2.2.2.2.2.2.2.1.size = cv.size ∧
  (∀ c, c < cv.size → (a.2.2.2.2.2.2.2.2.1[c]!).size = (cv[c]!).incs.length) ∧
  (∀ c j, usedB a.2.2.2.2.2.2.2.2.1 c j = (usedB used0 c j || hits a.2.2.2.2.2.2.2.2.2.2.toList c j)) ∧
  ∀ i (hi : i < a.2.2.2.2.2.2.2.2.2.2.size), EntryOk cv rd sh i a.2.2.2.2.2.2.2.2.2.2[i]

theorem beq_flip (a b : Nat) : (a == b) = decide (b = a) := by
  cases Nat.decEq a b with
  | isTrue h => subst h; simp
  | isFalse h => simp [h, Ne.symm h]

theorem sie_step (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat) (T x : Nat)
    (used0 : Array (Array Bool)) (a out : ProcActualReplayEntry.Acc) (ha : SIe cv used0 rd sh a)
    (hx : x = a.2.2.2.2.2.2.2.2.2.2.size)
    (h : ProcActualReplayEntry.step I cv rd sh T x a = .ok (.yield out)) :
    SIe cv used0 rd sh out ∧ out.2.2.2.2.2.2.2.2.2.2.size = x + 1 := by
  rcases a with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  obtain ⟨e, oL, oS, oR, sb', rb', aa', gg', ps', rfl, -, he, -⟩ :=
    entry_effect I cv rd sh T x sb rb aa gg ol os orr ps used gi es out h
  obtain ⟨h1, h2, h3, h4⟩ := ha
  dsimp only at h1 h2 h3 h4 hx ⊢
  have hc : e.eout / 64 < used.size := by rw [h1]; exact he.hcid
  have hj : e.eout % 64 < (used[e.eout / 64]!).size := by rw [h2 _ he.hcid]; exact he.hj
  refine ⟨⟨by simpa using h1, ?_, ?_, ?_⟩, by simp [hx]⟩
  · intro c hcv
    rw [getElem!_pos _ c (by simpa [h1] using hcv)]
    by_cases hce : e.eout / 64 = c
    · subst hce
      rw [Array.getElem_modify_self]
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      rw [← h2 _ hcv, getElem!_pos _ _ (by rw [h1]; exact hcv)]
    · rw [Array.getElem_modify_of_ne hce, ← h2 c hcv, getElem!_pos _ _ (by rw [h1]; exact hcv)]
  · intro c j
    rw [usedB_modify used _ _ c j hc hj, h3 c j]
    simp only [hits, Array.toList_push, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    cases usedB used0 c j <;> cases (es.toList.any fun e => e.eout / 64 == c && e.eout % 64 == j) <;>
      simp [beq_flip]
  · intro i hi
    simp only [Array.size_push] at hi
    by_cases hi' : i < es.size
    · rw [Array.getElem_push_lt hi']; exact h4 i hi'
    · have : i = es.size := by omega
      subst this
      rw [Array.getElem_push_eq, ← hx]; exact he

theorem sie_loop (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat) (T : Nat)
    (used0 : Array (Array Bool)) :
    ∀ (k a : Nat) (acc out : ProcActualReplayEntry.Acc), SIe cv used0 rd sh acc →
      acc.2.2.2.2.2.2.2.2.2.2.size = a →
      forIn (List.range' a k) acc (ProcActualReplayEntry.step I cv rd sh T) = .ok out →
      SIe cv used0 rd sh out ∧ out.2.2.2.2.2.2.2.2.2.2.size = a + k
  | 0, a, acc, out, ha, hs, h => by
    simp only [List.range'_zero, List.forIn_nil] at h; cases h; exact ⟨ha, by simp [hs]⟩
  | k + 1, a, acc, out, ha, hs, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    cases he : ProcActualReplayEntry.step I cv rd sh T a acc with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok nx =>
      obtain ⟨next, rfl, -, -, -⟩ :=
        ProcActualEntryTransition.step_effect I cv rd sh T a acc nx (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he, bind, Except.bind] at h
      obtain ⟨hn, hsz⟩ := sie_step I cv rd sh T a used0 acc next ha hs.symm he
      have := sie_loop I cv rd sh T used0 k (a + 1) next out hn hsz h
      exact ⟨this.1, by rw [this.2]; omega⟩

def allE (s : ProcActualReplayRound.Acc) : List Entry := (accRounds s).toList.flatMap (·.entries)

def SI (cv : Array CReq) (s : ProcActualReplayRound.Acc) : Prop :=
  (accUsed s).size = cv.size ∧
  (∀ c, c < cv.size → ((accUsed s)[c]!).size = (cv[c]!).incs.length) ∧
  (∀ c j, usedB (accUsed s) c j = hits (allE s) c j) ∧
  (∀ e ∈ allE s, EF cv e) ∧
  ((allE s).map (·.eout)).Perm ((allE s).map (·.ein))

theorem hits_append (a b : List Entry) (c j : Nat) : hits (a ++ b) c j = (hits a c j || hits b c j) := by
  simp [hits, List.any_append]

set_option maxHeartbeats 1600000 in
theorem si_round (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : ProcActualReplayRound.Acc) (hs : SI cv s)
    (h : ProcActualReplayRound.step I cv key rd s = .ok (.yield out)) : SI cv out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  obtain ⟨sh, kend, col, eo, -, hent, hsh, rfl⟩ :=
    round_effect I cv key rd sb rb aa gg ol os orr ps bs tm kp kq zq used rs gi out h
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  simp only [accUsed, allE, accRounds] at h1 h2 h3 h4 h5
  have h0 : SIe cv used rd sh (sb,rb,aa,gg,ol,os,orr,ps,used,gi,(#[] : Array Entry)) :=
    ⟨h1, h2, fun c j => by simp [hits], fun i hi => by simp at hi⟩
  obtain ⟨⟨e1, e2, e3, e4⟩, esz⟩ := sie_loop I cv rd sh tm used rd.bucket.length 0 _ eo h0 rfl
    (by simpa [List.range_eq_range'] using hent)
  have hperm := shuffle_perm key kp _ sh kend hsh
  have hlen : sh.length = rd.bucket.length := by simpa using hperm.length_eq
  have hout : eo.2.2.2.2.2.2.2.2.2.2.toList.map (·.eout) = sh := by
    apply List.ext_getElem (by simp [esz, hlen])
    intro i hi1 hi2
    simp only [List.getElem_map, Array.getElem_toList]
    rw [(e4 i (by simpa using hi1)).heout, getElem!_pos sh i hi2]
  have hin : eo.2.2.2.2.2.2.2.2.2.2.toList.map (·.ein) = rd.bucket.map (·.v) := by
    apply List.ext_getElem (by simp [esz])
    intro i hi1 hi2
    simp only [List.getElem_map, Array.getElem_toList]
    rw [(e4 i (by simpa using hi1)).hein, getElem!_pos _ i (by simpa using hi2)]
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · intro c j
    simp only [accUsed, allE, accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hits_append]
    rw [e3 c j, h3 c j]
  · intro e he
    simp only [allE, accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_append] at he
    rcases he with he | he
    · exact h4 e he
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      simp only [Array.getElem_toList] at hi ⊢
      exact (e4 i (by simpa using hi)).ef
  · simp only [allE, accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append]
    exact h5.append (by rw [hout, hin]; exact hperm)

theorem si_rounds (I : Input) (cv : Array CReq) (key : List Nat) :
    ∀ (rs : List Round) (s out : ProcActualReplayRound.Acc), SI cv s →
      forIn rs s (ProcActualReplayRound.step I cv key) = .ok out → SI cv out
  | [], s, out, hs, h => by simp only [List.forIn_nil] at h; cases h; exact hs
  | rd :: rs, s, out, hs, h => by
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok nx =>
      obtain ⟨next, rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s nx he
      simp only [he, bind, Except.bind] at h
      exact si_rounds I cv key rs next out (si_round I cv key rd s next hs he) h

theorem si_replay (I : Input) (cv : Array CReq) (rs : List Round) (out : ProcActualReplayRound.Acc)
    (h : ProcActualReplayFactor.replay I cv rs = .ok out) : SI cv out := by
  unfold ProcActualReplayFactor.replay at h
  obtain ⟨ops, -, h⟩ := bind_ok h
  apply si_rounds I cv _ rs _ out ?_ h
  refine ⟨by simp [ProcActualReplayInitial.initial, accUsed], ?_, ?_, by simp [allE, ProcActualReplayInitial.initial, accRounds],
    by simp [allE, ProcActualReplayInitial.initial, accRounds]⟩
  · intro c hc
    simp only [ProcActualReplayInitial.initial, accUsed]
    rw [getElem!_pos _ c (by simpa using hc), getElem!_pos cv c hc]
    simp
  · intro c j
    simp only [ProcActualReplayInitial.initial, accUsed, allE, accRounds, usedB, hits]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases hc : cv[c]? <;> simp [Array.getElem?_replicate]
    split <;> rfl

theorem nodup_of_count_le {l : List Nat} (h : ∀ a, l.count a ≤ 1) : l.Nodup := by
  apply List.nodup_iff_count_of_mem.mpr
  intro a ha
  have := List.count_pos_iff.mpr ha
  have := h a
  omega

theorem count_push_le (E : List Entry) (v : Nat) (hv : 1 ≤ v) :
    (E.flatMap (fun e => if e.push then [e.eout + 1] else [])).count v ≤ (E.map (·.eout)).count (v - 1) := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.flatMap_cons, List.map_cons, List.count_append, List.count_cons, beq_iff_eq]
    by_cases h : e.eout = v - 1
    · have h' : e.eout + 1 = v := by omega
      cases e.push <;> simp [h, h', Nat.sub_add_cancel hv] <;> omega
    · have h' : e.eout + 1 ≠ v := by omega
      cases e.push <;> simp [h, h', Nat.sub_add_cancel hv] <;> omega

theorem count_push_zero (E : List Entry) (v : Nat) (hv : v % 64 = 0)
    (hp : ∀ e ∈ E, e.push = true → e.eout % 64 + 1 < 64) :
    (E.flatMap (fun e => if e.push then [e.eout + 1] else [])).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp hm
  split at hm
  · rename_i hpe
    simp only [List.mem_singleton] at hm
    have := hp e he hpe
    omega
  · simp at hm

/-- Distinct processed entries: every `eout` once. -/
theorem eout_nodup (E : List Entry) (R : Nat)
    (hperm : (E.map (·.eout)).Perm ((List.range R).map (64 * ·) ++
      E.flatMap (fun e => if e.push then [e.eout + 1] else [])))
    (hp : ∀ e ∈ E, e.push = true → e.eout % 64 + 1 < 64) : (E.map (·.eout)).Nodup := by
  apply nodup_of_count_le
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    rw [hperm.count_eq, List.count_append]
    have hr : ((List.range R).map (64 * ·)).count v ≤ 1 := by
      have hn : ((List.range R).map (64 * ·)).Nodup := by
        apply List.Pairwise.map _ _ List.nodup_range
        intro a b hab; omega
      rw [hn.count]; split <;> omega
    by_cases h0 : v % 64 = 0
    · rw [count_push_zero E v h0 hp]; omega
    · have hz : ((List.range R).map (64 * ·)).count v = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
        omega
      have := count_push_le E v (by omega)
      have := ih (v - 1) (by omega)
      omega

/-- The `SINC` payload (after `τ`) of an entry. -/
def incN (e : Entry) : List Nat := [e.eout, e.inc, e.rem, e.s, e.r, e.link]

/-- The used increments `64·cid + j` of the converted requests. -/
def usedV (conv : List CReq) (used : Array (Array Bool)) : List Nat :=
  (List.range (64 * conv.length)).filter fun v =>
    decide (v % 64 < (conv.getD (v / 64) default).incs.length) && usedB used (v / 64) (v % 64)

/-- The `SINC` payload of the used increment `v`. -/
def incOf (conv : List CReq) (v : Nat) : List Nat :=
  [v, (conv.getD (v / 64) default).incs[v % 64]!, (conv.getD (v / 64) default).incs.length - v % 64 - 1,
    (conv.getD (v / 64) default).s, (conv.getD (v / 64) default).r, (conv.getD (v / 64) default).link]

theorem arr_getD {α : Type} [Inhabited α] (a : Array α) (i : Nat) : a[i]! = a.toList.getD i default := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
    simp
  · rw [getElem!_neg a i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]
    rfl

/-- **`SINC` of one run**: the processed entries are exactly the used increments, each once. -/
theorem run_sinc (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ((R.rounds.flatMap (·.entries)).map incN).Perm ((usedV R.conv R.used).map (incOf R.conv)) := by
  have hsp := run_spush I tau R h
  obtain ⟨cv, st, rs, ev, s, gs, hpre, hrep, -, -, -, hrd, hused, hconv, -, -, -⟩ := run_decomp I tau R h
  obtain ⟨hcv, -⟩ := ProcActualAfterMemoryReduction.prefix_facts I cv st rs ev hpre
  have hfa := ProcActualInitialPush.loop_facts I cv hcv
  have hbd := ProcActualConverted.loop_bounded I cv hcv
  obtain ⟨-, -, hU, hEF, hPerm⟩ := si_replay I cv rs s hrep
  rw [hrd, hused, hconv]
  rw [hrd, hconv] at hsp
  simp only [allE] at hU hEF hPerm
  generalize hE : (accRounds s).toList.flatMap (·.entries) = E at hU hEF hPerm ⊢
  have hsp' := hsp.map (fun q => q.2.2.2)
  simp only [List.map_append, List.map_flatMap, List.map_map] at hsp'
  have hinit : cv.toList.map ((fun q : Nat × Nat × Nat × Nat => q.2.2.2) ∘ initPush) =
      (List.range cv.size).map (64 * ·) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < cv.size := by simpa using h1
    have := (hfa i hi).1
    rw [getElem!_pos cv i hi] at this
    simp [initPush, this, Nat.mul_comm]
  have hpu : ∀ rd : Gen.RoundD, rd.entries.flatMap (fun e => (pushN rd.T e).map (fun q => q.2.2.2)) =
      rd.entries.flatMap (fun e => if e.push then [e.eout + 1] else []) := by
    intro rd
    apply ZkFormal.Near.flatMap_congr'
    intro e _; unfold pushN; split <;> rfl
  have hR : (accRounds s).toList.flatMap (fun a => a.entries.map ((fun q : Nat × Nat × Nat × Nat => q.2.2.2) ∘
      fun e => (e.ts, a.K, a.z, e.ein))) = E.map (·.ein) := by
    rw [← hE, List.map_flatMap]; rfl
  have hL : (accRounds s).toList.flatMap (fun a => a.entries.flatMap (fun e => (pushN a.T e).map
      (fun q : Nat × Nat × Nat × Nat => q.2.2.2))) = E.flatMap (fun e => if e.push then [e.eout + 1] else []) := by
    rw [← hE, List.flatMap_assoc]
    apply ZkFormal.Near.flatMap_congr'
    intro rd _; exact hpu rd
  rw [hinit, hL, hR] at hsp'
  have hp : ∀ e ∈ E, e.push = true → e.eout % 64 + 1 < 64 := by
    intro e he hpe
    have hf := hEF e he
    have hm : cv[e.eout / 64]! ∈ cv.toList := by
      rw [getElem!_pos cv _ hf.hcid]; exact Array.getElem_mem_toList _
    have hb := hbd _ hm
    rw [hf.hpush] at hpe
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpe
    have := hf.hrem
    have := hf.hj
    omega
  have hnd := eout_nodup E cv.size (hPerm.trans hsp'.symm) hp
  have hnd2 : (usedV cv.toList (accUsed s)).Nodup := List.Pairwise.filter _ List.nodup_range
  have hperm : (E.map (·.eout)).Perm (usedV cv.toList (accUsed s)) := by
    apply (List.perm_ext_iff_of_nodup hnd hnd2).mpr
    intro v
    simp only [List.mem_map, usedV, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      Array.length_toList]
    constructor
    · rintro ⟨e, he, rfl⟩
      have hf := hEF e he
      refine ⟨by have := hf.hcid; omega, ?_, ?_⟩
      · rw [← arr_getD]; exact hf.hj
      · rw [hU]; simp only [hits, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]; exact ⟨e, he, rfl, rfl⟩
    · rintro ⟨-, -, hu⟩
      rw [hU] at hu
      simp only [hits, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨e, he, h1, h2⟩ := hu
      refine ⟨e, he, ?_⟩
      have := Nat.div_add_mod e.eout 64
      have := Nat.div_add_mod v 64
      omega
  have hmap : E.map incN = (E.map (·.eout)).map (incOf cv.toList) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    have hf := hEF e he
    simp only [Function.comp_apply, incN, incOf, ← arr_getD, hf.hinc, hf.hrem, hf.hs, hf.hr, hf.hlink]
  rw [hmap]
  exact hperm.map _

end ZkFormal.NearV3.Render.SchedRun
