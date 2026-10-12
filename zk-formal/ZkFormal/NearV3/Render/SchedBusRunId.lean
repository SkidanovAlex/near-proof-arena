import ZkFormal.NearV3.Render.SchedBusRunInv
import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
import ZkFormal.NearV3.Candidates.ProcActualInitialPush

/-!
# Run-level identities of one successful `ActualRun.run`: `SOP` and `SPUSH`
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Sched.Complete (sopOp sopList sopInit finList)

theorem rounds_inv (I : Input) (τ : Nat) (cv : Array CReq) (key : List Nat) (hco : ProcActualCoordinates.All I cv)
    (reads : List (List Nat)) (inits : List (Nat × Nat × Nat × Nat)) :
    ∀ (rs : List Round) (s out : ProcActualReplayRound.Acc), RI I τ reads inits s →
      forIn rs s (ProcActualReplayRound.step I cv key) = .ok out → RI I τ reads inits out
  | [], s, out, hs, h => by simp only [List.forIn_nil] at h; cases h; exact hs
  | rd :: rs, s, out, hs, h => by
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok nx =>
      obtain ⟨next, rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s nx he
      simp only [he, bind, Except.bind] at h
      exact rounds_inv I τ cv key hco reads inits rs next out (round_inv I τ cv key rd hco reads inits s next hs he) h

/-- The `SOP` payload of the conversion read of request `c`. -/
def readMsg (τ : Nat) (a2 : Array Nat) (c : CReq) : List Nat :=
  [addrOf τ 0 c.link, c.cid + 1, OP_READ, a2[c.link]!, a2[c.link]!, 0, 0, 0]

/-- The initial push of request `c`. -/
def initPush (c : CReq) : Nat × Nat × Nat × Nat := (c.cid, c.key, if c.key = 0 then 1 else 0, c.cid * 64)

theorem reads_inv (τ : Nat) (aa gg : Array Nat) (n : Nat) (cv : List CReq) (hc : ∀ c ∈ cv, c.link < n) :
    ∀ (cs : List CReq) (ops out : Array (Array Gen.MOp)) (acc : List (List Nat)), (∀ c ∈ cs, c ∈ cv) →
      ops.size = n → (flat (addrOf τ 0) ops).Perm acc →
      forIn cs ops (ProcActualReplayFactor.readStep aa gg) = .ok out →
      out.size = n ∧ (flat (addrOf τ 0) out).Perm (acc ++ cs.map (readMsg τ aa))
  | [], ops, out, acc, _, hs, hp, h => by
    simp only [List.forIn_nil] at h; cases h; exact ⟨hs, by simpa using hp⟩
  | c :: cs, ops, out, acc, hm, hs, hp, h => by
    rw [List.forIn_cons] at h
    simp only [ProcActualReplayFactor.readStep, bind, Except.bind] at h
    have hl := hc c (hm c (by simp))
    have hpm := flat_modify (addrOf τ 0) ops c.link
      ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩ (by omega)
    have := reads_inv τ aa gg n cv hc cs _ out (acc ++ [readMsg τ aa c]) (fun x hx => hm x (by simp [hx]))
      (by simp [hs]) (hpm.trans (List.Perm.append_right _ hp)) h
    refine ⟨this.1, ?_⟩
    simpa using this.2

theorem flat_replicate (A : Nat → Nat) (n : Nat) : flat A (Array.replicate n (#[] : Array Gen.MOp)) = [] := by
  unfold flat
  apply List.flatMap_eq_nil_iff.mpr
  intro i hi
  have hi' : i < n := by simpa using hi
  rw [getElem!_pos _ i (by simpa using hi')]
  simp

/-- The link pass of a run input. -/
def lpOf (I : Input) : LinkPass := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)

theorem replay_ri (I : Input) (τ : Nat) (cv : Array CReq) (rs : List Round) (out : ProcActualReplayRound.Acc)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I) = .ok cv)
    (h : ProcActualReplayFactor.replay I cv rs = .ok out) :
    RI I τ (cv.toList.map (readMsg τ (lpOf I).a2)) (cv.toList.map initPush) out := by
  have hco := ProcActualCoordinates.loop_facts I cv hcv
  unfold ProcActualReplayFactor.replay at h
  obtain ⟨ops, hop, h⟩ := bind_ok h
  rw [← Array.forIn_toList] at hop
  have hl : ∀ c ∈ cv.toList, c.link < I.ids.length * I.ids.length := by
    intro c hc
    obtain ⟨hcs, hcr, hcl⟩ := hco c hc
    rw [hcl]
    have := Nat.mul_le_mul_right I.ids.length (Nat.succ_le_of_lt hcs)
    rw [Nat.succ_mul] at this; omega
  obtain ⟨hsz, hp⟩ := reads_inv τ _ _ _ cv.toList hl cv.toList _ ops [] (fun _ h => h) (by simp)
    (by rw [flat_replicate]) hop
  apply rounds_inv I τ cv _ hco _ _ rs _ out ?_ h
  refine ⟨hsz, by simp [ProcActualReplayInitial.initial], by simp [ProcActualReplayInitial.initial], ?_, ?_, ?_⟩
  · simp only [ProcActualReplayInitial.initial, flatAll, flat_replicate, List.append_nil, accRounds]
    simpa [lpOf] using hp
  · simp [ProcActualReplayInitial.initial, accPushes, accRounds, initPush]
  · simp [ProcActualReplayInitial.initial, ProcActualPoppedLog.buckets, accRounds]

theorem run_ri (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ∃ cv s gs, R.conv = cv.toList ∧ R.segs = gs.toList ∧ R.rounds = (accRounds s).toList ∧ R.used = accUsed s ∧
      forIn I.raw #[] (ProcActualConverted.step I) = .ok cv ∧
      ProcActualSegments.build I tau s = .ok gs ∧
      (sortPush (accPushes s).toList == sortPush (ProcActualPoppedLog.buckets s).toList) = true ∧
      RI I tau (cv.toList.map (readMsg tau (lpOf I).a2)) (cv.toList.map initPush) s := by
  obtain ⟨cv, st, rs, ev, s, gs, hpre, hrep, hb, hck, hsegs, hrd, hused, hconv, -, -⟩ := run_decomp I tau R h
  obtain ⟨hcv, -⟩ := ProcActualAfterMemoryReduction.prefix_facts I cv st rs ev hpre
  exact ⟨cv, s, gs, hconv, hsegs, hrd, hused, hcv, hb, hck, replay_ri I tau cv rs s hcv hrep⟩

/-- **`SPUSH` of one run**: initial pushes and re-pushes are the popped bucket records. -/
theorem run_spush (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    (R.conv.map initPush ++ R.rounds.flatMap (fun rd => rd.entries.flatMap (pushN rd.T))).Perm
      (R.rounds.flatMap (fun rd => rd.entries.map (fun e => (e.ts, rd.K, rd.z, e.ein)))) := by
  obtain ⟨cv, s, gs, hconv, -, hrd, -, -, -, hck, hri⟩ := run_ri I tau R h
  obtain ⟨-, -, -, -, h5, h6⟩ := hri
  have he : sortPush (accPushes s).toList = sortPush (ProcActualPoppedLog.buckets s).toList := by
    simpa using hck
  have hp := ((ProcQsortPermutation.sortPush_perm _).symm.trans (he ▸ ProcQsortPermutation.sortPush_perm _))
  rw [h5, h6] at hp
  rw [hconv, hrd]
  exact hp.symm

theorem seg_ops (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (k i : Nat) :
    (ProcActualSegments.make I tau s k i).ops.map (sopOp (ProcActualSegments.make I tau s k i)) =
      (if k = 0 then s.2.2.2.2.1[i]! else if k = 1 then s.2.2.2.2.2.1[i]! else s.2.2.2.2.2.2.1[i]!).toList.map
        (opMsg (addrOf tau (if k = 0 then 0 else if k = 1 then 1 else 2) i)) := by
  unfold ProcActualSegments.make
  split <;> (try split) <;> simp_all [sopOp, opMsg]

theorem flat_range (A : Nat → Nat) (logs : Array (Array Gen.MOp)) (n : Nat) (hn : logs.size = n) :
    (List.range n).flatMap (fun i => logs[i]!.toList.map (opMsg (A i))) = flat A logs := by
  rw [← hn]; rfl

/-- **`SOP` of one run**: the memory receives the link/shard INITs, the conversion reads and three
GRANTs per processed entry. -/
theorem run_sop (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    (sopList R.segs).Perm
      ((List.range (I.ids.length * I.ids.length)).map (fun l => [addrOf tau 0 l, 0, OP_INIT,
          b2n I.allowed[l]!, (lpOf I).a2[l]!, (lpOf I).g2[l]!, 0, 1]) ++
       (List.range I.ids.length).map (fun x => [addrOf tau 1 x, 0, OP_INIT, 0, (lpOf I).sb[x]!, 0, 0, 0]) ++
       (List.range I.ids.length).map (fun x => [addrOf tau 2 x, 0, OP_INIT, 0, (lpOf I).rb[x]!, 0, 0, 0]) ++
       R.conv.map (readMsg tau (lpOf I).a2) ++
       R.rounds.flatMap (fun rd => rd.entries.flatMap (grantN tau rd.T))) := by
  obtain ⟨cv, s, gs, hconv, hsegs, hrd, -, -, hb, -, hri⟩ := run_ri I tau R h
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hri
  rw [hsegs, ProcActualMemoryFinal.build_records I tau s gs hb, hconv, hrd]
  have e0 := flat_range (addrOf tau 0) s.2.2.2.2.1 _ h1
  have e1 := flat_range (addrOf tau 1) s.2.2.2.2.2.1 _ h2
  have e2 := flat_range (addrOf tau 2) s.2.2.2.2.2.2.1 _ h3
  rw [List.perm_iff_count] at h4 ⊢
  intro m
  have c4 := h4 m
  have hcnt : ∀ k (l : List Nat), (sopList (l.map (ProcActualSegments.make I tau s k))).count m =
      (l.map (fun i => sopInit (ProcActualSegments.make I tau s k i))).count m +
      (l.flatMap (fun i => (ProcActualSegments.make I tau s k i).ops.map
        (sopOp (ProcActualSegments.make I tau s k i)))).count m := by
    intro k l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [sopList, List.map_cons, List.flatMap_cons, List.count_cons, List.count_append] at ih ⊢
      omega
  have hops : ∀ k (l : List Nat), (l.flatMap (fun i => (ProcActualSegments.make I tau s k i).ops.map
        (sopOp (ProcActualSegments.make I tau s k i)))) = l.flatMap (fun i =>
      (if k = 0 then s.2.2.2.2.1[i]! else if k = 1 then s.2.2.2.2.2.1[i]! else s.2.2.2.2.2.2.1[i]!).toList.map
        (opMsg (addrOf tau (if k = 0 then 0 else if k = 1 then 1 else 2) i))) := by
    intro k l
    apply ZkFormal.Near.flatMap_congr'
    intro i _; exact seg_ops I tau s k i
  have hini : ∀ k (l : List Nat), l.map (fun i => sopInit (ProcActualSegments.make I tau s k i)) =
      l.map (fun i => if k = 0 then [addrOf tau 0 i, 0, OP_INIT, b2n I.allowed[i]!, (lpOf I).a2[i]!, (lpOf I).g2[i]!, 0, 1]
        else if k = 1 then [addrOf tau 1 i, 0, OP_INIT, 0, (lpOf I).sb[i]!, 0, 0, 0]
        else [addrOf tau 2 i, 0, OP_INIT, 0, (lpOf I).rb[i]!, 0, 0, 0]) := by
    intro k l
    apply List.map_congr_left
    intro i _
    unfold ProcActualSegments.make
    split <;> (try split) <;> simp_all [sopInit, lpOf, b2n]
  have ha : ∀ (a b c : List (ZkFormal.NearV3.Sched.Gen.Seg)), sopList (a ++ b ++ c) = sopList a ++ sopList b ++ sopList c := by
    intro a b c; simp [sopList, List.flatMap_append]
  rw [ha, List.count_append, List.count_append, hcnt, hcnt, hcnt, hops, hops, hops, hini, hini, hini]
  simp only [flatAll, List.count_append, ite_true, show ¬ (1 : Nat) = 0 by decide, ite_false,
    show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide] at c4 ⊢
  rw [e0, e1, e2]
  omega

end ZkFormal.NearV3.Render.SchedRun
