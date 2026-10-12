import ZkFormal.NearV3.Render.SchedBusRunId

/-!
# Run-level `SFIN` identity: the memory's final values per segment
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Sched.Complete (finList)

/-- Budget logs carry `w = 0`. -/
def WZ (logs : Array (Array Gen.MOp)) : Prop := ∀ (i : Nat), ∀ o ∈ (logs[i]! : Array Gen.MOp).toList, (o : Gen.MOp).w = 0

theorem wz_modify (logs : Array (Array Gen.MOp)) (j : Nat) (o : Gen.MOp) (h : WZ logs) (ho : o.w = 0) :
    WZ (logs.modify j (·.push o)) := by
  intro i o' hm
  by_cases hi : i < logs.size
  · rw [getElem!_pos _ i (by simpa using hi)] at hm
    by_cases hij : j = i
    · subst hij
      rw [Array.getElem_modify_self] at hm
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact h j o' (by rw [getElem!_pos _ j hi]; exact hm)
      · exact ho
    · rw [Array.getElem_modify_of_ne hij] at hm
      exact h i o' (by rw [getElem!_pos _ i hi]; exact hm)
  · rw [getElem!_neg _ i (by simpa using hi)] at hm
    exact absurd hm (by simp [default, Array.toList]; exact Array.not_mem_empty _)

theorem wz_replicate (n : Nat) : WZ (Array.replicate n (#[] : Array Gen.MOp)) := by
  intro i o hm
  by_cases hi : i < n
  · rw [getElem!_pos _ i (by simpa using hi)] at hm; simp at hm
  · rw [getElem!_neg _ i (by simpa using hi)] at hm; exact absurd hm (by simp [default, Array.toList]; exact Array.not_mem_empty _)

theorem wz_entries (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat) (T : Nat) :
    ∀ (xs : List Nat) (a out : ProcActualReplayEntry.Acc), WZ a.2.2.2.2.2.1 → WZ a.2.2.2.2.2.2.1 →
      forIn xs a (ProcActualReplayEntry.step I cv rd sh T) = .ok out → WZ out.2.2.2.2.2.1 ∧ WZ out.2.2.2.2.2.2.1
  | [], a, out, h1, h2, h => by simp only [List.forIn_nil] at h; cases h; exact ⟨h1, h2⟩
  | x :: xs, a, out, h1, h2, h => by
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayEntry.step I cv rd sh T x a with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok nx =>
      obtain ⟨next, rfl, -, -, -⟩ :=
        ProcActualEntryTransition.step_effect I cv rd sh T x a nx (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he, bind, Except.bind] at h
      rcases a with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
      obtain ⟨e, oL, oS, oR, sb', rb', aa', gg', ps', rfl, -, -, rfl, rfl, -⟩ :=
        entry_effect I cv rd sh T x sb rb aa gg ol os orr ps used gi es next he
      exact wz_entries I cv rd sh T xs _ out (wz_modify _ _ _ h1 rfl) (wz_modify _ _ _ h2 rfl) h

theorem wz_rounds (I : Input) (cv : Array CReq) (key : List Nat) :
    ∀ (rs : List Round) (s out : ProcActualReplayRound.Acc), WZ s.2.2.2.2.2.1 → WZ s.2.2.2.2.2.2.1 →
      forIn rs s (ProcActualReplayRound.step I cv key) = .ok out → WZ out.2.2.2.2.2.1 ∧ WZ out.2.2.2.2.2.2.1
  | [], s, out, h1, h2, h => by simp only [List.forIn_nil] at h; cases h; exact ⟨h1, h2⟩
  | rd :: rs, s, out, h1, h2, h => by
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok nx =>
      obtain ⟨next, rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s nx he
      simp only [he, bind, Except.bind] at h
      rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs',gi⟩
      obtain ⟨sh, kend, col, eo, -, hent, -, rfl⟩ :=
        round_effect I cv key rd sb rb aa gg ol os orr ps bs tm kp kq zq used rs' gi next he
      have := wz_entries I cv rd sh tm _ _ eo h1 h2 hent
      exact wz_rounds I cv key rs _ out this.1 this.2 h

theorem wz_replay (I : Input) (cv : Array CReq) (rs : List Round) (out : ProcActualReplayRound.Acc)
    (h : ProcActualReplayFactor.replay I cv rs = .ok out) : WZ out.2.2.2.2.2.1 ∧ WZ out.2.2.2.2.2.2.1 := by
  unfold ProcActualReplayFactor.replay at h
  obtain ⟨ops, -, h⟩ := bind_ok h
  exact wz_rounds I cv _ rs _ out (wz_replicate _) (wz_replicate _) h

theorem shard_fin (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (k : Nat) (hk : k = 1 ∨ k = 2)
    (cur v0 : Array Nat) (logs : Array (Array Gen.MOp)) (x : Nat)
    (hlogs : logs = if k = 1 then s.2.2.2.2.2.1 else s.2.2.2.2.2.2.1)
    (hv0 : v0 = if k = 1 then (lpOf I).sb else (lpOf I).rb)
    (he : ProcActualMemoryFinal.Ends Gen.MOp.v v0 cur logs) (hw : WZ logs) (hx : x < logs.size) :
    [(ProcActualSegments.make I tau s k x).addr, (ProcActualSegments.make I tau s k x).vfin,
      (ProcActualSegments.make I tau s k x).wfin] = [addrOf tau k x, cur[x]!, 0] := by
  have hend := he.2 x hx
  have hw' := hw x
  rcases hk with rfl | rfl
  all_goals
    simp only [ProcActualSegments.make, Seg.vfin, Seg.wfin, lpOf] at hlogs hv0 ⊢
    simp only [show ¬ (1 : Nat) = 0 by decide, show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide,
      ite_true, ite_false] at hlogs hv0 ⊢
    subst hlogs hv0
    unfold ProcActualMemoryFinal.lastValue at hend
    cases hl : (_ : Array Gen.MOp).toList.getLast? <;> simp_all
  all_goals exact hw' _ (Array.mem_of_back? hl)

/-- **`SFIN` of one run**: per link the segment's final value and grant; per sender/receiver the
final budget of the process state and `0`. -/
theorem run_sfin (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    finList R.segs =
      (List.range (I.ids.length * I.ids.length)).map (fun l =>
          [addrOf tau 0 l, (R.segs.getD l default).vfin, (R.segs.getD l default).wfin]) ++
      (List.range I.ids.length).map (fun x => [addrOf tau 1 x, R.fin.sb[x]!, 0]) ++
      (List.range I.ids.length).map (fun x => [addrOf tau 2 x, R.fin.rb[x]!, 0]) := by
  obtain ⟨cv, st, rs, ev, s, gs, hpre, hrep, hb, -, hsegs, -, -, -, -, hfin, hck⟩ := run_decomp I tau R h
  obtain ⟨hcv, -⟩ := ProcActualAfterMemoryReduction.prefix_facts I cv st rs ev hpre
  obtain ⟨-, h2, h3, -, -, -⟩ := replay_ri I tau cv rs s hcv hrep
  have hinv := ProcActualMemoryFinal.replay_final I cv rs s hrep
  obtain ⟨-, -, hS, hR⟩ := hinv
  obtain ⟨wS, wR⟩ := wz_replay I cv rs s hrep
  simp only [Bool.and_eq_true, beq_iff_eq] at hck
  obtain ⟨⟨⟨hsb, hrb⟩, -⟩, -⟩ := hck
  have hrec := ProcActualMemoryFinal.build_records I tau s gs hb
  have hlk := ProcActualMemoryFinal.build_link I tau s gs hb
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs',gi⟩
  dsimp only [ProcActualReplayRound.entryAcc] at hS hR h2 h3 wS wR hsb hrb
  rw [hsegs, hrec, hfin]
  simp only [finList, List.map_append, List.map_map]
  congr 1; congr 1
  · apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply]
    rw [← hrec, hlk l hl']
    simp [ProcActualSegments.make]
  · apply List.map_congr_left
    intro x hx
    have hx' := List.mem_range.mp hx
    simp only [Function.comp_apply]
    rw [← hsb]
    exact shard_fin I tau _ 1 (Or.inl rfl) _ _ _ x (by simp) (by simp [lpOf]) hS wS (by omega)
  · apply List.map_congr_left
    intro x hx
    have hx' := List.mem_range.mp hx
    simp only [Function.comp_apply]
    rw [← hrb]
    exact shard_fin I tau _ 2 (Or.inr rfl) _ _ _ x (by simp) (by simp [lpOf]) hR wR (by omega)

end ZkFormal.NearV3.Render.SchedRun
