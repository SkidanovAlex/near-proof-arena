import ZkFormal.NearV3.Render.SchedBusRunSinc

/-!
# Process-table (13) and memory-table (14) message lists of one run, in run-identity form

Field-level (`ProcBus.nf`) versions of the run identities, stated on the per-run lists of
`SchedBusProc` (`sopL`, `incL`, `pushRL`, `pushSL`) and `SchedBusMem` (`sopList`, `finList`).
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Render.ProcBus (nf sopL incL pushRL pushSL sopE incE pushRE pushSE)
open ZkFormal.NearV3.Sched.Complete (sopList finList)

/-- Field image of a push record `(ts, key, z, e)` as an `SPUSH` message `(τ, key, z, ts, e)`. -/
def pushF (τ : Nat) (q : Nat × Nat × Nat × Nat) : List ZkFormal.Algebra.Fp := nf [τ, q.2.1, q.2.2.1, q.1, q.2.2.2]

theorem sopE_eq (R : Run) (rd : Gen.RoundD) (e : Entry) : sopE R rd e = (grantN R.tau rd.T e).map nf := by
  simp [sopE, grantN, addrOf, Nat.mul_comm, Nat.add_assoc]

theorem sopL_eq (R : Run) : sopL R = (R.rounds.flatMap (fun rd => rd.entries.flatMap (grantN R.tau rd.T))).map nf := by
  simp only [sopL, List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  apply ZkFormal.Near.flatMap_congr'
  intro e _
  exact sopE_eq R rd e

theorem incL_eq (R : Run) : incL R = ((R.rounds.flatMap (·.entries)).map incN).map (fun l => nf (R.tau :: l)) := by
  simp only [incL, List.map_flatMap, List.map_map, List.flatMap_assoc]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  rw [← List.map_eq_flatMap]
  rfl

theorem pushRL_eq (R : Run) : pushRL R =
    (R.rounds.flatMap (fun rd => rd.entries.map (fun e => (e.ts, rd.K, rd.z, e.ein)))).map (pushF R.tau) := by
  simp only [pushRL, List.map_flatMap, List.map_map]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  rw [← List.map_eq_flatMap]
  rfl

theorem pushSL_eq (R : Run) (hp : ∀ rd ∈ R.rounds, ∀ e ∈ rd.entries, e.push = (e.ok && e.rem != 0)) : pushSL R =
    (R.rounds.flatMap (fun rd => rd.entries.flatMap (pushN rd.T))).map (pushF R.tau) := by
  simp only [pushSL, List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro rd hrd
  apply ZkFormal.Near.flatMap_congr'
  intro e he
  unfold pushSE pushN
  rw [hp rd hrd e he]
  by_cases hq : (e.ok && e.rem != 0) = true
  · have hq' : (e.ok && !(e.rem == 0)) = true := hq
    simp only [hq, hq', ite_true, List.map_cons, List.map_nil, pushF]
  · have hq' : ¬ (e.ok && !(e.rem == 0)) = true := hq
    simp only [hq, hq', ite_false, List.map_nil, Bool.false_eq_true]

/-- **`SPUSH`, one run, field form**: initial pushes ++ process re-pushes ~ process bucket receives. -/
theorem run_push_field (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ∀ rd ∈ R.rounds, ∀ e ∈ rd.entries, e.push = (e.ok && e.rem != 0) := by
  obtain ⟨cv, st, rs, ev, s, gs, hpre, hrep, -, -, -, hrd, -⟩ := run_decomp I tau R h
  obtain ⟨-, -, -, hEF, -⟩ := si_replay I cv rs s hrep
  intro rd hr e he
  rw [hrd] at hr
  exact (hEF e (List.mem_flatMap.mpr ⟨rd, hr, he⟩)).hpush

theorem run_spush_fp (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ((R.conv.map initPush).map (pushF R.tau) ++ pushSL R).Perm (pushRL R) := by
  rw [pushSL_eq R (run_push_field I tau R h), pushRL_eq, ← List.map_append]
  exact (run_spush I tau R h).map _

/-- **`SINC`, one run, field form.** -/
theorem run_sinc_fp (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    (incL R).Perm ((usedV R.conv R.used).map (fun v => nf (R.tau :: incOf R.conv v))) := by
  rw [incL_eq]
  have := (run_sinc I tau R h).map (fun l => nf (R.tau :: l))
  simpa only [List.map_map, Function.comp_def] using this

/-- **`SOP`, one run, field form**: memory receives = INITs ++ reads ++ process GRANTs. -/
theorem run_sop_fp (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ((sopList R.segs).map nf).Perm
      (((List.range (I.ids.length * I.ids.length)).map (fun l => [addrOf tau 0 l, 0, OP_INIT,
          b2n I.allowed[l]!, (lpOf I).a2[l]!, (lpOf I).g2[l]!, 0, 1]) ++
       (List.range I.ids.length).map (fun x => [addrOf tau 1 x, 0, OP_INIT, 0, (lpOf I).sb[x]!, 0, 0, 0]) ++
       (List.range I.ids.length).map (fun x => [addrOf tau 2 x, 0, OP_INIT, 0, (lpOf I).rb[x]!, 0, 0, 0]) ++
       R.conv.map (readMsg tau (lpOf I).a2)).map nf ++ sopL R) := by
  have ht : R.tau = tau := (ProcActualRunProjection.run_fields I tau R h).1
  rw [sopL_eq, ht, ← List.map_append]
  exact (run_sop I tau R h).map _

end ZkFormal.NearV3.Render.SchedRun
