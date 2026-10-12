import ZkFormal.NearV3.Candidates.ProcActualReplayFactor
import ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
import ZkFormal.NearV3.Render.ChachaReplay

/-!
# ZkFormal.NearV3.Render.ChachaRun — what a native scheduler run guarantees about its shuffles

From `ActualRun.run I τ = .ok R` (through its factored form `runPrefix` / `replay` / `finish`):

* `entry_step`, `entries_inv`: the entry loop of a round stores `ein = bucket[x].v`,
  `eout = sh[x]` (the replayed shuffle) and checks `sh[x] / 64 < |conv|`;
* `round_step`, `replay_inv`: every stored round satisfies `RoundOk` (its replay
  `replayShuffle key kst (ein list) = .ok (eout list, kend)`, the request-index bound, `|entries| = Lr`,
  `1 ≤ Lr < 16384`) and the rounds carry the cursor chain `ProcActualReplayChain.Stamped`;
* `finish_kpos`, `finish_fields`: the final stream position is checked against the process state;
* **`run_rounds`**: the process state is `R.fin`, `R.kfin = rngPos R.fin.rng`, `R.key = leWords seed`,
  `Stamped _ R.kfin _ _ R.rounds`, and every round is `RoundOk`.
-/
namespace ZkFormal.NearV3.Render.ChachaBus
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

def EInv (nc : Nat) (rd : Round) (sh : List Nat) (n : Nat) (acc : ProcActualReplayEntry.Acc) : Prop :=
  acc.2.2.2.2.2.2.2.2.2.2.size = n ∧ ∀ i, i < n →
    (acc.2.2.2.2.2.2.2.2.2.2[i]!).ein = (rd.bucket[i]!).v ∧
    (acc.2.2.2.2.2.2.2.2.2.2[i]!).eout = sh[i]! ∧ sh[i]! / 64 < nc

theorem einv_push {nc : Nat} {rd : Round} {sh : List Nat} {n : Nat} {ents : Array Entry}
    (h : ents.size = n ∧ ∀ i, i < n → (ents[i]!).ein = (rd.bucket[i]!).v ∧ (ents[i]!).eout = sh[i]! ∧
      sh[i]! / 64 < nc)
    (e : Entry) (h1 : e.ein = (rd.bucket[n]!).v) (h2 : e.eout = sh[n]!) (hc : sh[n]! / 64 < nc) :
    (ents.push e).size = n + 1 ∧ ∀ i, i < n + 1 → ((ents.push e)[i]!).ein = (rd.bucket[i]!).v ∧
      ((ents.push e)[i]!).eout = sh[i]! ∧ sh[i]! / 64 < nc := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases hl : i < n
  · rw [getElem!_pos (ents.push e) i (by simp; omega), Array.getElem_push_lt (by omega),
      ← getElem!_pos ents i (by omega)]
    exact h.2 i hl
  · have : i = n := by omega
    subst this
    have hs : ents.size = i := h.1
    rw [getElem!_pos (ents.push e) _ (by simp; omega)]
    simp only [Array.getElem_push, hs, Nat.lt_irrefl, dite_false]
    exact ⟨h1, h2, hc⟩

theorem step_cid {I : Input} {conv : Array CReq} {rd : Round} {sh : List Nat} {T i : Nat}
    {acc : ProcActualReplayEntry.Acc} {s : ForInStep ProcActualReplayEntry.Acc}
    (hs : ProcActualReplayEntry.step I conv rd sh T i acc = .ok s) : sh[i]! / 64 < conv.size := by
  obtain ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,ents⟩ := acc
  unfold ProcActualReplayEntry.step at hs
  simp only [bind, Except.bind, pure, Except.pure, check] at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · rename_i heq
      split at heq
      · exact of_decide_eq_true ‹_›
      · cases heq

set_option maxHeartbeats 1000000 in
theorem entry_step (I : Input) (conv : Array CReq) (rd : Round) (sh : List Nat) (T i : Nat)
    (acc : ProcActualReplayEntry.Acc) (hacc : EInv conv.size rd sh i acc) (s : ForInStep ProcActualReplayEntry.Acc)
    (hs : ProcActualReplayEntry.step I conv rd sh T i acc = .ok s) :
    ∃ b', s = .yield b' ∧ EInv conv.size rd sh (i + 1) b' := by
  have hcid := step_cid hs
  obtain ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,ents⟩ := acc
  unfold ProcActualReplayEntry.step at hs
  simp only [bind, Except.bind, pure, Except.pure, check] at hs
  repeat (first | split at hs | cases hs)
  all_goals first
    | (refine ⟨_, rfl, ?_⟩; exact einv_push hacc _ rfl rfl hcid)
    | (cases hs; refine ⟨_, rfl, ?_⟩; exact einv_push hacc _ rfl rfl hcid)

theorem entries_inv (I : Input) (conv : Array CReq) (rd : Round) (sh : List Nat) (T L : Nat)
    (acc out : ProcActualReplayEntry.Acc) (h0 : acc.2.2.2.2.2.2.2.2.2.2 = #[])
    (h : forIn (List.range L) acc (ProcActualReplayEntry.step I conv rd sh T) = .ok out) :
    EInv conv.size rd sh L out :=
  ExceptRange.range_invariant _ (EInv conv.size rd sh) L
    (fun i _ b hb s hs => entry_step I conv rd sh T i b hb s hs) acc out
    (by simp [EInv, h0]) h

/-- What the replay guarantees for one round. -/
structure RoundOk (key : List Nat) (nc : Nat) (rd : Gen.RoundD) : Prop where
  replay : replayShuffle key rd.kst (rd.entries.map (·.ein)) = .ok (rd.entries.map (·.eout), rd.kend)
  cid : ∀ e ∈ rd.entries, e.eout / 64 < nc
  len : rd.entries.length = rd.Lr
  L_pos : 1 ≤ rd.Lr
  L_lt : rd.Lr < 16384

abbrev Acc := ProcActualReplayChain.ReplayAcc

theorem ents_map {nc : Nat} {rd : Round} {sh : List Nat} {out : ProcActualReplayEntry.Acc}
    (he : EInv nc rd sh rd.bucket.length out) (_h : True) (hlen : sh.length = rd.bucket.length) :
    out.2.2.2.2.2.2.2.2.2.2.toList.map (·.ein) = rd.bucket.map (·.v) ∧
      out.2.2.2.2.2.2.2.2.2.2.toList.map (·.eout) = sh := by
  obtain ⟨h1, h2⟩ := he
  constructor
  · apply List.ext_getElem (by simp [h1])
    intro i hi _
    simp only [List.length_map, Array.length_toList] at hi
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos _ i hi, (h2 i (by omega)).1, getElem!_pos rd.bucket i (by omega)]
  · apply List.ext_getElem (by simp [h1, hlen])
    intro i hi _
    simp only [List.length_map, Array.length_toList] at hi
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos _ i hi, (h2 i (by omega)).2.1, getElem!_pos sh i (by omega)]

def RInv (key : List Nat) (nc : Nat) (s : Acc) : Prop :=
  ProcActualReplayChain.Stamped s.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2.1
    s.2.2.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList ∧
  ∀ rd ∈ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList, RoundOk key nc rd

set_option maxHeartbeats 1000000 in
theorem round_step (I : Input) (conv : Array CReq) (key : List Nat) (rd : Round) (acc : Acc)
    (hacc : RInv key conv.size acc) (s : ForInStep Acc)
    (hs : ProcActualReplayRound.step I conv key rd acc = .ok s) :
    ExceptLoop.StepInv (RInv key conv.size) s := by
  obtain ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩ := acc
  unfold ProcActualReplayRound.step at hs
  simp only [bind, Except.bind, pure, Except.pure, check] at hs
  repeat (first | split at hs | cases hs)
  rename_i x5 v5 hsz x4 shk hrep x3 v3 hsh x2 v2 hst x1 col hcol x out hent
  obtain ⟨sh, kend⟩ := shk
  have he := entries_inv I conv rd sh T _ _ out rfl hent
  have hL : 1 ≤ rd.bucket.length ∧ rd.bucket.length < 16384 := by
    split at hsz
    · rename_i hc; simpa using hc
    · cases hsz
  obtain ⟨-, hsh, -⟩ := replay_inst 0 key kpos _ sh kend hrep
  have hlen : sh.length = rd.bucket.length := by
    rw [hsh, final_length]; simp [sinstOf, ZkFormal.Chacha.Shuffle.Gen.SInst.L]
  obtain ⟨m1, m2⟩ := ents_map he trivial hlen
  refine ⟨?_, ?_⟩
  · simp only [Array.toList_push]
    exact ProcActualReplayChain.Stamped.snoc hacc.1 _ _ _ _ _
  · intro r hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hacc.2 r hr
    · refine ⟨?_, ?_, ?_, hL.1, hL.2⟩
      · show replayShuffle key kpos _ = _
        rw [m1, m2]; exact hrep
      · intro e hmem
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        simp only [Array.length_toList] at hi
        have := (he.2 i (by rw [← he.1]; exact hi)).2
        rw [Array.getElem_toList, ← getElem!_pos _ i hi, this.1]
        exact this.2
      · simp [he.1]

theorem finish_kpos {I : Input} {tau : Nat} {cv : Array CReq} {st : PState} {acc : Acc} {R : Run}
    (h : ProcActualReplayFactor.finish I tau cv st acc = .ok R) :
    acc.2.2.2.2.2.2.2.2.2.2.1 = rngPos st.rng := by
  obtain ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩ := acc
  unfold ProcActualReplayFactor.finish at h
  simp only [bind, Except.bind, pure, Except.pure, check] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i heq
        split at heq
        · rename_i hc; simpa using hc
        · cases heq

set_option maxHeartbeats 2000000 in
theorem finish_fields {I : Input} {tau : Nat} {cv : Array CReq} {st : PState} {acc : Acc} {R : Run}
    (h : ProcActualReplayFactor.finish I tau cv st acc = .ok R) :
    R.rounds = acc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList ∧ R.kfin = acc.2.2.2.2.2.2.2.2.2.2.1 ∧
      R.fin = st ∧ R.key = NearSpecV3.leWords I.seed ∧ R.conv = cv.toList := by
  obtain ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩ := acc
  unfold ProcActualReplayFactor.finish at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (first | split at h | cases h)
  all_goals first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | (cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem replay_inv {I : Input} {cv : Array CReq} {rs : List Round} {acc : Acc}
    (h : ProcActualReplayFactor.replay I cv rs = .ok acc) :
    RInv (NearSpecV3.leWords I.seed) cv.size acc := by
  unfold ProcActualReplayFactor.replay at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ops _
    refine ExceptLoop.invariant rs _ (RInv (NearSpecV3.leWords I.seed) cv.size)
      (fun rd _ b hb s hs => round_step I cv _ rd b hb s hs) _ acc ?_ h
    exact ⟨ProcActualReplayChain.Stamped.nil, by simp [ProcActualReplayInitial.initial]⟩

/-- **The run's rounds**: the process state, the final stream position, the cursor chain and the
per-round replay. -/
theorem run_rounds (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    (∃ rs, ProcActualInput.process I = .ok (R.fin, rs)) ∧ R.kfin = rngPos R.fin.rng ∧
      R.key = NearSpecV3.leWords I.seed ∧
      (∃ T Kq zq, ProcActualReplayChain.Stamped T R.kfin Kq zq R.rounds) ∧
      ∀ rd ∈ R.rounds, RoundOk R.key R.conv.length rd := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  cases hp : ProcActualPrefix.runPrefix I with
  | error e => rw [hp] at h; cases h
  | ok x =>
    obtain ⟨cv, st, rs, ev⟩ := x
    rw [hp] at h
    change ProcActualRunFactor.runRest I tau cv st rs = .ok R at h
    have hpf := (ProcActualAfterMemoryReduction.prefix_facts I cv st rs ev hp).2
    rw [ProcActualEntryFactor.rest_eq, ProcActualRoundFactor.rest_eq, ProcActualReplayFactor.rest_eq] at h
    cases hr : ProcActualReplayFactor.replay I cv rs with
    | error e => rw [hr] at h; cases h
    | ok acc =>
      rw [hr] at h
      change ProcActualReplayFactor.finish I tau cv st acc = .ok R at h
      have hinv := replay_inv hr
      obtain ⟨h1, h2, h3, h4, h5⟩ := finish_fields h
      have hk := finish_kpos h
      refine ⟨⟨rs, by rw [h3]; exact hpf⟩, by rw [h2, hk, h3], h4, ⟨_, _, _, by rw [h1, h2]; exact hinv.1⟩, ?_⟩
      rw [h1, h4, h5, Array.length_toList]
      exact hinv.2
end ZkFormal.NearV3.Render.ChachaBus
