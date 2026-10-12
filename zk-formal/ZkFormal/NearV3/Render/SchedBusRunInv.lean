import ZkFormal.NearV3.Render.SchedBusRunEntry
import ZkFormal.NearV3.Candidates.ProcActualCoordinates

/-!
# Ghost invariants of the replay: memory logs, push log, bucket log as entry lists
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

/-- The `SOP` payload of op `o` at address `a` (= `sopOp g o` when `g.addr = a`). -/
def opMsg (a : Nat) (o : Gen.MOp) : List Nat := [a, o.t, o.op, o.vin, o.v, o.inc, b2n o.ok, b2n o.c]

def flat (A : Nat → Nat) (logs : Array (Array Gen.MOp)) : List (List Nat) :=
  (List.range logs.size).flatMap fun i => logs[i]!.toList.map (opMsg (A i))

def flatAll (τ : Nat) (ol os orr : Array (Array Gen.MOp)) : List (List Nat) :=
  flat (addrOf τ 0) ol ++ flat (addrOf τ 1) os ++ flat (addrOf τ 2) orr

theorem flatMap_perm_modify {α : Type} (g g' : Nat → List α) (i : Nat) (m : α)
    (h1 : g' i = g i ++ [m]) (h2 : ∀ j, j ≠ i → g' j = g j) :
    ∀ (l : List Nat), l.Nodup → i ∈ l → (l.flatMap g').Perm (l.flatMap g ++ [m])
  | [], _, hi => by simp at hi
  | a :: l, hl, hi => by
    rw [List.nodup_cons] at hl
    simp only [List.flatMap_cons]
    by_cases ha : a = i
    · subst ha
      have hr : l.flatMap g' = l.flatMap g := by
        apply ZkFormal.Near.flatMap_congr'
        intro j hj; exact h2 j (fun e => hl.1 (e ▸ hj))
      rw [h1, hr, List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · have hi' : i ∈ l := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm ha
        · exact h
      rw [h2 a ha, List.append_assoc]
      exact List.Perm.append_left _ (flatMap_perm_modify g g' i m h1 h2 l hl.2 hi')

theorem flat_modify (A : Nat → Nat) (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (hi : i < logs.size) :
    (flat A (logs.modify i (·.push o))).Perm (flat A logs ++ [opMsg (A i) o]) := by
  unfold flat
  rw [Array.size_modify]
  apply flatMap_perm_modify _ _ i _ ?_ ?_ _ List.nodup_range (List.mem_range.mpr hi)
  · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_modify_self, getElem!_pos _ i hi]
    simp
  · intro j hj
    by_cases hjs : j < logs.size
    · rw [getElem!_pos _ j (by simpa using hjs), Array.getElem_modify_of_ne (Ne.symm hj), getElem!_pos _ j hjs]
    · rw [getElem!_neg _ j (by simpa using hjs), getElem!_neg _ j hjs]

/-- The three `SOP` GRANT payloads of an entry of a round starting at `T`. -/
def grantN (τ T : Nat) (e : Entry) : List (List Nat) :=
  [[addrOf τ 1 e.s, T + e.x, OP_GRANT, e.sbIn, e.sbOut, e.inc, b2n e.ok, b2n e.cS],
   [addrOf τ 2 e.r, T + e.x, OP_GRANT, e.rbIn, e.rbOut, e.inc, b2n e.ok, b2n e.cR],
   [addrOf τ 0 e.link, T + e.x, OP_GRANT, e.alIn, e.alOut, e.inc, b2n e.ok, b2n e.cL]]

/-- The re-push of an entry. -/
def pushN (T : Nat) (e : Entry) : List (Nat × Nat × Nat × Nat) :=
  if e.push then [(T + e.x, e.alOut, e.zn, e.eout + 1)] else []

def EI (I : Input) (τ T : Nat) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (base : List (List Nat)) (basePs : List (Nat × Nat × Nat × Nat)) (a : ProcActualReplayEntry.Acc) : Prop :=
  a.2.2.2.2.1.size = I.ids.length * I.ids.length ∧ a.2.2.2.2.2.1.size = I.ids.length ∧
  a.2.2.2.2.2.2.1.size = I.ids.length ∧
  (flatAll τ a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1).Perm (base ++ a.2.2.2.2.2.2.2.2.2.2.toList.flatMap (grantN τ T)) ∧
  a.2.2.2.2.2.2.2.1.toList = basePs ++ a.2.2.2.2.2.2.2.2.2.2.toList.flatMap (pushN T) ∧
  ∀ i (hi : i < a.2.2.2.2.2.2.2.2.2.2.size), EntryOk cv rd sh i a.2.2.2.2.2.2.2.2.2.2[i]

theorem entry_inv (I : Input) (τ T : Nat) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (hco : ProcActualCoordinates.All I cv) (base : List (List Nat)) (basePs : List (Nat × Nat × Nat × Nat))
    (x : Nat) (a out : ProcActualReplayEntry.Acc) (ha : EI I τ T cv rd sh base basePs a)
    (hx : x = a.2.2.2.2.2.2.2.2.2.2.size)
    (h : ProcActualReplayEntry.step I cv rd sh T x a = .ok (.yield out)) :
    EI I τ T cv rd sh base basePs out ∧ out.2.2.2.2.2.2.2.2.2.2.size = x + 1 := by
  rcases a with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  obtain ⟨e, oL, oS, oR, sb', rb', aa', gg', ps', rfl, hps, he, rfl, rfl, hLt, hLop, hLvin, hLv, hLinc, hLok, hLc⟩ :=
    entry_effect I cv rd sh T x sb rb aa gg ol os orr ps used gi es out h
  subst hps
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  dsimp only at h1 h2 h3 h4 h5 h6 hx ⊢
  have hcm : cv[e.eout / 64]! ∈ cv.toList := by
    rw [getElem!_pos cv _ he.hcid]; exact Array.getElem_mem_toList _
  obtain ⟨hcs, hcr, hcl⟩ := hco _ hcm
  have hsn : e.s < I.ids.length := by rw [he.hs]; exact hcs
  have hrn : e.r < I.ids.length := by rw [he.hr]; exact hcr
  have hln : e.link < I.ids.length * I.ids.length := by
    rw [he.hlink, hcl]
    have := Nat.mul_le_mul_right I.ids.length (Nat.succ_le_of_lt hcs)
    rw [Nat.succ_mul] at this; omega
  refine ⟨⟨by simpa using h1, by simpa using h2, by simpa using h3, ?_, ?_, ?_⟩, by simp [hx]⟩
  · have pL := flat_modify (addrOf τ 0) ol e.link oL (by omega)
    have pS := flat_modify (addrOf τ 1) os e.s ⟨T + x, OP_GRANT, e.sbIn, e.sbOut, 0, 0, e.inc, e.ok, e.cS, e.cS⟩ (by omega)
    have pR := flat_modify (addrOf τ 2) orr e.r ⟨T + x, OP_GRANT, e.rbIn, e.rbOut, 0, 0, e.inc, e.ok, e.cR, e.cR⟩ (by omega)
    rw [List.perm_iff_count] at pL pS pR h4 ⊢
    intro m
    have eL := pL m; have eS := pS m; have eR := pR m; have e4 := h4 m
    simp only [flatAll, List.count_append] at eL eS eR e4 ⊢
    simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.count_append] at e4 ⊢
    have hm : opMsg (addrOf τ 0 e.link) oL = [addrOf τ 0 e.link, T + e.x, OP_GRANT, e.alIn, e.alOut, e.inc, b2n e.ok, b2n e.cL] := by
      simp only [opMsg, hLt, hLop, hLvin, hLv, hLinc, hLok, hLc, he.hx]
    rw [hm] at eL
    simp only [opMsg, he.hx] at eS eR
    simp only [grantN, List.count_cons, List.count_nil, he.hx] at eL eS eR e4 ⊢
    omega
  · dsimp only
    rw [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hpx := he.hx
    cases hp : e.push <;> simp [h5, hpx, pushN, hp]
  · intro i hi
    simp only [Array.size_push] at hi
    by_cases hi' : i < es.size
    · rw [Array.getElem_push_lt hi']; exact h6 i hi'
    · have : i = es.size := by omega
      subst this
      rw [Array.getElem_push_eq]
      rw [← hx]; exact he

theorem entry_loop (I : Input) (τ T : Nat) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (hco : ProcActualCoordinates.All I cv) (base : List (List Nat)) (basePs : List (Nat × Nat × Nat × Nat)) :
    ∀ (k a : Nat) (acc out : ProcActualReplayEntry.Acc), EI I τ T cv rd sh base basePs acc →
      acc.2.2.2.2.2.2.2.2.2.2.size = a →
      forIn (List.range' a k) acc (ProcActualReplayEntry.step I cv rd sh T) = .ok out →
      EI I τ T cv rd sh base basePs out ∧ out.2.2.2.2.2.2.2.2.2.2.size = a + k
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
      obtain ⟨hn, hsz⟩ := entry_inv I τ T cv rd sh hco base basePs a acc next ha hs.symm he
      have := entry_loop I τ T cv rd sh hco base basePs k (a + 1) next out hn hsz h
      exact ⟨this.1, by rw [this.2]; omega⟩

def RI (I : Input) (τ : Nat) (reads : List (List Nat)) (inits : List (Nat × Nat × Nat × Nat))
    (s : ProcActualReplayRound.Acc) : Prop :=
  s.2.2.2.2.1.size = I.ids.length * I.ids.length ∧ s.2.2.2.2.2.1.size = I.ids.length ∧
  s.2.2.2.2.2.2.1.size = I.ids.length ∧
  (flatAll τ s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1).Perm
    (reads ++ (accRounds s).toList.flatMap (fun rd => rd.entries.flatMap (grantN τ rd.T))) ∧
  (accPushes s).toList = inits ++ (accRounds s).toList.flatMap (fun rd => rd.entries.flatMap (pushN rd.T)) ∧
  (ProcActualPoppedLog.buckets s).toList =
    (accRounds s).toList.flatMap (fun rd => rd.entries.map (fun e => (e.ts, rd.K, rd.z, e.ein)))

set_option maxHeartbeats 1600000 in
theorem round_inv (I : Input) (τ : Nat) (cv : Array CReq) (key : List Nat) (rd : Round)
    (hco : ProcActualCoordinates.All I cv) (reads : List (List Nat)) (inits : List (Nat × Nat × Nat × Nat))
    (s out : ProcActualReplayRound.Acc) (hs : RI I τ reads inits s)
    (h : ProcActualReplayRound.step I cv key rd s = .ok (.yield out)) : RI I τ reads inits out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  obtain ⟨sh, kend, col, eo, hcol, hent, -, rfl⟩ := round_effect I cv key rd sb rb aa gg ol os orr ps bs tm kp kq zq used rs gi out h
  obtain ⟨htag, hcol'⟩ := collect_ok _ _ _ rd.bucket bs col hcol
  have h0 : EI I τ tm cv rd sh (flatAll τ ol os orr) ps.toList (sb,rb,aa,gg,ol,os,orr,ps,used,gi,(#[] : Array Entry)) := by
    obtain ⟨h1, h2, h3, -, -, -⟩ := hs
    refine ⟨h1, h2, h3, by simp, by simp, fun i hi => by simp at hi⟩
  have hl := entry_loop I τ tm cv rd sh hco _ _ rd.bucket.length 0 _ eo h0 rfl (by simpa [List.range_eq_range'] using hent)
  obtain ⟨⟨e1, e2, e3, e4, e5, e6⟩, esz⟩ := hl
  obtain ⟨-, -, -, h4, h5, h6⟩ := hs
  simp only [accRounds, accPushes, ProcActualPoppedLog.buckets] at h4 h5 h6
  refine ⟨e1, e2, e3, ?_, ?_, ?_⟩
  · simp only [accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ← List.append_assoc]
    exact e4.trans (List.Perm.append_right _ h4)
  · simp only [accPushes, accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ← List.append_assoc]
    rw [e5, h5]
  · simp only [ProcActualPoppedLog.buckets, accRounds, Array.toList_push, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hcol', h6]
    congr 1
    apply List.ext_getElem (by simp [esz])
    intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    simp only [List.length_map, Array.length_toList] at h1
    have hi : i < rd.bucket.length := by simpa using h1
    have hk := e6 i (by simpa using h2)
    have ht := htag rd.bucket[i] (List.getElem_mem hi)
    have hb : rd.bucket[i]! = rd.bucket[i] := getElem!_pos _ i hi
    rw [hk.hts, hk.hein, hb]
    simp [ProcPushConservation.stamp, ht.1, ht.2]

end ZkFormal.NearV3.Render.SchedRun
