import ZkFormal.NearV3.Render.SchedBusSsd

/-!
# The distribute rows of one run as an explicit functional model

`cells i st m`: the first `m` grid cells of sender position `i` from the receiver endpoints `ri` and
the sender endpoint `se` (exactly `cellStep`'s state updates), as descriptors, with the grid grants
array `gb`; `grid m`: `m` sender positions (header, then `n` cells each).  `dist_rows`: for a run with a
successful `distRows`, the emitted rows are the shard rows of both sides, then `grid n`'s descriptors,
and the returned grants array is `grid n`'s.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd
open ProcDistGeneratorFactor ProcDistCellBridge NearSpecV3.Scheduler

section
variable (I : Input) (R : Run)

/-- Grid state: descriptors so far, grants array, receiver endpoints, sender endpoint. -/
abbrev GS := List Desc × Array Nat × Array (Nat × Nat) × (Nat × Nat)

def cstep (i : Nat) (st : GS) (j : Nat) : GS :=
  let rr := receiver I R j
  let re := st.2.2.1[rr]!
  let al := cAl I R i j
  let se := st.2.2.2
  let g := ProcDistCellRow.grant al se.1 se.2 re.1 re.2
  (st.1 ++ [.cell I.ids R.tau R.n i j (sender I R i) rr se.1 se.2 re.1 re.2 al],
   if al then st.2.1.set! (sender I R i * R.n + rr) g else st.2.1,
   st.2.2.1.set! rr (re.1 - b2n al, re.2 - g),
   (se.1 - b2n al, se.2 - g))

def cells (i : Nat) (st : GS) (m : Nat) : GS := (List.range m).foldl (cstep I R i) st

def gstep (st : GS) (i : Nat) : GS :=
  let sv := sender I R i
  cells I R i (st.1 ++ [hdrD I R i], st.2.1, st.2.2.1, (cntS R.n I.allowed sv, R.fin.sb[sv]!)) R.n

def ri0 : Array (Nat × Nat) := (List.range R.n).toArray.map fun r => (cntR R.n I.allowed r, R.fin.rb[r]!)

def grid (m : Nat) : GS := (List.range m).foldl (gstep I R) ([], Array.replicate (R.n * R.n) 0, ri0 I R, (0, 0))

theorem cells_succ (i : Nat) (st : GS) (m : Nat) : cells I R i st (m + 1) = cstep I R i (cells I R i st m) m := by
  simp [cells, List.range_succ, List.foldl_append]

theorem grid_succ (m : Nat) : grid I R (m + 1) = gstep I R (grid I R m) m := by
  simp [grid, List.range_succ, List.foldl_append]

theorem cell_step_gb (i j : Nat) (acc : CellAcc) (o : ForInStep CellAcc) (h : cellStep I R i j acc = .ok o) :
    ∃ out, o = .yield out ∧ out.2.2.1 = if cAl I R i j then acc.2.2.1.set! (sender I R i * R.n + receiver I R j)
      (ProcDistCellRow.grant (cAl I R i j) acc.2.2.2.2.1 acc.2.2.2.2.2
        (acc.2.2.2.1[receiver I R j]!).1 (acc.2.2.2.1[receiver I R j]!).2) else acc.2.2.1 := by
  by_cases hal : cAl I R i j = true
  · unfold cellStep at h
    dsimp only at h
    unfold cAl at hal
    dsimp only [sender, receiver] at hal
    simp only [hal, ite_true] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨_, rfl, ?_⟩
      simp only [cAl, sender, receiver, hal, ProcDistCellRow.grant, ite_true]
  · have hf : cAl I R i j = false := by simpa using hal
    unfold cellStep at h
    dsimp only at h
    unfold cAl at hf
    dsimp only [sender, receiver] at hf
    simp only [hf, Bool.false_eq_true, ite_false] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [cAl, sender, receiver, hf, Bool.false_eq_true, ite_false]

/-- The cell loop of sender position `i` is `cells`. -/
theorem cell_loop (i : Nat) (acc out : CellAcc) (h : forIn (List.range R.n) acc (cellStep I R i) = .ok out) :
    ∃ ds, out.1.toList = acc.1.toList ++ ds.map Desc.row ∧
      cells I R i ([], acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2) R.n = (ds, out.2.2.1, out.2.2.2.1, out.2.2.2.2) := by
  have := ExceptRange.range_invariant (cellStep I R i)
    (fun k (s : CellAcc) => ∃ ds, s.1.toList = acc.1.toList ++ ds.map Desc.row ∧
      cells I R i ([], acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2) k = (ds, s.2.2.1, s.2.2.2.1, s.2.2.2.2)) R.n
    (fun k _ s hs o ho => by
      obtain ⟨ds, hrows, hst⟩ := hs
      obtain ⟨out, rfl, h1, h2, h3, _⟩ := cell_step I R i k s o ho
      obtain ⟨out', ho', hg⟩ := cell_step_gb I R i k s _ ho
      cases ho'
      refine ⟨out, rfl, ds ++ [.cell I.ids R.tau R.n i k (sender I R i) (receiver I R k) s.2.2.2.2.1 s.2.2.2.2.2
        (s.2.2.2.1[receiver I R k]!).1 (s.2.2.2.1[receiver I R k]!).2 (cAl I R i k)], ?_, ?_⟩
      · rw [h1, Array.toList_push, hrows]; simp; rfl
      · rw [cells_succ, hst, h2, h3, hg]
        rfl)
    _ out ⟨[], by simp, rfl⟩ h
  exact this

theorem cells_app (i : Nat) (L : List Desc) (g : Array Nat) (ri : Array (Nat × Nat)) (se : Nat × Nat) :
    ∀ m, cells I R i (L, g, ri, se) m =
      (L ++ (cells I R i ([], g, ri, se) m).1, (cells I R i ([], g, ri, se) m).2)
  | 0 => by simp [cells]
  | m + 1 => by
    rw [cells_succ, cells_succ, cells_app i L g ri se m]
    simp [cstep]

theorem grid_loop (pre : List (Array Nat)) (a : GridAcc) (out : GridAcc)
    (ha : a.1.toList = pre) (hg : a.2.2.1 = Array.replicate (R.n * R.n) 0) (hr : a.2.2.2 = ri0 I R)
    (h : forIn (List.range R.n) a (gridStep I R) = .ok out) :
    out.1.toList = pre ++ (grid I R R.n).1.map Desc.row ∧ out.2.2.1 = (grid I R R.n).2.1 ∧
      out.2.2.2 = (grid I R R.n).2.2.1 := by
  have := ExceptRange.range_invariant (gridStep I R)
    (fun k (s : GridAcc) => s.1.toList = pre ++ (grid I R k).1.map Desc.row ∧ s.2.2.1 = (grid I R k).2.1 ∧
      s.2.2.2 = (grid I R k).2.2.1) R.n
    (fun k _ s hs o ho => by
      obtain ⟨hrows, hgb, hri⟩ := hs
      unfold gridStep at ho
      obtain ⟨u, hu, ho⟩ := bind_ok' ho
      cases ho
      obtain ⟨ds, hds, hc⟩ := cell_loop I R k _ u hu
      have hc' : cells I R k ([], s.2.2.1, s.2.2.2, (cntS R.n I.allowed (sender I R k), R.fin.sb[sender I R k]!)) R.n =
          (ds, u.2.2.1, u.2.2.2.1, u.2.2.2.2) := hc
      have hds' : u.1.toList = s.1.toList ++ [Desc.row (hdrD I R k)] ++ ds.map Desc.row := by
        rw [hds, Array.toList_push]; rfl
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · show u.1.toList = _
        rw [grid_succ]
        unfold gstep
        rw [cells_app, ← hgb, ← hri, hc', hds', hrows]
        simp
      · show u.2.2.1 = _
        rw [grid_succ]
        unfold gstep
        rw [cells_app, ← hgb, ← hri, hc']
      · show u.2.2.2.1 = _
        rw [grid_succ]
        unfold gstep
        rw [cells_app, ← hgb, ← hri, hc'])
    a out ⟨by rw [ha]; simp [grid], hg, hr⟩ h
  exact this

/-- **The distribute rows of a run, explicitly.** -/
theorem dist_rows (d : DistOut) (hd : distRows I R = .ok d) :
    d.rows.toList = ((List.range R.n).map (shardD I R 0)).map Desc.row ++
      ((List.range R.n).map (shardD I R 1)).map Desc.row ++ (grid I R R.n).1.map Desc.row ∧
    d.gb = (grid I R R.n).2.1 := by
  rw [native_eq] at hd
  unfold build at hd
  obtain ⟨a, ha, hd⟩ := bind_ok' hd
  obtain ⟨b, hbld, hd⟩ := bind_ok' hd
  cases hd
  have hA : a.1.toList = ((List.range R.n).map (shardD I R 0)).map Desc.row ++
      ((List.range R.n).map (shardD I R 1)).map Desc.row := by
    simp only [List.forIn_cons, List.forIn_nil] at ha
    obtain ⟨o0, h0, ha⟩ := bind_ok' ha
    obtain ⟨a0, rfl, ha0⟩ := shard_side I R 0 _ o0 h0
    simp only at ha
    obtain ⟨o1, h1, ha⟩ := bind_ok' ha
    obtain ⟨a1, rfl, ha1⟩ := shard_side I R 1 _ o1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    rw [ha1, ha0]; simp
  obtain ⟨h1, h2, -⟩ := grid_loop I R _ _ b hA rfl rfl hbld
  exact ⟨h1, h2⟩

end

end ZkFormal.NearV3.Render.SsdBus
