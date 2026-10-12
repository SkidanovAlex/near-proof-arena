import ZkFormal.NearV3.Render.SchedBusGridRows

/-!
# The distribute grid model: structure, endpoints and grants

For the functional grid model of `SchedBusSsdDist` (`cells`, `grid`): the sorted senders/receivers
are injective into `range n`; the cells of a row are the descriptors read at each step's state; the
receiver endpoint of receiver `rⱼ` changes only at cell `j`, the grants array only at link
`sender i · n + rⱼ` of an allowed cell.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd
open ProcDistGeneratorFactor ProcDistCellBridge NearSpecV3.Scheduler

theorem inj_of_nodup_map (f : Nat → Nat) : ∀ n, ((List.range n).map f).Nodup →
    ∀ a b, a < n → b < n → f a = f b → a = b
  | 0, _, _, _, ha, _, _ => absurd ha (Nat.not_lt_zero _)
  | n + 1, h, a, b, ha, hb, e => by
    rw [List.range_succ, List.map_append, List.nodup_append] at h
    obtain ⟨h1, -, h3⟩ := h
    have hm : ∀ x, x < n → f x ≠ f n := by
      intro x hx hx'
      exact h3 (f x) (List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩) (f n) (by simp) hx'
    by_cases ha' : a = n
    · by_cases hb' : b = n
      · omega
      · exact absurd (by rw [← e, ha']) (hm b (by omega))
    · by_cases hb' : b = n
      · exact absurd (by rw [e, hb']) (hm a (by omega))
      · exact inj_of_nodup_map f n h1 a b (by omega) (by omega) e

section
variable (I : Input) (R : Run)

theorem sender_lt (i : Nat) (hi : i < R.n) : sender I R i < R.n := by
  have hm : sender I R i ∈ ProcDistGridBridge.senders I R := by
    rw [← ProcDistGridBridge.sender_list]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  exact List.mem_range.mp ((sortByKey_perm _ _).mem_iff.mp hm)

theorem receiver_lt (j : Nat) (hj : j < R.n) : receiver I R j < R.n := by
  have hm : receiver I R j ∈ ProcDistGridBridge.receivers I R := by
    rw [← ProcDistGridBridge.receiver_list]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  exact List.mem_range.mp ((sortByKey_perm _ _).mem_iff.mp hm)

theorem sender_inj {i i' : Nat} (hi : i < R.n) (hi' : i' < R.n) (h : sender I R i = sender I R i') : i = i' := by
  have hnd : ((List.range R.n).map (sender I R)).Nodup := by
    rw [ProcDistGridBridge.sender_list]; exact (sortByKey_perm _ _).nodup_iff.mpr List.nodup_range
  exact inj_of_nodup_map _ _ hnd i i' hi hi' h

theorem receiver_inj {j j' : Nat} (hj : j < R.n) (hj' : j' < R.n) (h : receiver I R j = receiver I R j') : j = j' := by
  have hnd : ((List.range R.n).map (receiver I R)).Nodup := by
    rw [ProcDistGridBridge.receiver_list]; exact (sortByKey_perm _ _).nodup_iff.mpr List.nodup_range
  exact inj_of_nodup_map _ _ hnd j j' hj hj' h

theorem link_inj {i j i' j' : Nat} (hi : i < R.n) (hj : j < R.n) (hi' : i' < R.n) (hj' : j' < R.n)
    (h : sender I R i * R.n + receiver I R j = sender I R i' * R.n + receiver I R j') : i = i' ∧ j = j' := by
  have h1 := receiver_lt I R j hj
  have h2 := receiver_lt I R j' hj'
  have hs : sender I R i = sender I R i' := by
    have e1 : (sender I R i * R.n + receiver I R j) / R.n = sender I R i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h1, Nat.zero_add]
    have e2 : (sender I R i' * R.n + receiver I R j') / R.n = sender I R i' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2, Nat.zero_add]
    rw [← e1, ← e2, h]
  have hr : receiver I R j = receiver I R j' := by rw [hs] at h; omega
  exact ⟨sender_inj I R hi hi' hs, receiver_inj I R hj hj' hr⟩

theorem link_lt {i j : Nat} (hi : i < R.n) (hj : j < R.n) : sender I R i * R.n + receiver I R j < R.n * R.n := by
  have h1 := sender_lt I R i hi
  have h2 := receiver_lt I R j hj
  calc sender I R i * R.n + receiver I R j < sender I R i * R.n + R.n := by omega
    _ = (sender I R i + 1) * R.n := by rw [Nat.succ_mul]
    _ ≤ R.n * R.n := Nat.mul_le_mul_right _ h1

/-! ## One row of cells -/

/-- The descriptor of cell `j` from the state before it. -/
def cellAt (i j : Nat) (st : GS) : Desc :=
  .cell I.ids R.tau R.n i j (sender I R i) (receiver I R j) st.2.2.2.1 st.2.2.2.2
    (st.2.2.1[receiver I R j]!).1 (st.2.2.1[receiver I R j]!).2 (cAl I R i j)

/-- The grant of cell `j` from the state before it. -/
def gAt (i j : Nat) (st : GS) : Nat :=
  ProcDistCellRow.grant (cAl I R i j) st.2.2.2.1 st.2.2.2.2
    (st.2.2.1[receiver I R j]!).1 (st.2.2.1[receiver I R j]!).2

theorem cells_list (i : Nat) (g : Array Nat) (ri : Array (Nat × Nat)) (se : Nat × Nat) :
    ∀ k, (cells I R i ([], g, ri, se) k).1 = (List.range k).map fun j => cellAt I R i j (cells I R i ([], g, ri, se) j)
  | 0 => rfl
  | k + 1 => by
    rw [cells_succ, List.range_succ, List.map_append, ← cells_list i g ri se k]
    rfl

theorem cells_size (i : Nat) (st : GS) : ∀ k, (cells I R i st k).2.2.1.size = st.2.2.1.size ∧
    (cells I R i st k).2.1.size = st.2.1.size
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    rw [cells_succ]
    obtain ⟨h1, h2⟩ := cells_size i st k
    simp only [cstep, Array.size_set!]
    refine ⟨h1, ?_⟩
    split <;> simp [h2]

theorem cells_ri_other (i : Nat) (st : GS) (r : Nat) :
    ∀ k, (∀ j, j < k → receiver I R j ≠ r) → (cells I R i st k).2.2.1[r]! = st.2.2.1[r]!
  | 0, _ => rfl
  | k + 1, h => by
    rw [cells_succ]
    simp only [cstep]
    rw [Sched.getElem!_set!_ne _ _ (h k (by omega)), cells_ri_other i st r k (fun j hj => h j (by omega))]

theorem cells_gb_other (i : Nat) (st : GS) (l : Nat) :
    ∀ k, (∀ j, j < k → sender I R i * R.n + receiver I R j ≠ l) → (cells I R i st k).2.1[l]! = st.2.1[l]!
  | 0, _ => rfl
  | k + 1, h => by
    rw [cells_succ]
    simp only [cstep]
    split
    · rw [Sched.getElem!_set!_ne _ _ (h k (by omega)), cells_gb_other i st l k (fun j hj => h j (by omega))]
    · exact cells_gb_other i st l k (fun j hj => h j (by omega))

/-- The receiver endpoint read by cell `j` is the row's initial one. -/
theorem cells_ri_read (i : Nat) (st : GS) (j : Nat) (hj : j < R.n) (k : Nat) (hk : k ≤ j) :
    (cells I R i st k).2.2.1[receiver I R j]! = st.2.2.1[receiver I R j]! :=
  cells_ri_other I R i st _ k (fun j' hj' e => by have := receiver_inj I R (by omega) hj e; omega)

/-- After the row, receiver `rⱼ` holds cell `j`'s update. -/
theorem cells_ri_after (i : Nat) (st : GS) (hs : st.2.2.1.size = R.n) (j : Nat) (hj : j < R.n) :
    (cells I R i st R.n).2.2.1[receiver I R j]! =
      ((st.2.2.1[receiver I R j]!).1 - b2n (cAl I R i j),
       (st.2.2.1[receiver I R j]!).2 - gAt I R i j (cells I R i st j)) := by
  have hr := receiver_lt I R j hj
  have hafter : (cells I R i st R.n).2.2.1[receiver I R j]! = (cells I R i st (j + 1)).2.2.1[receiver I R j]! := by
    have key : ∀ d, j + 1 + d ≤ R.n → (cells I R i st (j + 1 + d)).2.2.1[receiver I R j]! =
        (cells I R i st (j + 1)).2.2.1[receiver I R j]! := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, cells_succ]
        simp only [cstep]
        rw [Sched.getElem!_set!_ne _ _ (fun e => by have := receiver_inj I R (by omega) hj e; omega), ih (by omega)]
    have := key (R.n - (j + 1)) (by omega)
    rwa [show j + 1 + (R.n - (j + 1)) = R.n by omega] at this
  rw [hafter, cells_succ]
  simp only [cstep]
  rw [Sched.getElem!_set!_self, if_pos (by rw [(cells_size I R i st j).1, hs]; exact hr),
    cells_ri_read I R i st j hj j (Nat.le_refl _)]
  unfold gAt
  rw [cells_ri_read I R i st j hj j (Nat.le_refl _)]

/-- After the row, the grants array holds cell `j`'s grant at its link if allowed. -/
theorem cells_gb_after (i : Nat) (hi : i < R.n) (st : GS) (hs : st.2.1.size = R.n * R.n) (j : Nat) (hj : j < R.n) :
    (cells I R i st R.n).2.1[sender I R i * R.n + receiver I R j]! =
      if cAl I R i j then gAt I R i j (cells I R i st j) else st.2.1[sender I R i * R.n + receiver I R j]! := by
  have hl := link_lt I R hi hj
  have hafter : (cells I R i st R.n).2.1[sender I R i * R.n + receiver I R j]! =
      (cells I R i st (j + 1)).2.1[sender I R i * R.n + receiver I R j]! := by
    have key : ∀ d, j + 1 + d ≤ R.n → (cells I R i st (j + 1 + d)).2.1[sender I R i * R.n + receiver I R j]! =
        (cells I R i st (j + 1)).2.1[sender I R i * R.n + receiver I R j]! := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, cells_succ]
        simp only [cstep]
        have hne : sender I R i * R.n + receiver I R (j + 1 + d) ≠ sender I R i * R.n + receiver I R j := by
          intro e; have := (link_inj I R hi (by omega) hi hj e).2; omega
        split
        · rw [Sched.getElem!_set!_ne _ _ hne, ih (by omega)]
        · exact ih (by omega)
    have := key (R.n - (j + 1)) (by omega)
    rwa [show j + 1 + (R.n - (j + 1)) = R.n by omega] at this
  rw [hafter, cells_succ]
  simp only [cstep]
  have hbefore := cells_gb_other I R i st (sender I R i * R.n + receiver I R j) j
    (fun j' hj' e => by have := (link_inj I R hi (by omega) hi hj e).2; omega)
  split
  · rename_i ha
    rw [Sched.getElem!_set!_self, if_pos (by rw [(cells_size I R i st j).2, hs]; exact hl)]; rfl
  · exact hbefore

/-! ## The generator's allowed-cell check -/

/-- An allowed cell reads a positive receiver count. -/
def CellOk : Desc → Prop
  | .cell _ _ _ _ _ _ _ _ _ n2 _ al => al = true → 1 ≤ n2
  | _ => True

theorem cell_loop_ok (i : Nat) (acc out : CellAcc) (h : forIn (List.range R.n) acc (cellStep I R i) = .ok out) :
    ∃ ds, cells I R i ([], acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2) R.n = (ds, out.2.2.1, out.2.2.2.1, out.2.2.2.2) ∧
      ∀ x ∈ ds, CellOk x := by
  have := ExceptRange.range_invariant (cellStep I R i)
    (fun k (s : CellAcc) => ∃ ds, cells I R i ([], acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2) k =
      (ds, s.2.2.1, s.2.2.2.1, s.2.2.2.2) ∧ ∀ x ∈ ds, CellOk x) R.n
    (fun k _ s hs o ho => by
      obtain ⟨ds, hst, hok⟩ := hs
      obtain ⟨out, rfl, -, h2, h3, h4⟩ := cell_step I R i k s o ho
      obtain ⟨out', ho', hg⟩ := cell_step_gb I R i k s _ ho
      cases ho'
      refine ⟨out, rfl, ds ++ [.cell I.ids R.tau R.n i k (sender I R i) (receiver I R k) s.2.2.2.2.1 s.2.2.2.2.2
        (s.2.2.2.1[receiver I R k]!).1 (s.2.2.2.1[receiver I R k]!).2 (cAl I R i k)], ?_, ?_⟩
      · rw [cells_succ, hst, h2, h3, hg]
        rfl
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hok x hx
        · simp only [List.mem_singleton] at hx
          subst hx
          exact fun ha => (h4 ha).2)
    _ out ⟨[], rfl, fun _ h => by simp at h⟩ h
  exact this

theorem grid_loop_ok (a : GridAcc) (out : GridAcc)
    (hg : a.2.2.1 = Array.replicate (R.n * R.n) 0) (hr : a.2.2.2 = ri0 I R)
    (h : forIn (List.range R.n) a (gridStep I R) = .ok out) : ∀ x ∈ (grid I R R.n).1, CellOk x := by
  have := ExceptRange.range_invariant (gridStep I R)
    (fun k (s : GridAcc) => s.2.2.1 = (grid I R k).2.1 ∧ s.2.2.2 = (grid I R k).2.2.1 ∧
      ∀ x ∈ (grid I R k).1, CellOk x) R.n
    (fun k _ s hs o ho => by
      obtain ⟨hgb, hri, hok⟩ := hs
      unfold gridStep at ho
      obtain ⟨u, hu, ho⟩ := bind_ok' ho
      cases ho
      obtain ⟨ds, hc, hdok⟩ := cell_loop_ok I R k _ u hu
      have hc' : cells I R k ([], s.2.2.1, s.2.2.2, (cntS R.n I.allowed (sender I R k), R.fin.sb[sender I R k]!)) R.n =
          (ds, u.2.2.1, u.2.2.2.1, u.2.2.2.2) := hc
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · show u.2.2.1 = _
        rw [grid_succ]; unfold gstep; rw [cells_app, ← hgb, ← hri, hc']
      · show u.2.2.2.1 = _
        rw [grid_succ]; unfold gstep; rw [cells_app, ← hgb, ← hri, hc']
      · rw [grid_succ]; unfold gstep; rw [cells_app, ← hgb, ← hri, hc']
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with (hx | hx) | hx
        · exact hok x hx
        · subst hx; trivial
        · exact hdok x hx)
    a out ⟨by rw [hg]; rfl, hr, fun _ h => by simp [grid] at h⟩ h
  exact this.2.2

theorem dist_ok (d : DistOut) (hd : distRows I R = .ok d) : ∀ x ∈ (grid I R R.n).1, CellOk x := by
  rw [native_eq] at hd
  unfold build at hd
  obtain ⟨a, -, hd⟩ := bind_ok' hd
  obtain ⟨b, hbld, -⟩ := bind_ok' hd
  exact grid_loop_ok I R _ b rfl rfl hbld

/-! ## The whole grid -/

def se0 (i : Nat) : Nat × Nat := (cntS R.n I.allowed (sender I R i), R.fin.sb[sender I R i]!)

/-- Row `i`'s cell states (from the empty descriptor list). -/
def rowC (i k : Nat) : GS := cells I R i ([], (grid I R i).2.1, (grid I R i).2.2.1, se0 I R i) k

theorem grid_succ_eq (i : Nat) :
    (grid I R (i + 1)).1 = (grid I R i).1 ++ hdrD I R i :: (rowC I R i R.n).1 ∧
    (grid I R (i + 1)).2 = (rowC I R i R.n).2 := by
  rw [grid_succ]
  unfold gstep
  rw [cells_app]
  exact ⟨by simp [rowC, se0], rfl⟩

theorem grid_list : ∀ m, (grid I R m).1 = (List.range m).flatMap fun i =>
    hdrD I R i :: (List.range R.n).map fun j => cellAt I R i j (rowC I R i j)
  | 0 => rfl
  | m + 1 => by
    rw [(grid_succ_eq I R m).1, grid_list m, List.range_succ, List.flatMap_append, rowC, cells_list]
    simp [rowC]

theorem ri0_size : (ri0 I R).size = R.n := by simp [ri0]

theorem grid_size : ∀ m, (grid I R m).2.1.size = R.n * R.n ∧ (grid I R m).2.2.1.size = R.n
  | 0 => by simp [grid, ri0_size]
  | m + 1 => by
    rw [(grid_succ_eq I R m).2]
    obtain ⟨h1, h2⟩ := grid_size m
    exact ⟨(cells_size I R m _ R.n).2.trans h1, (cells_size I R m _ R.n).1.trans h2⟩

theorem gAt_false (i j : Nat) (st : GS) (h : cAl I R i j = false) : gAt I R i j st = 0 := by
  simp [gAt, ProcDistCellRow.grant, h]

theorem grid_gb : ∀ m, m ≤ R.n → ∀ i j, i < R.n → j < R.n →
    (grid I R m).2.1[sender I R i * R.n + receiver I R j]! = if i < m then gAt I R i j (rowC I R i j) else 0
  | 0, _, i, j, hi, hj => by
    simp only [grid, List.range_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
    have := link_lt I R hi hj
    simp [getElem!_def, Array.getElem?_replicate, this]
  | m + 1, hm, i, j, hi, hj => by
    rw [(grid_succ_eq I R m).2]
    by_cases him : i = m
    · subst him
      rw [rowC, cells_gb_after I R i hi ([], (grid I R i).2.1, (grid I R i).2.2.1, se0 I R i) (grid_size I R i).1 j hj, grid_gb i (by omega) i j hi hj]
      simp only [Nat.lt_irrefl, ite_false, show i < i + 1 by omega, ite_true]
      cases ha : cAl I R i j
      · simp only [Bool.false_eq_true, ite_false]; rw [gAt_false I R i j _ ha]
      · rfl
    · rw [rowC, cells_gb_other I R m _ _ R.n (fun j' hj' e => by
          have := (link_inj I R (by omega) hj' hi hj e).1; omega),
        grid_gb m (by omega) i j hi hj]
      by_cases hlt : i < m
      · simp [hlt, show i < m + 1 by omega]
      · simp [hlt, show ¬ i < m + 1 by omega]

theorem grid_ri_succ (i j : Nat) (hj : j < R.n) :
    (grid I R (i + 1)).2.2.1[receiver I R j]! =
      (((grid I R i).2.2.1[receiver I R j]!).1 - b2n (cAl I R i j),
       ((grid I R i).2.2.1[receiver I R j]!).2 - gAt I R i j (rowC I R i j)) := by
  rw [(grid_succ_eq I R i).2]
  exact cells_ri_after I R i ([], (grid I R i).2.1, (grid I R i).2.2.1, se0 I R i) (grid_size I R i).2 j hj

theorem grid_ri0 (j : Nat) (hj : j < R.n) :
    (grid I R 0).2.2.1[receiver I R j]! = (cntR R.n I.allowed (receiver I R j), R.fin.rb[receiver I R j]!) := by
  show (ri0 I R)[receiver I R j]! = _
  simp only [ri0, List.map_toArray]
  exact getElem!_toArray_map_range R.n _ (receiver_lt I R j hj)

theorem rowC_ri (i j : Nat) (hj : j < R.n) :
    ((rowC I R i j).2.2.1)[receiver I R j]! = (grid I R i).2.2.1[receiver I R j]! :=
  cells_ri_read I R i _ j hj j (Nat.le_refl _)

end

end ZkFormal.NearV3.Render.SsdBus
