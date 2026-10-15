/-
Hand-written deltas for the generated D1 walk copies (`scripts/rcpt_d1_copy.py --profile walk`,
lane v3-d1-phase2, L1 after the merge of lane v3-d1-a7b).  Not a Lean module.  Format as
`rcpt_d1_overrides.lean` (`-- @override <D0a constant>`, `-- @patch <D0a constant>`).

The two provenance lemmas read the bus balance with `walkU`'s walks (`D1/Link/WalkProv`);
`walkBal_all` moves the unread walks behind the ups walks.
-/

-- @override ZkFormal.NearV3.Walk3.edge_provided3
/-- **Every edge a walk row uses is provided** (D1: `walkU`'s walks are on the bus too,
`D1/Link/WalkProv.edge_provided3D`). -/
theorem edge_provided3_wu (hN : NodeWf3 vs) (hH : HeadWf hs) (hW : WalkWf3 ws)
    (hbal : ZkFormal.NearV3.D1.Link.BusBalD vs hs ws B_EDGE) (hT : (ws.flatMap (·.steps)).length < P)
    (hkl : ∀ s ∈ vs, klen3 s.v < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode ≤ 1) :
    (∃ n, ∃ hn : n < vs.length, st.e ∈ edgesOf3 n vs[n]) ∨
      ∃ h ∈ hs, st.e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] :=
  ZkFormal.NearV3.D1.Link.edge_provided3D hN hH hW hbal hkl hw hst hm

-- @override ZkFormal.NearV3.Walk3.bmap_provided3
/-- **Every `BMAP` message of an absent-at-branch row is a branch record's** (D1: with `walkU`'s
walks, `D1/Link/WalkProv.bmap_provided3D`). -/
theorem bmap_provided3_wu (hN : NodeWf3 vs) (hW : WalkWf3 ws)
    (hbal : ZkFormal.NearV3.D1.Link.BusBalD vs hs ws B_BMAP) (hT : (ws.flatMap (·.steps)).length < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode = 2) :
    ∃ n, ∃ hn : n < vs.length, st.e.getD 0 0 = n ∧ vs[n].v.bmap = some (st.bm, st.hv) :=
  ZkFormal.NearV3.D1.Link.bmap_provided3D hN hW hbal hw hst hm

-- @override ZkFormal.NearV3.UpsRows.walkBal_all
/-- **The balance over all walks** (D1: the candidates' and the ups walks, then `walkU`'s). -/
theorem walkBal_all_wu {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR} {v : List UpsSeg} (hw : UpsWf v)
    {b : Nat} (hb : b = B_EDGE ∨ b = B_BMAP) (hE : ZkFormal.NearV3.D1.Link.WalkBalD vs hs ws v b) :
    ZkFormal.NearV3.D1.Link.BusBalD vs hs (allWalks ws v) b := by
  obtain ⟨wx, hx, hE⟩ := hE
  refine ⟨wx, hx, ?_⟩
  have h := walkBal_all hw hb hE
  have key : ∀ (f : List WalkR → List Msg), (∀ A B, f (A ++ B) = f A ++ f B) → ∀ X : List Msg,
      ((X ++ f ((ws ++ v.map upsWalk) ++ wx)).map Msg.toFp).Perm
        ((X ++ f ((ws ++ wx) ++ v.map upsWalk)).map Msg.toFp) := by
    intro f hf X
    rw [hf, hf, hf, hf]
    apply List.Perm.map
    simp only [List.append_assoc]
    apply List.Perm.append_left; apply List.Perm.append_left
    exact List.perm_append_comm
  unfold Walk3.BusBal at h ⊢
  unfold allWalks at h ⊢
  exact (key (fun w => walkSends3 w b) (fun A B => walkSends3_append A B b) _).trans
    (h.trans (key (fun w => walkRecvs3 w b) (fun A B => walkRecvs3_append A B b) _).symm)

-- @override ZkFormal.NearV3.UpsRows.ups_bm_22
/-- The `W3` bitmap of an absent-at-branch terminal is a branch record's bitmap (D1: `walkU`'s
walks are on `BMAP` too). -/
theorem ups_bm_22_wu {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR} {v : List UpsSeg}
    (hN : NodeWf3 vs) (hW : WalkWf3 ws) (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 22) (hw : UpsWf v)
    (hbal : ZkFormal.NearV3.D1.Link.WalkBalD vs hs ws v B_BMAP) {s : UpsSeg} (hs' : s ∈ v) (hm : s.row 3 mB = 1) : s.row 3 wbm < 2 ^ 16 := by
  obtain ⟨wx, hx, hb⟩ := walkBal_all_wu hw (Or.inr rfl) hbal
  have hP := P_big
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs'
  have hl4 := hL.walk.1
  -- the row's `BMAP` step
  have hst : stepOf (s.row 3) 3 ∈ (upsWalk s).steps := by
    simp only [upsWalk, List.mem_map, List.mem_range]; exact ⟨3, by omega, rfl⟩
  have hmode : (stepOf (s.row 3) 3).mode = 2 := by
    have F := wRowF hw hs' hL 3 (by omega)
    have Mc := mode_cases F.modes 3
    exact Mc.2.2.1.2 hm
  -- canonical `BMAP` keys of all walks
  have hwalkC0 : ∀ {wv' : WalkR}, wv' ∈ allWalks ws v → ∀ st' ∈ wv'.steps, st'.mode = 2 →
      Link.Canon [st'.e.getD 0 0, st'.bm, st'.hv] ∧ st'.ub < P := by
    intro wv' hw' st' hst' hm2
    rcases List.mem_append.1 hw' with hw' | hw'
    · obtain ⟨b', hok'⟩ := Walk3.stepOk_of_mem hW hw' hst'
      have hab' := hok'.absB hm2
      have hc' := (hW.canon wv' hw').2.2 st' hst'
      refine ⟨?_, hc'.2.2.1⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Link.getD_lt hc'.2.2.2 0
      · have := hab'.2.1; unfold P; omega
      · have := hab'.2.2.1; unfold P; omega
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw'
      simp only [upsWalk, List.mem_map, List.mem_range] at hst'
      obtain ⟨j', hj', rfl⟩ := hst'
      refine ⟨?_, by simp only [stepOf]; exact rowLt hw ht _ _⟩
      intro x hx
      simp only [stepOf, List.mem_cons, List.not_mem_nil, or_false, List.getD_cons_zero] at hx
      rcases hx with rfl | rfl | rfl <;> exact rowLt hw ht _ _
  -- `walkU`'s rows (D1): `StepOkU.absB`
  have hwalkC : ∀ {wv' : WalkR}, wv' ∈ allWalks ws v ++ wx → ∀ st' ∈ wv'.steps, st'.mode = 2 →
      Link.Canon [st'.e.getD 0 0, st'.bm, st'.hv] ∧ st'.ub < P := by
    intro wv' hw' st' hst' hm2
    rcases List.mem_append.1 hw' with hw' | hw'
    · exact hwalkC0 hw' st' hst' hm2
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hst'
      have hab' := (hx.rows wv' hw' i hi).absB hm2
      have hc' := (hx.canon wv' hw').2.2 _ hst'
      refine ⟨?_, hc'.2.2.1⟩
      intro x hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact Link.getD_lt hc'.2.2.2 0
      · have := hab'.2.1; unfold P; omega
      · have := hab'.2.2.1; unfold P; omega
  have hheadS : headSends hs B_BMAP = [] := by simp [headSends, B_BMAP, B_MIDROOT, B_PARENT, B_EDGE, B_DIGS]
  have hheadR : headRecvs hs B_BMAP = [] := by simp [headRecvs, B_BMAP, B_DIGEST, B_ROOT, B_EDGE]
  unfold Walk3.BusBal at hb
  rw [Walk3.walkSends3_bmap, Walk3.walkRecvs3_bmap, hheadS, hheadR, List.append_nil, List.append_nil] at hb
  let st := stepOf (s.row 3) 3
  have hprov : ∃ n, ∃ hn : n < vs.length, ∃ bm hv', vs[n].v.bmap = some (bm, hv') ∧
      [n, bm, hv'] = [st.e.getD 0 0, st.bm, st.hv] := by
    apply Classical.byContradiction; intro hno
    refine Walk3.chain_provided (k := 3) _ _ _ [st.e.getD 0 0, st.bm, st.hv] ?_ ?_ ?_ rfl
      (hwalkC (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨s, hs', rfl⟩))) st hst hmode).1
      (u := st.ub) ?_ hb
    · intro m hm'
      have hm'' : m ∈ nodeSends3 vs B_BMAP ∨ m ∈ nodeRecvs3 vs B_BMAP := by
        rcases List.mem_append.mp hm' with h | h
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨n, hn, bm, hv', x, hbm, rfl⟩ := Walk3.mem_nodeBmap hm''
      have hsm := List.getElem_mem hn
      refine ⟨[n, bm, hv'], x, rfl, rfl, ?_, fun he => hno ⟨n, hn, bm, hv', hbm, he⟩⟩
      have hwf := hN.wf _ hsm
      generalize hvv : vs[n].v = vv at hbm hwf
      cases vv with
      | branch sv kids m =>
        simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
        obtain ⟨rfl, rfl⟩ := hbm
        exact Walk3.bmap_canon hwf.1 n (by have := hN.count; omega) sv
      | leaf => simp [NodeV3.bmap] at hbm
      | ext => simp [NodeV3.bmap] at hbm
    · intro p hp
      obtain ⟨wv', hw', hp'⟩ := List.mem_flatMap.mp hp
      obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hp'
      have hst'' := List.mem_filter.mp hst'
      have hm2 : st'.mode = 2 := by simpa using hst''.2
      exact ⟨rfl, (hwalkC hw' st' hst''.1 hm2).1, (hwalkC hw' st' hst''.1 hm2).2⟩
    · have := Walk3.flatMap_filter_len (fun st : WStep3 => decide (st.mode = 2))
        (fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)) (allWalks ws v ++ wx)
      have h1 : ((allWalks ws v ++ wx).flatMap (·.steps)).length =
          (ws.flatMap (·.steps)).length + 4 * v.length + (wx.flatMap (·.steps)).length := by
        rw [List.flatMap_append, List.length_append, allWalks, List.flatMap_append, List.length_append,
          upsWalks_len]
      have := segs_len hw
      have := hx.nrows
      omega
    · exact List.mem_flatMap.mpr ⟨upsWalk s, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨s, hs', rfl⟩)),
        List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hmode⟩, rfl⟩⟩
  obtain ⟨n, hn, bm, hv', hbm, he⟩ := hprov
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨-, rfl, -⟩ := he
  have hwf := hN.wf _ (List.getElem_mem hn)
  generalize hvv : vs[n].v = vv at hbm hwf
  cases vv with
  | branch sv kids m =>
    simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
    obtain ⟨hb1, -⟩ := hbm
    have := Link3.kidBitmap_lt3 hwf.1
    show st.bm < 2 ^ 16
    rw [← hb1]; exact this
  | leaf => simp [NodeV3.bmap] at hbm
  | ext => simp [NodeV3.bmap] at hbm
