import ZkFormal.NearV3.Link.Walk3Prov
import ZkFormal.NearV3.D1.Link.WalkU

/-!
# `ZkFormal.NearV3.D1.Link.WalkProv` — walk provenance with the unread-key walks (L1)

Lane `v3-d1-phase2`, item L1 (after the a7b merge).  D0a's `edge_provided3` / `bmap_provided3`
(`Link/Walk3Prov`) read the `EDGE` / `BMAP` balance of the node / head records and **all** walks
on the bus, and use the walks' `WalkWf3` only for two per-row facts of the rows on the bus: the
row's `StepOk` (edge length, `absB`) and its canonicity.  In `nearAirV3D1` the bus also carries
`walkU`'s walks (`WalkUWf`: D0a rows plus the stub mode `4`, which has no `EDGE` / `BMAP`
traffic).  So:

* `WalkRowsOk ws`: the per-row facts (canonical rows; `StepOk` for every non-stub row);
  `rowsOk_of_wf` (`WalkWf3`), `rowsOk_of_u` (`WalkUWf`), `rowsOk_append`;
* `BusBalD vs hs ws b`: D0a's `BusBal` over `ws` followed by some `walkU` walks;
* **`edge_provided3R`**, **`bmap_provided3R`**: D0a's proofs with `WalkRowsOk` for the walks on
  the bus (text of `Link/Walk3Prov`, the two row facts read from `WalkRowsOk`);
* **`edge_provided3D`**, **`bmap_provided3D`**: the D0a statements with `BusBalD`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3 ZkFormal.NearV3.Walk3

/-- The per-row facts of the walks on a bus that the provenance arguments use. -/
structure WalkRowsOk (ws : List WalkR) : Prop where
  canon : ∀ wv ∈ ws, wv.w < P ∧ wv.tau < P ∧ ∀ st ∈ wv.steps,
    st.sym < P ∧ st.u < P ∧ st.ub < P ∧ ∀ x ∈ st.e, x < P
  ok : ∀ wv ∈ ws, ∀ st ∈ wv.steps, st.mode ≠ 4 → ∃ b, StepOk st b

theorem rowsOk_of_wf {ws : List WalkR} (hW : WalkWf3 ws) : WalkRowsOk ws :=
  ⟨hW.canon, fun _ hw _ hst _ => stepOk_of_mem hW hw hst⟩

theorem rowsOk_of_u {ws : List WalkR} (hW : WalkUWf ws) : WalkRowsOk ws := by
  refine ⟨hW.canon, fun wv hw st hst h4 => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hst
  exact ⟨_, (hW.rows wv hw i hi).stepOk h4⟩

theorem rowsOk_append {A B : List WalkR} (hA : WalkRowsOk A) (hB : WalkRowsOk B) :
    WalkRowsOk (A ++ B) := by
  refine ⟨fun wv hw => ?_, fun wv hw => ?_⟩
  · rcases List.mem_append.mp hw with h | h
    · exact hA.canon wv h
    · exact hB.canon wv h
  · rcases List.mem_append.mp hw with h | h
    · exact hA.ok wv h
    · exact hB.ok wv h

/-- **The D1 walk balance on one bus**: D0a's `BusBal` with `walkU`'s walks after `ws`. -/
def BusBalD (vs : List NodeS3) (hs : List HeadE) (ws : List WalkR) (b : Nat) : Prop :=
  ∃ wx, WalkUWf wx ∧ BusBal vs hs (ws ++ wx) b

theorem rows_append_lt {ws wx : List WalkR} (hW : WalkWf3 ws) (hx : WalkUWf wx) :
    ((ws ++ wx).flatMap (·.steps)).length < P := by
  have h1 := hW.nrows
  have h2 := hx.nrows
  rw [List.flatMap_append, List.length_append]
  unfold P; omega

section Prov
variable {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR}

/-- **Every edge a walk row uses is provided** (by a node record or a head). -/
theorem edge_provided3R (hN : NodeWf3 vs) (hH : HeadWf hs) (hR : WalkRowsOk ws)
    (hbal : BusBal vs hs ws B_EDGE) (hT : (ws.flatMap (·.steps)).length < P)
    (hkl : ∀ s ∈ vs, klen3 s.v < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode ≤ 1) :
    (∃ n, ∃ hn : n < vs.length, st.e ∈ edgesOf3 n vs[n]) ∨
      ∃ h ∈ hs, st.e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] := by
  apply Classical.byContradiction; intro hno
  have hno1 : ∀ n (hn : n < vs.length), st.e ∉ edgesOf3 n vs[n] :=
    fun n hn he => hno (Or.inl ⟨n, hn, he⟩)
  have hno2 : ∀ h ∈ hs, st.e ≠ [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] :=
    fun h hh he => hno (Or.inr ⟨h, hh, he⟩)
  obtain ⟨b, hok⟩ := hR.ok wv hw st hst (by omega)
  have hcanW := hR.canon wv hw
  have hec : Canon st.e := (hcanW.2.2 st hst).2.2.2
  have hcount := hN.count
  have hP := P_big
  unfold BusBal at hbal
  rw [nodeSends3_edge, nodeRecvs3_edge, headSends_edge, headRecvs_edge, walkSends3_edge,
    walkRecvs3_edge] at hbal
  refine chain_provided (k := 6) _ _ _ st.e ?_ ?_ ?_ hok.elen hec (u := st.u) ?_ hbal
  · intro m hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · rcases List.mem_append.mp hm' with hm' | hm'
      · obtain ⟨⟨s, n⟩, hp, hm'⟩ := List.mem_flatMap.mp hm'
        obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm'
        have hsm := List.getElem_mem hn
        obtain ⟨h6, hc, -, -⟩ := edges3_canon n vs[n] (by omega) (hN.canon _ hsm) (hkl _ hsm)
          (hN.wf _ hsm) e' he'
        exact ⟨e', 0, rfl, h6, hc, fun he => hno1 n hn (he ▸ he')⟩
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm'
        have hc := hH.canon h hh
        refine ⟨[0, h.tau, SYM_START, h.rres, 0, EK_DOWN], 0, rfl, rfl, ?_, fun he => hno2 h hh he.symm⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (unfold SYM_START P; omega) | (unfold EK_DOWN P; omega)
    · rcases List.mem_append.mp hm' with hm' | hm'
      · obtain ⟨⟨s, n⟩, hp, hm'⟩ := List.mem_flatMap.mp hm'
        obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
        obtain ⟨⟨e', u⟩, he', rfl⟩ := List.mem_map.mp hm'
        have he'' := (List.of_mem_zip he').1
        have hsm := List.getElem_mem hn
        obtain ⟨h6, hc, -, -⟩ := edges3_canon n vs[n] (by omega) (hN.canon _ hsm) (hkl _ hsm)
          (hN.wf _ hsm) e' he''
        exact ⟨e', u, rfl, h6, hc, fun he => hno1 n hn (he ▸ he'')⟩
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm'
        have hc := hH.canon h hh
        refine ⟨[0, h.tau, SYM_START, h.rres, 0, EK_DOWN], h.mE, rfl, rfl, ?_, fun he => hno2 h hh he.symm⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (unfold SYM_START P; omega) | (unfold EK_DOWN P; omega)
  · intro s hs
    obtain ⟨wv', hw', hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hs'
    have hst'' := (List.mem_filter.mp hst').1
    have hm1 : st'.mode ≤ 1 := by simpa using (List.mem_filter.mp hst').2
    obtain ⟨b', hok'⟩ := hR.ok wv' hw' st' hst'' (by omega)
    have hc' := (hR.canon wv' hw').2.2 st' hst''
    exact ⟨hok'.elen, hc'.2.2.2, hc'.2.1⟩
  · have := flatMap_filter_len (fun st : WStep3 => decide (st.mode ≤ 1)) (fun st => (st.e, st.u)) ws
    omega
  · exact List.mem_flatMap.mpr ⟨wv, hw, List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hm⟩, rfl⟩⟩

/-- **Every `BMAP` message of an absent-at-branch row is a branch record's.** -/
theorem bmap_provided3R (hN : NodeWf3 vs) (hR : WalkRowsOk ws)
    (hbal : BusBal vs hs ws B_BMAP) (hT : (ws.flatMap (·.steps)).length < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode = 2) :
    ∃ n, ∃ hn : n < vs.length, st.e.getD 0 0 = n ∧ vs[n].v.bmap = some (st.bm, st.hv) := by
  apply Classical.byContradiction; intro hno
  have hno1 : ∀ n (hn : n < vs.length) bm hv, vs[n].v.bmap = some (bm, hv) →
      [n, bm, hv] ≠ [st.e.getD 0 0, st.bm, st.hv] := by
    intro n hn bm hv hb he
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨h1, rfl, rfl⟩ := he
    exact hno ⟨n, hn, h1.symm, hb⟩
  obtain ⟨b, hok⟩ := hR.ok wv hw st hst (by omega)
  have hcanW := hR.canon wv hw
  have hab := hok.absB hm
  have hcount := hN.count
  have hP := P_big
  have hcanon : ∀ st' ∈ wv.steps, ∀ x ∈ st'.e, x < P := fun st' h => (hcanW.2.2 st' h).2.2.2
  have hwalkC : ∀ {wv' : WalkR}, wv' ∈ ws → ∀ st' ∈ wv'.steps, st'.mode = 2 →
      Canon [st'.e.getD 0 0, st'.bm, st'.hv] := by
    intro wv' hw' st' hst' hm2
    obtain ⟨b', hok'⟩ := hR.ok wv' hw' st' hst' (by omega)
    have hab' := hok'.absB hm2
    have hc' := (hR.canon wv' hw').2.2 st' hst'
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact getD_lt hc'.2.2.2 0
    · have := hab'.2.1; unfold P; omega
    · have := hab'.2.2.1; unfold P; omega
  have hheadS : headSends hs B_BMAP = [] := by simp [headSends, B_BMAP, B_MIDROOT, B_PARENT, B_EDGE, B_DIGS]
  have hheadR : headRecvs hs B_BMAP = [] := by simp [headRecvs, B_BMAP, B_DIGEST, B_ROOT, B_EDGE]
  unfold BusBal at hbal
  rw [walkSends3_bmap, walkRecvs3_bmap, hheadS, hheadR, List.append_nil, List.append_nil] at hbal
  have hprov : ∀ m, m ∈ nodeSends3 vs B_BMAP ∨ m ∈ nodeRecvs3 vs B_BMAP →
      ∃ e' x, m = e' ++ [x] ∧ e'.length = 3 ∧ Canon e' ∧ e' ≠ [st.e.getD 0 0, st.bm, st.hv] := by
    intro m hm'
    obtain ⟨n, hn, bm, hv, x, hb, rfl⟩ := mem_nodeBmap hm'
    have hsm := List.getElem_mem hn
    refine ⟨[n, bm, hv], x, rfl, rfl, ?_, hno1 n hn bm hv hb⟩
    have hwf := hN.wf _ hsm
    generalize hvv : vs[n].v = v at hb hwf
    cases v with
    | branch sv kids m =>
      simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact bmap_canon hwf.1 n (by omega) sv
    | leaf => simp [NodeV3.bmap] at hb
    | ext => simp [NodeV3.bmap] at hb
  refine chain_provided (k := 3) _ _ _ [st.e.getD 0 0, st.bm, st.hv] ?_ ?_ ?_ rfl
    (hwalkC hw st hst hm) (u := st.ub) ?_ hbal
  · intro m hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hprov m (Or.inl hm')
    · exact hprov m (Or.inr hm')
  · intro s hs
    obtain ⟨wv', hw', hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hs'
    have hst'' := List.mem_filter.mp hst'
    have hm2 : st'.mode = 2 := by simpa using hst''.2
    exact ⟨rfl, hwalkC hw' st' hst''.1 hm2, ((hR.canon wv' hw').2.2 st' hst''.1).2.2.1⟩
  · have := flatMap_filter_len (fun st : WStep3 => decide (st.mode = 2))
      (fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)) ws
    omega
  · exact List.mem_flatMap.mpr ⟨wv, hw, List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hm⟩, rfl⟩⟩


/-- **`edge_provided3`** (D1): with `walkU`'s walks on `EDGE`. -/
theorem edge_provided3D (hN : NodeWf3 vs) (hH : HeadWf hs) (hW : WalkWf3 ws)
    (hbal : BusBalD vs hs ws B_EDGE) (hkl : ∀ s ∈ vs, klen3 s.v < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode ≤ 1) :
    (∃ n, ∃ hn : n < vs.length, st.e ∈ edgesOf3 n vs[n]) ∨
      ∃ h ∈ hs, st.e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] := by
  obtain ⟨wx, hx, hb⟩ := hbal
  exact edge_provided3R hN hH (rowsOk_append (rowsOk_of_wf hW) (rowsOk_of_u hx)) hb
    (rows_append_lt hW hx) hkl (List.mem_append_left _ hw) hst hm

/-- **`bmap_provided3`** (D1): with `walkU`'s walks on `BMAP`. -/
theorem bmap_provided3D (hN : NodeWf3 vs) (hW : WalkWf3 ws)
    (hbal : BusBalD vs hs ws B_BMAP)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode = 2) :
    ∃ n, ∃ hn : n < vs.length, st.e.getD 0 0 = n ∧ vs[n].v.bmap = some (st.bm, st.hv) := by
  obtain ⟨wx, hx, hb⟩ := hbal
  exact bmap_provided3R hN (rowsOk_append (rowsOk_of_wf hW) (rowsOk_of_u hx)) hb
    (rows_append_lt hW hx) (List.mem_append_left _ hw) hst hm

end Prov

end ZkFormal.NearV3.D1.Link
