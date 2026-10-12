import ZkFormal.NearV3.Assembly.A7TraceRun

/-!
# ZkFormal.NearV3.Assembly.A7Trace — (E1): the `upsV3` plan is the spec's `traceUpsert` run, part by part

`PartsOk … parts`: part `k` of `parts` has the plan's kind `UKind.all[kd k]`, the plan's node `upsQ … k` as
output, and, if its kind replaces its source (`replK`), the plan's source `src k`.

* **`ups_termTrace`** (the terminal parts, by case, as `ups_term`): the run of `traceUpsert` at the terminal
  record `N_D` with the key left (`[0,15].drop (si − ti)`) has exactly the `nT` terminal parts of the plan
  (`close_gen`: lower parts, the top terminal part, the wrapping extension; the top output from `ups_term`);
* **`ups_traceUp`** (the upper parts, bottom-up as `ups_up`): every upper part pushes one part
  (`trace_rdb` / `trace_ext`), with output `upsQ k` (`traceUpsert_output` and `ups_up`); an `RDE` record's key
  is non-empty (the walk's descends, `ups_desc`);
* **`ups_trace`**: the run at the instance's root record has exactly the plan's parts (`A7Match.PartMatch`);
* **`ups_traceB_22`**: the same from the views, balances, `ShaHyp` and the interfaces (as `upsV3_linkB_22`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
open Render.UpsGen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.A7TraceRun

/-- Parts `0 … |parts| − 1` are the plan's. -/
def PartsOk (ci ti si x : Nat) (val : NearSpec.Bytes) (kd sdx : Nat → Nat) (src : Nat → NearSpec.PTrie)
    (parts : List TreePart) : Prop :=
  ∀ k q, parts[k]? = some q → q.kind = UKind.all.getD (kd k) .RDB ∧
    q.output = upsQ ci si ti x val kd sdx src k ∧ (TrieA7Repl.replK q.kind = true → q.source = src k)

section Gen
variable {ci ti si x : Nat} {val : NearSpec.Bytes} {kd sdx : Nat → Nat} {src : Nat → NearSpec.PTrie}

theorem partsOk_nil : PartsOk ci ti si x val kd sdx src [] := fun _ _ h => by simp at h

theorem partsOk_push {parts : List TreePart} {q : TreePart} (h : PartsOk ci ti si x val kd sdx src parts)
    (hk : q.kind = UKind.all.getD (kd parts.length) .RDB)
    (ho : q.output = upsQ ci si ti x val kd sdx src parts.length)
    (hs : TrieA7Repl.replK q.kind = true → q.source = src parts.length) :
    PartsOk ci ti si x val kd sdx src (parts ++ [q]) := by
  intro j q' hq
  rcases Nat.lt_or_ge j parts.length with hj | hj
  · rw [List.getElem?_append_left hj] at hq; exact h j q' hq
  · rw [List.getElem?_append_right hj] at hq
    rcases (show j = parts.length ∨ parts.length < j by omega) with rfl | hj'
    · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq; exact ⟨hk, ho, hs⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hq; cases hq

/-- One lower part. -/
theorem partsOk_one {q : TreePart} (hk : q.kind = UKind.all.getD (kd 0) .RDB)
    (ho : q.output = upsQ ci si ti x val kd sdx src 0)
    (hs : TrieA7Repl.replK q.kind = true → q.source = src 0) :
    PartsOk ci ti si x val kd sdx src [q] :=
  partsOk_push (parts := []) partsOk_nil hk ho hs

/-- Two lower parts. -/
theorem partsOk_two {q0 q1 : TreePart} (hk0 : q0.kind = UKind.all.getD (kd 0) .RDB)
    (ho0 : q0.output = upsQ ci si ti x val kd sdx src 0)
    (hs0 : TrieA7Repl.replK q0.kind = true → q0.source = src 0)
    (hk1 : q1.kind = UKind.all.getD (kd 1) .RDB)
    (ho1 : q1.output = upsQ ci si ti x val kd sdx src 1)
    (hs1 : TrieA7Repl.replK q1.kind = true → q1.source = src 1) :
    PartsOk ci ti si x val kd sdx src [q0, q1] :=
  partsOk_push (parts := [q0]) (partsOk_one hk0 ho0 hs0) hk1 ho1 hs1

/-- **Closing a terminal run**: lower parts, the top terminal part (`K`, output `B`), the wrapping extension. -/
theorem close_gen (run : TreeRun) (lower : List TreePart) (K : UKind) (srcN : NearSpec.PTrie) (sl : Nat)
    (p : List Nat) (B : NearSpec.PTrie) (nT j0 : Nat) (hj0 : lower.length = j0)
    (hparts : run.parts = lower ++ [⟨K, srcN, B, sl⟩] ++ wexL srcN p B)
    (hout : run.output = NearSpec.wrapExt p B)
    (hn : nT = j0 + 1 + (if p = [] then 0 else 1))
    (htop : run.output = upsQ ci si ti x val kd sdx src (nT - 1))
    (hq : upsQ ci si ti x val kd sdx src (nT - 1) = NearSpec.wrapExt p (upsQ ci si ti x val kd sdx src j0))
    (hK : UKind.all.getD (kd j0) .RDB = K)
    (hsrc : TrieA7Repl.replK K = true → srcN = src j0)
    (hW : p ≠ [] → kd (j0 + 1) = 9)
    (hlow : PartsOk ci ti si x val kd sdx src lower) :
    run.parts.length = nT ∧ PartsOk ci ti si x val kd sdx src run.parts := by
  subst hj0
  have hB : B = upsQ ci si ti x val kd sdx src lower.length :=
    wrapExt_inj p (by rw [← hout, htop, hq])
  have h1 := partsOk_push (q := ⟨K, srcN, B, sl⟩) hlow hK.symm hB hsrc
  refine ⟨?_, ?_⟩
  · rw [hparts, hn]; cases p <;> simp [wexL]
  · rw [hparts]
    cases p with
    | nil => simpa [wexL] using h1
    | cons a as =>
      have hn' : nT - 1 = lower.length + 1 := by rw [hn]; simp
      have h2 := partsOk_push (q := ⟨.WEX, srcN, NearSpec.wrapExt (a :: as) B, 0⟩) h1
        (by simp only [List.length_append, List.length_singleton]; rw [hW (by simp)]; rfl)
        (by simp only [List.length_append, List.length_singleton]; rw [← hn', ← htop, hout])
        (fun h => by simp [TrieA7Repl.replK] at h)
      simpa [wexL] using h2

theorem take_nil_iff (k : List Nat) (t : Nat) (h : t ≤ k.length) : k.take t = [] ↔ t = 0 := by
  rw [List.take_eq_nil_iff]; constructor
  · rintro (h0 | h0); · exact h0
    · subst h0; simp at h; exact h
  · intro h0; exact Or.inl h0

theorem hn_conv (nT base t : Nat) (k : List Nat) (hb : 1 ≤ base) (ht : t ≤ k.length)
    (hn : nT = base + (if 1 ≤ t then 1 else 0)) (lowerLen : Nat) (hl : lowerLen + 1 = base) :
    nT = lowerLen + 1 + (if k.take t = [] then 0 else 1) := by
  rw [hn]
  by_cases h : t = 0
  · rw [if_neg (by omega), if_pos ((take_nil_iff k t ht).2 h)]; omega
  · rw [if_pos (by omega), if_neg (fun e => h ((take_nil_iff k t ht).1 e))]; omega

end Gen

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

set_option maxHeartbeats 8000000 in
/-- **The terminal parts are the `traceUpsert` parts at the terminal record.** -/
theorem ups_termTrace :
    ∃ run, traceUpsert (fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di))) (UpsSpec.key.drop (si - ti))
        (sv (s.row 0 tau)) = some run ∧ run.parts.length = nTof ci ti ∧
      PartsOk ci ti si (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) run.parts := by
  have hw := E.ups
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  have hnT := nTof_pos ci i1 ti i2
  have hnT4 := nTof_le ci i1 ti i2
  have hlen := hP.len
  have hti := ups_tiLe E.walk hw hs hL hP
  have hTop : ∀ run, traceUpsert (fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)))
      (UpsSpec.key.drop (si - ti)) (sv (s.row 0 tau)) = some run →
      run.output = upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps)
        (nTof ci ti - 1) := by
    intro run hr
    obtain ⟨-, hU⟩ := ups_term E hs hL hP
    have := traceUpsert_output (fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)))
      (UpsSpec.key.drop (si - ti)) (sv (s.row 0 tau))
    rw [hr, hU] at this
    simpa using this
  -- terminal parts read `N_D`
  have srcT : ∀ j (hj : j < nTof ci ti), kd j ≠ 8 →
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)) := by
    intro j hj h8
    have hj' : j < ps.length := by omega
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; rfl
    obtain ⟨-, h1, h2, -, -, hsd, -⟩ := hP.term j hj' hj
    simp only [srcOf, hg]
    rw [(hP.src j hj' (by omega)).1, hsd]
  have hkdT : ∀ j (hj : j < nTof ci ti) (K : UKind), (termPlan (UCase.all.getD ci .LP) ti).getD j .RDB = K →
      kd j = K.ix := fun j hj K hK =>
    kd_eq _ (hP.part j (by omega)).1 K ((hP.term j (by omega) hj).1.trans hK)
  -- the record `N_D`
  have hNlt : s.row 0 (11 + di) < vs.length := by
    have hj : nTof ci ti - 1 < nTof ci ti := by omega
    have h8 : kd (nTof ci ti - 1) ≠ 8 := by
      intro h
      have := termLast ci i1 ti i2
      rw [← (hP.term _ (by omega) hj).1, h] at this
      exact this rfl
    have := part_sN E.node hw E.upb hs hL hP (nTof ci ti - 1) (by omega)
    obtain ⟨-, -, h2', -, -, hsd, -⟩ := hP.term (nTof ci ti - 1) (by omega) hj
    rwa [(hP.src (nTof ci ti - 1) (by omega) (by omega)).1, hsd] at this
  have hTN := post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hNlt
  have hshape := ups_shape E hs hL hP
  have hok := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hNlt
  obtain ⟨tL, tE, tB⟩ := tn_cases (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
    (Link3.vpos (Link3.vid0 es)) vs[s.row 0 (11 + di)].v
  rw [← hTN] at tL tE tB
  obtain ⟨hstepT, hT1, hT2, hT3, hci2, hnI, -, -, -, hK, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨-, -, -, hNT⟩ := ups_levels hw hs hL hP
  have RK := rowKey E.node E.head E.par E.walk hw hs hL hP (si + 1) (by omega) (Nat.le_refl _)
  rw [hNT, hnI] at RK
  obtain ⟨-, RK⟩ := RK
  rw [show si + 1 - 1 - ti = si - ti by omega] at RK
  obtain ⟨kL, kE, kB⟩ := RK _ (List.getElem?_eq_getElem hNlt)
  have tEdge : s.row (si + 1) mS = 1 ∨ s.row (si + 1) mK = 1 → (s.row (si + 1) nib ≠ SYM_START ∨
      s.row (si + 1) ek ≠ EK_DOWN) → [s.row 0 (11 + di), ti, s.row (si + 1) nib, s.row (si + 1) nN2,
        s.row (si + 1) nI2, s.row (si + 1) ek] ∈ edgesOf3 (s.row 0 (11 + di)) vs[s.row 0 (11 + di)] := by
    intro hm hnh
    obtain ⟨r, hr, he⟩ := rowEdge E.walk hw hs hL (si + 1) (by omega) hm hnh
    rw [hNT] at hr; rw [hNT, hnI] at he
    rw [List.getElem?_eq_getElem hNlt] at hr
    cases hr; exact he
  have mveL : ∀ j (hj : j < ps.length), kd j = 7 → ∀ key c m,
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = .ext key c m → ti + 1 < key.length := by
    intro j hj h7 key c m hsj
    have hb := (ups_partsAllV E hs hL hP j hj).1
    have hq : upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) j =
        UpsSpec.qMVE key c m ti := by rw [upsQ_eq, h7, hsj]; rfl
    rw [hq] at hb
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape j hj
    obtain ⟨k', c', m', he', hI⟩ := s7 h7
    rw [hsj] at he'; simp only [NearSpec.PTrie.ext.injEq] at he'; obtain ⟨rfl, rfl, rfl⟩ := he'
    have hn := part_sN E.node hw E.upb hs hL hP j hj
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have ho := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hn
    simp only [srcOf, hg] at hsj
    rw [hsj] at ho
    exact mveLong hw hs hL hP j hj h7 key c m (ho.ext key c m rfl).2.2 hb hI
  have esxL : ∀ j (hj : j < ps.length), kd j = 10 → spXN ci = 1 → ∀ key c m,
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = .ext key c m → key.length = ti + 1 := by
    intro j hj h10 hX key c m hsj
    have hn := part_sN E.node hw E.upb hs hL hP j hj
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have ho := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hn
    simp only [srcOf, hg] at hsj
    rw [hsj] at ho
    have hTj := post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hn
    obtain ⟨-, tE', -⟩ := tn_cases (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
      (Link3.vpos (Link3.vid0 es)) vs[s.row ps[j].1 sN].v
    rw [← hTj] at tE'
    obtain ⟨kid, mB, hv⟩ := tE' key c m hsj
    have hwf := E.node.wf _ (List.getElem_mem hn)
    rw [hv] at hwf
    have hPb : postB vs (s.row ps[j].1 sN) = vs[s.row ps[j].1 sN].v.ser true := by
      simp only [postB]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    have hR : UpbReads s (postB vs) := fun i hi hrd => upb_reads E.node hw E.upb hs i hi hrd
    refine esx1Len hw hs hL hP j hj h10 hX (postB vs) hR key (ho.ext key c m rfl).2.1 ?_ ?_
    · rw [hPb,hv]
      have hb : (kid.bytes true).length=32 := by
        cases kid with
        | none => exact absurd rfl hwf.2.1
        | hash h => exact hwf.2.2.1
        | node n l r pre po => exact hwf.2.2.1.2
      simp [NodeV3.ser, u32Bytes_length, hpN, UpsSpec.hp_len, hb, hwf.2.2.2]
      omega
    · rw [hPb, hv]; exact ser5_ext key kid mB hwf.1
  generalize hval : sv (s.row 0 tau) = val at hTop
  generalize hsrc : srcOf (Rpost vs es) (Vpost vs es pv) s ps = src at srcT hshape mveL esxL hTop
  generalize hTT : fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)) = TN at srcT tL tE tB hok hTop
  generalize hrv : vs[s.row 0 (11 + di)].v = rv at kL kE kB tL tE tB tEdge
  -- common facts
  have hXl : ∀ t, t ≤ si → (UpsSpec.key.drop (si - t)).length = 2 - si + t := by
    intro t ht; simp [UpsSpec.key]; omega
  have hkey' := key'_drop ti si hti
  have Q0 := upsQ_zero ci si ti (s.row 0 tX) val kd sdx src
  have Qn := fun j (hj : 1 ≤ j) => upsQ_next ci si ti (s.row 0 tX) val kd sdx src j hj
  have F := wRowF hw hs hL (si + 1) (by omega)
  have hseg := hP.seg 0 (by have := hL.walk.1; omega)
  have spbF : 4 ≤ ci → s.row 0 tX < 16 ∧ (spYN ci = 1 → si ≤ 1) := by
    intro h4
    obtain ⟨c1, -, -, c4⟩ := hseg
    obtain ⟨a, -, -, b⟩ := spbSeg (okRow hw hs (i := 0) (by have := hL.walk.1; omega)) (rowLt hw hs _)
      (nextLt hw hs _) hL.walk.2.1 c1 c4 h4 (by omega) i4
    exact ⟨a, b⟩
  have keyT : 4 ≤ ci → ci ≠ 4 →
      (∀ k sl m, rv = .leaf k sl m → ti < k.length ∧ k.getD ti 0 = s.row 0 tX) ∧
      (∀ k kid m, rv = .ext k kid m → ti < k.length ∧ k.getD ti 0 = s.row 0 tX) := by
    intro h4 hne
    obtain ⟨hekK, hnib⟩ := (hK h4).2 hne
    have hm : s.row (si + 1) mK = 1 := by rw [hT3, if_pos h4]
    have he := tEdge (Or.inr hm) (Or.inr (by rw [hekK]; decide))
    have hσ : s.row (si + 1) nib < 16 := by
      rw [hnib, hL.segc _ (by have := hL.walk.1; omega) tX (by decide)]; exact (spbF h4).1
    have C := stepEdge he (by simpa using hσ) (Or.inr (by simpa using hekK))
    simp only [List.getD_cons_succ, List.getD_cons_zero] at C
    rw [hrv, hnib, hL.segc _ (by have := hL.walk.1; omega) tX (by decide)] at C
    refine ⟨fun k sl m hv => ?_, fun k kid m hv => ?_⟩ <;> rw [hv] at C
    · rcases C with ⟨_, _, _, _, _, _, _, _, h, -⟩ | ⟨k', _, _, h, h1, h2, -⟩ | ⟨_, _, _, h, -⟩ <;>
        simp at h
      obtain ⟨rfl, -⟩ := h; exact ⟨h1, h2⟩
    · rcases C with ⟨_, _, _, _, _, _, _, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨k', _, _, h, h1, h2, -⟩ <;>
        simp at h
      obtain ⟨rfl, -⟩ := h; exact ⟨h1, h2⟩
  have getI : ∀ (k : List Nat) (h : ti < k.length), k.getD ti 0 = s.row 0 tX → k[ti] = s.row 0 tX := by
    intro k h e; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] at e; exact e
  have planK : ∀ j (hj : j < nTof ci ti) (K : UKind), (termPlan (UCase.all.getD ci .LP) ti).getD j .RDB = K →
      kd j = K.ix := hkdT
  -- the common prefix in the split cases
  have cpL : ∀ k : List Nat, k.take ti = (UpsSpec.key.drop (si - ti)).take ti → ti ≤ k.length →
      ti ≤ (UpsSpec.key.drop (si - ti)).length →
      (k.length = ti ∨ (UpsSpec.key.drop (si - ti)).length = ti ∨
        k[ti]? ≠ (UpsSpec.key.drop (si - ti))[ti]?) →
      (NearSpec.commonPrefix k (UpsSpec.key.drop (si - ti))) = k.take ti ∧
      (NearSpec.commonPrefix k (UpsSpec.key.drop (si - ti))).length = ti := by
    intro k hpre h1 h2 h3
    have hcp := commonPrefix_eq k _ ti hpre h1 h2 h3
    refine ⟨hcp, ?_⟩
    rw [hcp, List.length_take]; omega
  have kdrop : (UpsSpec.key.drop (si - ti)).drop ti = UpsSpec.key.drop si := hkey'
  -- `NLF` / `MVL` / `MVE` lower parts
  have nlfOk : ∀ j, kd j = 8 → ∀ srcN : NearSpec.PTrie,
      (⟨.NLF, srcN, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩ : TreePart).output =
        upsQ ci si ti (s.row 0 tX) val kd sdx src j := by
    intro j h8 srcN
    rw [upsQ_eq, h8]; rfl
  rcases (show ci = 0 ∨ ci = 1 ∨ ci = 2 ∨ ci = 3 ∨ ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10
    by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `LP`: a present leaf
    have hn : nTof 0 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 2 := planK 0 (by omega) .RLP (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := hci2 (by omega)
    obtain ⟨-, -, s2, -⟩ := hshape 0 (by omega)
    obtain ⟨k, sl, m, hT⟩ := s2 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    have hm3 : s.row (si + 1) mS = 1 := by rw [hT1]; simp
    have hekV := (F.stepE hm3).2.2 (by omega)
    have he := tEdge (Or.inl hm3) (Or.inl (by rw [(F.stepE hm3).1, show si + 1 = 3 by omega]; decide))
    rcases edge_val he (by simpa using hekV) with ⟨k', sl'', m'', hv', hp⟩ | ⟨sl'', kids, m'', hv', hp⟩
    · rw [hrv, hv] at hv'; simp only [NodeV3.leaf.injEq] at hv'; obtain ⟨rfl, -⟩ := hv'
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
      obtain ⟨-, htk⟩ := kL k sl' mB hv
      have hl := hXl ti hti
      have hkk : k = UpsSpec.key.drop (si - ti) := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at htk; exact htk
      rw [hT, ← hkk] at hTop ⊢
      have hr := A7TraceRun.trace_leaf_eq k sl m val
      refine ⟨_, hr, close_gen _ [] .RLP (.leaf k sl m) 0 [] (NearSpec.newLeaf k val) (nTof 0 ti) 0 rfl rfl rfl
        (by rw [hn]; rfl) (hTop _ hr) (by rw [hn]; rfl) (by rw [k0]; rfl)
        (fun _ => by rw [srcT 0 (by omega) (by omega), hT]) (fun h => absurd rfl h) partsOk_nil⟩
    · rw [hrv, hv] at hv'; cases hv'
  · -- `BR`: a branch value replaced
    have hn : nTof 1 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 3 := planK 0 (by omega) .RBR (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := hci2 (by omega)
    obtain ⟨-, -, -, s3, -⟩ := hshape 0 (by omega)
    obtain ⟨sl, cs, m, hT⟩ := s3 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    subst hsi; subst h0
    rw [hT] at hTop ⊢
    obtain ⟨run, hr, hp⟩ := A7TraceRun.trace_branch_nil (some sl) cs m val
    refine ⟨run, hr, close_gen run [] .RBR (.branch (some sl) cs m) 0 [] run.output (nTof 1 0) 0 rfl (by rw [hp]; rfl)
      rfl (by rw [hn]; rfl) (hTop _ hr) (by rw [hn]; rfl) (by rw [k0]; rfl)
      (fun _ => by rw [srcT 0 (by omega) (by omega), hT]) (fun h => absurd rfl h) partsOk_nil⟩
  · -- `BV`: a branch value set
    have hn : nTof 2 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 4 := planK 0 (by omega) .RBV (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, s4, -⟩ := hshape 0 (by omega)
    obtain ⟨cs, m, hT⟩ := s4 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    subst hsi; subst h0
    rw [hT] at hTop ⊢
    obtain ⟨run, hr, hp⟩ := A7TraceRun.trace_branch_nil none cs m val
    refine ⟨run, hr, close_gen run [] .RBV (.branch none cs m) 0 [] run.output (nTof 2 0) 0 rfl (by rw [hp]; rfl)
      rfl (by rw [hn]; rfl) (hTop _ hr) (by rw [hn]; rfl) (by rw [k0]; rfl)
      (fun _ => by rw [srcT 0 (by omega) (by omega), hT]) (fun h => absurd rfl h) partsOk_nil⟩
  · -- `BI`: an empty slot
    have hn : nTof 3 ti = 2 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k1 : kd 1 = 5 := planK 1 (by omega) .RBI (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k0 : kd 0 = 8 := planK 0 (by omega) .NLF (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi := rbiSi hw hs hL hP 1 (by omega) k1
    obtain ⟨-, -, -, -, -, s5, -⟩ := hshape 1 (by omega)
    obtain ⟨bv, cs, m, hT, hy⟩ := s5 k1
    rw [srcT 1 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    have h16 := (hok.branch bv cs m hT).1
    subst h0
    rw [hT, Nat.sub_zero, key_drop si (by omega)] at hTop ⊢
    obtain ⟨run, hr, hp⟩ := A7TraceRun.trace_rbi bv cs m (UpsSpec.yOf si) (UpsSpec.ysOf si) val
      (by rw [h16]; rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide) hy
    refine ⟨run, hr, close_gen run [⟨.NLF, .branch bv cs m, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩] .RBI
      (.branch bv cs m) (UpsSpec.yOf si) [] run.output (nTof 3 0) 1 rfl (by rw [hp]; rfl)
      rfl (by rw [hn]; rfl) (hTop _ hr) (by rw [hn]; rfl) (by rw [k1]; rfl)
      (fun _ => by rw [srcT 1 (by omega) (by omega), hT]) (fun h => absurd rfl h)
      (partsOk_one (by rw [k0]; rfl) (nlfOk 0 k0 _) (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `LSa`
    have hn : nTof 4 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k0 : kd 0 = 8 := planK 0 (by rw [hn]; split <;> omega) .NLF
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 1 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT⟩ := (s10 k1).1 rfl
    rw [srcT 1 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨hkl, htk⟩ := kL k sl' mB hv
    have hm : s.row (si + 1) mK = 1 := by rw [hT3, if_pos (by omega)]
    have hekL := (hK (by omega)).1 rfl
    have he := tEdge (Or.inr hm) (Or.inr (by rw [hekL]; decide))
    obtain ⟨k', sl'', m'', hv', hp⟩ := edge_lendAt he (by simpa using hekL)
    rw [hrv, hv] at hv'; simp only [NodeV3.leaf.injEq] at hv'; obtain ⟨rfl, -⟩ := hv'
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega) (Or.inl hp.symm)
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_leaf_ne k sl m (UpsSpec.key.drop (si - ti)) val (ne_of_len (by omega))
    obtain ⟨B, hparts, hout⟩ := leafSplit_a k sl m (UpsSpec.key.drop (si - ti)) val (UpsSpec.yOf si) (UpsSpec.ysOf si)
      (by rw [hcpl]; simp; omega) (by rw [hcpl, kdrop, key_drop si (by omega)])
    rw [hcp] at hparts hout
    refine ⟨_, hr, close_gen _ [⟨.NLF, .leaf k sl m, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩] .SPB
      (.leaf k sl m) 0 (k.take ti) B (nTof 4 ti) 1 rfl hparts hout
      (hn_conv _ 2 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 4 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk) (by rw [k1]; rfl)
      (fun _ => by rw [srcT 1 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_one (by rw [k0]; rfl) (nlfOk 0 k0 _) (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `LSb`
    have hn : nTof 5 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 6 := planK 0 (by rw [hn]; split <;> omega) .MVL
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, s6, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT, hI⟩ := s6 k0
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨-, htk⟩ := kL k sl' mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).1 k sl' mB hv
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega) (Or.inr (Or.inl (by omega)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_leaf_ne k sl m (UpsSpec.key.drop (si - ti)) val (ne_of_len (by omega))
    obtain ⟨B, hparts, hout⟩ := leafSplit_b k sl m (UpsSpec.key.drop (si - ti)) val k[ti] (k.drop (ti + 1))
      (by rw [hcpl]; exact drop_cons_of hlt) (by rw [hcpl, kdrop, hsi]; rfl)
    rw [hcp] at hparts hout
    refine ⟨_, hr, close_gen _ [⟨.MVL, .leaf k sl m, .leaf (k.drop (ti + 1)) sl (NearSpec.leafMem (k.drop (ti + 1)) sl.len), 0⟩]
      .SPB (.leaf k sl m) 0 (k.take ti) B (nTof 5 ti) 1 rfl hparts hout
      (hn_conv _ 2 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 5 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk) (by rw [k1]; rfl)
      (fun _ => by rw [srcT 1 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_one (by rw [k0]; rfl) (by rw [upsQ_eq, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]; rfl)
        (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `LSc`
    have hn : nTof 6 ti = 3 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 3 = 9 := fun h => planK 3 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 6 := planK 0 (by rw [hn]; split <;> omega) .MVL
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 8 := planK 1 (by rw [hn]; split <;> omega) .NLF
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k2 : kd 2 = 10 := planK 2 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 6) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, s6, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT, hI⟩ := s6 k0
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨-, htk⟩ := kL k sl' mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).1 k sl' mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega)
      (Or.inr (Or.inr (by rw [List.getElem?_eq_getElem hly, hy, List.getElem?_eq_getElem hlt]; simpa using hxk)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_leaf_ne k sl m (UpsSpec.key.drop (si - ti)) val (ne_of_get hlt hly (by rw [hy]; exact hxk))
    obtain ⟨B, hparts, hout⟩ := leafSplit_c k sl m (UpsSpec.key.drop (si - ti)) val k[ti] (k.drop (ti + 1)) (UpsSpec.yOf si) (UpsSpec.ysOf si)
      (by rw [hcpl]; exact drop_cons_of hlt) (by rw [hcpl, kdrop, key_drop si (by omega)])
    rw [hcp] at hparts hout
    refine ⟨_, hr, close_gen _ [⟨.MVL, .leaf k sl m, .leaf (k.drop (ti + 1)) sl (NearSpec.leafMem (k.drop (ti + 1)) sl.len), 0⟩,
        ⟨.NLF, .leaf k sl m, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩]
      .SPB (.leaf k sl m) 0 (k.take ti) B (nTof 6 ti) 2 rfl hparts hout
      (hn_conv _ 3 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 6 si ti (s.row 0 tX) val kd sdx src 3 (by omega) hn hkW k htk) (by rw [k2]; rfl)
      (fun _ => by rw [srcT 2 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_two (by rw [k0]; rfl) (by rw [upsQ_eq, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]; rfl)
        (fun h => by simp [TrieA7Repl.replK] at h) (by rw [k1]; rfl) (nlfOk 1 k1 _)
        (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `ESl0`
    have hn : nTof 7 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 7 := planK 0 (by rw [hn]; split <;> omega) .MVE
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT, hI⟩ := s7 k0
    have hlong := mveL 0 (by rw [hlen, hn]; split <;> omega) k0 k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega) (Or.inr (Or.inl (by omega)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_ext_ne k c m (UpsSpec.key.drop (si - ti)) val (take_ne_of_len (by omega))
    have hd1 : k.drop (ti + 1) = k[ti + 1] :: k.drop (ti + 2) := drop_cons_of hlong
    obtain ⟨B, hparts, hout⟩ := extSplit_l0 k c m (UpsSpec.key.drop (si - ti)) val k[ti] k[ti + 1] (k.drop (ti + 2))
      (by rw [hcpl, drop_cons_of (show ti < k.length by omega), hd1]) (by rw [hcpl, kdrop, hsi]; rfl)
    rw [hcp, ← hd1] at hparts
    rw [hcp] at hout
    refine ⟨_, hr, close_gen _ [⟨.MVE, .ext k c m, .ext (k.drop (ti + 1)) c
        (NearSpec.extOwnMem (k.drop (ti + 1)) + (m - NearSpec.extOwnMem k)), 0⟩]
      .SPB (.ext k c m) 0 (k.take ti) B (nTof 7 ti) 1 rfl hparts hout
      (hn_conv _ 2 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 7 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk) (by rw [k1]; rfl)
      (fun _ => by rw [srcT 1 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_one (by rw [k0]; rfl) (by rw [upsQ_eq, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]; rfl)
        (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `ESl1`
    have hn : nTof 8 ti = 1 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 1 = 9 := fun h => planK 1 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 10 := planK 0 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT⟩ := (s10 k0).2 (by decide)
    have hkl := esxL 0 (by rw [hlen, hn]; split <;> omega) k0 (by decide) k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega) (Or.inr (Or.inl (by omega)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_ext_ne k c m (UpsSpec.key.drop (si - ti)) val (take_ne_of_len (by omega))
    obtain ⟨B, hparts, hout⟩ := extSplit_l1 k c m (UpsSpec.key.drop (si - ti)) val (k[ti]'(by omega))
      (by rw [hcpl, drop_cons_of (show ti < k.length by omega), List.drop_eq_nil_of_le (by omega)]) (by rw [hcpl, kdrop, hsi]; rfl)
    rw [hcp] at hparts hout
    refine ⟨_, hr, close_gen _ [] .SPB (.ext k c m) 0 (k.take ti) B (nTof 8 ti) 0 rfl hparts hout
      (hn_conv _ 1 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 8 si ti (s.row 0 tX) val kd sdx src 1 (Nat.le_refl _) hn hkW k htk) (by rw [k0]; rfl)
      (fun _ => by rw [srcT 0 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      partsOk_nil⟩
  · -- `ESn0`
    have hn : nTof 9 ti = 3 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 3 = 9 := fun h => planK 3 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 7 := planK 0 (by rw [hn]; split <;> omega) .MVE
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 8 := planK 1 (by rw [hn]; split <;> omega) .NLF
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k2 : kd 2 = 10 := planK 2 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 9) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT, hI⟩ := s7 k0
    have hlong := mveL 0 (by rw [hlen, hn]; split <;> omega) k0 k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega)
      (Or.inr (Or.inr (by rw [List.getElem?_eq_getElem hly, hy, List.getElem?_eq_getElem hlt]; simpa using hxk)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_ext_ne k c m (UpsSpec.key.drop (si - ti)) val (take_ne_of_get hlt hly (by rw [hy]; exact hxk))
    have hd1 : k.drop (ti + 1) = k[ti + 1] :: k.drop (ti + 2) := drop_cons_of hlong
    obtain ⟨B, hparts, hout⟩ := extSplit_n0 k c m (UpsSpec.key.drop (si - ti)) val k[ti] k[ti + 1] (k.drop (ti + 2))
      (UpsSpec.yOf si) (UpsSpec.ysOf si)
      (by rw [hcpl, drop_cons_of hlt, hd1]) (by rw [hcpl, kdrop, key_drop si (by omega)])
    rw [hcp, ← hd1] at hparts
    rw [hcp] at hout
    refine ⟨_, hr, close_gen _ [⟨.MVE, .ext k c m, .ext (k.drop (ti + 1)) c
        (NearSpec.extOwnMem (k.drop (ti + 1)) + (m - NearSpec.extOwnMem k)), 0⟩,
        ⟨.NLF, .ext k c m, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩]
      .SPB (.ext k c m) 0 (k.take ti) B (nTof 9 ti) 2 rfl hparts hout
      (hn_conv _ 3 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 9 si ti (s.row 0 tX) val kd sdx src 3 (by omega) hn hkW k htk) (by rw [k2]; rfl)
      (fun _ => by rw [srcT 2 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_two (by rw [k0]; rfl) (by rw [upsQ_eq, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]; rfl)
        (fun h => by simp [TrieA7Repl.replK] at h) (by rw [k1]; rfl) (nlfOk 1 k1 _)
        (fun h => by simp [TrieA7Repl.replK] at h))⟩
  · -- `ESn1`
    have hn : nTof 10 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 8 := planK 0 (by rw [hn]; split <;> omega) .NLF
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 10) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 1 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT⟩ := (s10 k1).2 (by decide)
    have hkl := esxL 1 (by rw [hlen, hn]; split <;> omega) k1 (by decide) k c m hT
    rw [srcT 1 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hl := hXl ti hti
    obtain ⟨hcp, hcpl⟩ := cpL k htk (by omega) (by omega)
      (Or.inr (Or.inr (by rw [List.getElem?_eq_getElem hly, hy, List.getElem?_eq_getElem hlt]; simpa using hxk)))
    rw [hT] at hTop ⊢
    have hr := A7TraceRun.trace_ext_ne k c m (UpsSpec.key.drop (si - ti)) val (take_ne_of_get hlt hly (by rw [hy]; exact hxk))
    obtain ⟨B, hparts, hout⟩ := extSplit_n1 k c m (UpsSpec.key.drop (si - ti)) val k[ti] (UpsSpec.yOf si) (UpsSpec.ysOf si)
      (by rw [hcpl, drop_cons_of hlt, List.drop_eq_nil_of_le (by omega)]) (by rw [hcpl, kdrop, key_drop si (by omega)])
    rw [hcp] at hparts hout
    refine ⟨_, hr, close_gen _ [⟨.NLF, .ext k c m, NearSpec.newLeaf (UpsSpec.ysOf si) val, 0⟩]
      .SPB (.ext k c m) 0 (k.take ti) B (nTof 10 ti) 1 rfl hparts hout
      (hn_conv _ 2 ti k (by omega) (by omega) hn _ rfl) (hTop _ hr)
      (wexTop 10 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk) (by rw [k1]; rfl)
      (fun _ => by rw [srcT 1 (by rw [hn]; split <;> omega) (by omega), hT])
      (fun h => hkW (Nat.pos_of_ne_zero (fun h0 => h ((take_nil_iff k ti (by omega)).2 h0))))
      (partsOk_one (by rw [k0]; rfl) (nlfOk 0 k0 _) (fun h => by simp [TrieA7Repl.replK] at h))⟩


/-- **The upper parts, bottom-up**: the run at every part from the top terminal part up has exactly the plan's
parts so far. -/
theorem ups_traceUp {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) :
    ∀ k, nTof ci ti ≤ k + 1 → k < ps.length →
      ∃ run, traceUpsert (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)
          (UpsSpec.key.drop (Eoff di si ti (lvlOf s ps kd sdx k))) (sv (s.row 0 tau)) = some run ∧
        run.parts.length = k + 1 ∧
        PartsOk ci ti si (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps)
          run.parts := by
  have i12 := hP.ix
  have hnT := nTof_pos ci i12.1 ti i12.2.1
  have base : ∀ k, k + 1 = nTof ci ti → k < ps.length →
      ∃ run, traceUpsert (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)
          (UpsSpec.key.drop (Eoff di si ti (lvlOf s ps kd sdx k))) (sv (s.row 0 tau)) = some run ∧
        run.parts.length = k + 1 ∧
        PartsOk ci ti si (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps)
          run.parts := by
    intro k hk1 hk
    obtain ⟨run, hr, hl, hok⟩ := ups_termTrace E hs hL hP
    have h0 := termK hP k hk (by omega)
    obtain ⟨-, -, -, -, -, hsd, -⟩ := hP.term k hk (by omega)
    have hsrc := (hP.src k hk (by omega)).1
    have hlv : lvlOf s ps kd sdx k = di := by unfold lvlOf; rw [if_neg (by omega), hsd]
    have hsk : srcOf (Rpost vs es) (Vpost vs es pv) s ps k =
        fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)) := by
      simp only [srcOf, getD_ps hk, hsrc, hsd]
    have hE : Eoff di si ti di = si - ti := by simp [Eoff]
    rw [hlv, hsk, hE]
    exact ⟨run, hr, by omega, hok⟩
  intro k
  induction k with
  | zero => intro hT hk; exact base 0 (by omega) hk
  | succ k ih =>
    intro hT hk
    by_cases hTk : k + 2 ≤ nTof ci ti
    · exact base (k + 1) (by omega) hk
    have hT1 : nTof ci ti ≤ k + 1 := by omega
    obtain ⟨run, hr, hlen, hok⟩ := ih (by omega) (by omega)
    have hl := lvl_succ hP k hk hT1
    rw [hl] at hr
    obtain ⟨r, hr', c, l, cr, pre, po, hcs, ⟨hc, -⟩, hPT, hDB, hDE⟩ := ups_ch E hs hL hP hC k hk hT1
    obtain ⟨hn, hsrcE⟩ := src_eq E hs hL hP (k + 1) hk
    rw [List.getElem?_eq_getElem hn, Option.some.injEq] at hr'
    subst hr'
    have hsk : srcOf (Rpost vs es) (Vpost vs es pv) s ps k = fullTree (Rpost vs es) (Vpost vs es pv) c := by
      simp only [srcOf, getD_ps (show k < ps.length by omega), hcs]
    rw [hsk] at hr
    have hcm : (fullTree (Rpost vs es) (Vpost vs es pv) c).mem? =
        some (fullTree (Rpost vs es) (Vpost vs es pv) c).memD := by
      rw [post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hc]; exact nodeTree_mem _ _ _
    have hstep : ∃ q : TreePart, traceUpsert (srcOf (Rpost vs es) (Vpost vs es pv) s ps (k + 1))
        (UpsSpec.key.drop (Eoff di si ti (lvlOf s ps kd sdx (k + 1)))) (sv (s.row 0 tau)) = some (pushPart run q) ∧
        q.kind = UKind.all.getD (kd (k + 1)) .RDB ∧ q.source = srcOf (Rpost vs es) (Vpost vs es pv) s ps (k + 1) := by
      rw [hsrcE]
      rcases upperK hP (k + 1) hk hT1 with h1 | h11
      · rcases (show kd (k + 1) = 0 ∨ kd (k + 1) = 1 by omega) with h0 | h1e
        · obtain ⟨hd2, hEd, hEd1, sv', kids, m, hv, hkid⟩ := hDB h0
          have hrc := hP.desc (k + 1) hk (by omega)
          have hlk : lvlOf s ps kd sdx (k + 1) = sdx (k + 1) := by unfold lvlOf; rw [if_neg (by omega)]
          rw [hrc, hEd1] at hr
          rw [hlk, hEd, slot_key _ hd2, hv, h0]
          simp only [NodeV3.toRec3, nodeTree3]
          obtain ⟨q, e1, e2, e3⟩ := trace_rdb _ _ _ _ _ _ _ _ _ (kidAt_node _ kids _ hkid) hcm hr
          exact ⟨q, e1, by rw [e2]; rfl, e3⟩
        · obtain ⟨kk, m, hv, hkk, hE1⟩ := hDE h1e
          have hrc := hP.desc (k + 1) hk (by omega)
          have hlk : lvlOf s ps kd sdx (k + 1) = sdx (k + 1) := by unfold lvlOf; rw [if_neg (by omega)]
          have hlt := descLt E.ups hs hL hP (k + 1) hk (by omega)
          have hEs : Eoff di si ti (sdx (k + 1)) = sdx (k + 1) := by unfold Eoff; rw [if_neg (by omega)]
          obtain ⟨-, hD⟩ := ups_desc E.node E.head E.par E.walk E.ups hs hL hP
          obtain ⟨i, -, -, -, -, -, hiI, hEi⟩ := hD (sdx (k + 1)) hlt
          have hkkne : kk.isEmpty = false := by
            cases kk with
            | nil => simp only [List.length_nil, Nat.add_zero] at hE1; omega
            | cons _ _ => rfl
          rw [hrc, hE1] at hr
          rw [hlk, hv, h1e]
          simp only [NodeV3.toRec3, nodeTree3, kidTree3, NKid.toKid3]
          obtain ⟨q, e1, e2, e3⟩ := trace_ext _ _ _ _ _ _ _ hkk.symm hcm (by rw [List.drop_drop]; exact hr)
          exact ⟨q, e1, by rw [e2, hkkne]; rfl, e3⟩
      · obtain ⟨m, hv⟩ := hPT h11
        have hlk : lvlOf s ps kd sdx (k + 1) = s.row ps[k + 1].1 UpsV3.rc := by
          unfold lvlOf; rw [if_pos h11, getD_ps hk]
        rw [hlk, hv, h11]
        simp only [NodeV3.toRec3, nodeTree3, kidTree3, NKid.toKid3]
        obtain ⟨q, e1, e2, e3⟩ := trace_ext [] _ _ _ _ _ _ (by simp) hcm (by simpa using hr)
        exact ⟨q, e1, by rw [e2]; rfl, e3⟩
    obtain ⟨q, htr, hqk, hqs⟩ := hstep
    have hU := ups_up E hs hL hP hC (k + 1) hT (by omega)
    have ho := traceUpsert_output (srcOf (Rpost vs es) (Vpost vs es pv) s ps (k + 1))
      (UpsSpec.key.drop (Eoff di si ti (lvlOf s ps kd sdx (k + 1)))) (sv (s.row 0 tau))
    rw [htr, hU] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    refine ⟨pushPart run q, htr, by simp [pushPart, hlen], ?_⟩
    simp only [pushPart]
    exact partsOk_push hok (by rw [hlen, hqk]) (by rw [hlen, ← ho]; rfl) (fun _ => by rw [hlen, hqs])

/-- **(E1) for a segment**: the spec's run at the instance's root record has exactly the plan's parts. -/
theorem ups_trace {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) (run : TreeRun)
    (hr : traceUpsert (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid) UpsSpec.key
      (sv (s.row 0 tau)) = some run) :
    A7Match.PartMatch (Rpost vs es) (Vpost vs es pv) s ps ci ti si kd sdx (sv (s.row 0 tau)) run := by
  have hne := hL.nonempty
  have hT : nTof ci ti ≤ ps.length - 1 + 1 := by have := hP.len; omega
  obtain ⟨run', hr', hlen, hok⟩ := ups_traceUp E hs hL hP hC (ps.length - 1) hT (by omega)
  rw [lvl_top hP hne] at hr'
  obtain ⟨hE0, -⟩ := ups_desc E.node E.head E.par E.walk E.ups hs hL hP
  rw [hE0, List.drop_zero] at hr'
  have hroot := ups_rootSrc hC E.ups hs hL hP (ps.length - 1) (by omega) (by omega)
  have hsk : srcOf (Rpost vs es) (Vpost vs es pv) s ps (ps.length - 1) =
      fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid := by
    simp only [srcOf, getD_ps (show ps.length - 1 < ps.length by omega), hroot]
  rw [hsk, hr] at hr'
  have e := Option.some.inj hr'
  subst e
  refine ⟨by omega, fun k hk => ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, run.parts[k]? = some q := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a, b, c⟩ := hok k q hq
  exact ⟨q, hq, a, b, c⟩

end

/-- **(E1) from the views, balances, `ShaHyp` and the interfaces** (the hypotheses of `upsV3_linkB_22`). -/
theorem ups_traceB_22 {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
    {othersU : List Msg} {ws : List WalkR} {prov : List Msg} {K : Nat} {r0 rK : List Nat}
    (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hw : UpsWf v) (hW : WalkWf3 ws)
    (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 22)
    (hb : Link3.ParentBal vs hds) (hvb : Link3.VParentBal vs es) (hupb : UpbBal vs v)
    (hE : WalkBal vs hds ws v B_EDGE) (hB : WalkBal vs hds ws v B_BMAP) (hKn : Link3.KeynibOk ws prov)
    (hbytesU : ∀ m, shaR B_BYTES m = ZkFormal.Near.cnt ((upsTraffic v).sends B_BYTES ++ othersU) m)
    (hothU : ∀ m ∈ othersU, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdigU : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (hmemd : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (hK : K + 1 < P) (hK17 : K < 2 ^ 17) (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
    (hROOT : (([[0] ++ r0] ++ (upsTraffic v).sends B_ROOT).map Msg.toFp).Perm
      ((headRecvs hds B_ROOT ++ [[K + 1] ++ rK]).map Msg.toFp))
    (hMID : ((headSends hds B_MIDROOT).map Msg.toFp).Perm (((upsTraffic v).recvs B_MIDROOT).map Msg.toFp))
    (hlen : hds.length < P)
    (hsha : Link3.ShaHyp vs hds es others shaS shaR)
    (hvpost : Link3.VPostOk others pv)
    (hvpostLen : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    (hsched : SchedVal v sv) :
    ∀ s ∈ v, ∀ L ps fls wsl ci ti di si kd sdx, UpsLayout s L ps fls wsl → UpsPlan s ps ci ti di si kd sdx →
      ∀ run, traceUpsert (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid) UpsSpec.key
          (sv (s.row 0 tau)) = some run →
        A7Match.PartMatch (Rpost vs es) (Vpost vs es pv) s ps ci ti si kd sdx (sv (s.row 0 tau)) run := by
  have hC := ups_chain hhw hw hK hr0 hrK hROOT hMID hlen
  have E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws :=
    { node := hN, head := hhw, val := hvw, par := hb, vpar := hvb, sha := hsha, vpost := hvpost,
      vpostLen := hvpostLen, ups := hw, upb := hupb, sched := hsched, bytesU := hbytesU, othU := hothU,
      digU := hdigU, memd := hmemd, tauD := ups_tauDistinct hC,
      tauB := fun s hs => by have := ups_tauBound hC s hs; omega,
      walk := ups_walkHyp_22 hN hhw hvw hW hWr hw hb hvb hE hB hKn (Link3.rec_bytes hN hhw hvw hb hsha) _ }
  intro s hs L ps fls wsl ci ti di si kd sdx hL hP run hr
  exact ups_trace E hs hL hP hC run hr

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace A7Match

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows LinkSched

/-- **(E1) closed**: `UpsPartMatch tr r` from `HoldsP` (`ups_traceB_22` with the hypotheses of
`LinkSched.upsLink_holds`). -/
theorem upsPartMatch_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    UpsPartMatch tr r := by
  obtain ⟨sv, hsvd, hsv⟩ := schedVal_holds hp hsz hH T
  have L := trieLink_of hp hsz hH T W
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  subst hsvd
  intro s hs Lr ps fls ws ci ti di si kd sdx hL hP run hr
  refine ups_traceB_22 W.nodes W.heads W.values W.ups W.walks W.walkSteps L.parent L.vparent L.upb
    L.edge L.bmap (LinkKeynib.keynibOk_of hp hsz hH T W) (LinkUps.hbytesU_of hp hsz hH T W)
    (LinkUps.hothU_of hp hsz hH T W) ?_ (memdBal_of hH T) (by unfold P; omega) (by omega) ?_ ?_
    (rootBal_of hp hsz hH T) (midBal_of hH T) ?_ L.sha (LinkVPost.vpostOk_holds hp hsz hH T W)
    (LinkVPost.hvpostLen_of hH T W) hsv s hs Lr ps fls ws ci ti di si kd sdx hL hP run hr
  · intro m hm
    apply digest_provided hH (t := T_UPS) (by decide)
    rw [ups_count T _ _ _ (by decide +kernel)]
    simp only [tcnt, Bool.false_eq_true, ite_false]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · have := heads_le L.parent; have := W.nodes.count; unfold P; omega

end A7Match

end ZkFormal.NearV3.Assembly
