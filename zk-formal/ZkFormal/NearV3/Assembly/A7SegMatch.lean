import ZkFormal.NearV3.Assembly.A7Rows

/-!
# ZkFormal.NearV3.Assembly.A7SegMatch — `UpsSegMatch` from (E1) + (E2), and `unfoldedBytes` (A7) closed

For every `upsV3` segment `s` (layout, plan) and the spec's run on `Tpost r τ`:

* outputs: `outputByteCharge run = Σ_k |nodeEnc (upsQ k)| = Σ_k ℓ_k` (`PartMatch`, `ups_partsAllV`) and
  `|sv τ| = L` (`ups_vlen`), so `outputByteCharge + |sv| = a7S s` (`a7S_eq`);
* `RPL`: `[nD] = [N_D]` (`nD_eq`) is the source of the terminal replacing part (`termRepl`: every terminal plan has
  one), `[sN_k]` of the upper parts are their sources; `|ser n| = |nodeEnc (srcOf k)|` (`UpsExt0.srcEnc`,
  `ser_length_post3`); all are `replK` parts of the run, at distinct indices (`sum_le_plus`);
* `RPLV`: `pres = 1` ⇒ the key's value is found in `Tpost` (`ups_s0f`) and in `Fpre` (`ups_s0f_any`, the same walk with
  the pre values), `len_vid = |pre value|` (`wV_le`), `|post value| ≤ oldValCharge` (`trace_find_old`) and
  `U Tpost + |pre| ≤ U Fpre + |post|` (`le_find_gap`, `tpost_le`).

**`A7Match.upsSegMatch_holds`**: `A7Pre.UpsSegMatch tr r` from `HoldsP`; **`unfoldedBytes_holds`**:
`unfoldBytes cb (witnessOfV3 k (xOf r d)) ≤ B0` (with `shape`, `applied`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Every terminal plan has a part that replaces its source. -/
def termReplCheck : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti =>
    (List.range (nTof ci ti)).any fun j =>
      Assembly.TrieA7Repl.replK ((termPlan (UCase.all.getD ci .LP) ti).getD j .RDB)

theorem termReplCheck_ok : termReplCheck = true := by decide

theorem termRepl {ci ti : Nat} (h1 : ci < 11) (h2 : ti < 3) :
    ∃ j, j < nTof ci ti ∧ Assembly.TrieA7Repl.replK ((termPlan (UCase.all.getD ci .LP) ti).getD j .RDB) = true := by
  have c := termReplCheck_ok
  simp only [termReplCheck, List.all_eq_true, List.any_eq_true, List.mem_range] at c
  exact c ci h1 ti h2

/-- **The `upsV3` environment from the views, balances, `ShaHyp` and the interfaces** (as `upsV3_linkB_22`). -/
theorem upsEnv_B22 {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
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
    UpsEnv vs hds es others shaS shaR pv v sv othersU ws ∧ RootChain hds (v.map upsE) K r0 rK := by
  have hC := ups_chain hhw hw hK hr0 hrK hROOT hMID hlen
  refine ⟨?_, hC⟩
  exact
    { node := hN, head := hhw, val := hvw, par := hb, vpar := hvb, sha := hsha, vpost := hvpost,
      vpostLen := hvpostLen, ups := hw, upb := hupb, sched := hsched, bytesU := hbytesU, othU := hothU,
      digU := hdigU, memd := hmemd, tauD := ups_tauDistinct hC,
      tauB := fun s hs => by have := ups_tauBound hC s hs; omega,
      walk := ups_walkHyp_22 hN hhw hvw hW hWr hw hb hvb hE hB hKn (Link3.rec_bytes hN hhw hvw hb hsha) _ }

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK)
include E hC

/-- **`S0F` with any value list** (`ups_s0f` with the walk's values taken from `V'`). -/
theorem ups_s0f_any (V' : List ValRec3) {s : UpsSeg} (hs : s ∈ v) :
    (s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) V' (headAt hds (s.row 0 tau)).rid).find UpsSpec.key =
        some (some (valOf V' (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
    (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
      (fullTree (Rpost vs es) V' (headAt hds (s.row 0 tau)).rid).find UpsSpec.key = some none) := by
  have hw := E.ups
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
  obtain ⟨ci, ti, di, si, kd, sdx, hP⟩ := ups_plan hw hs hL
  have G' := Link3.walkHyp_any E.node E.head E.val E.walk.walk E.par E.vpar E.walk.balE E.walk.balB
    (Link3.rec_bytes E.node E.head E.val E.par E.sha) E.walk.sym V'
  obtain ⟨h, hh, ht, hV, hA⟩ := Walk3.walk3_find_of G' (upsWalk_mem (ws := ws) hs)
  have hhd : h = headAt hds (s.row 0 tau) := by
    have := (hC.head_all h hh).2; rw [ht] at this; exact this
  subst hhd
  rw [upsWalk_key3] at hV hA
  have hlast : (upsWalk s).last = stepOf (s.row 3) 3 := by
    unfold WalkR.last; rw [upsWalk_len]; exact upsWalk_step s (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpr, hvd⟩ := ups_walkTerm hw hs hL hP
  have h4 := hL.walk.1
  have sp : s.row 3 pres = s.row 0 pres := hL.segc 3 (by omega) pres (by decide)
  have sv' : s.row 3 vid = s.row 0 vid := hL.segc 3 (by omega) vid (by decide)
  have hm := (wRowF hw hs hL 3 (by omega)).modes.1
  unfold WalkR.fk WalkR.k at hV
  unfold WalkR.fk at hA
  rw [hlast] at hV hA
  rcases (show s.row 3 mS = 0 ∨ s.row 3 mS = 1 by omega) with h0 | h1
  · have hmd : (stepOf (s.row 3) 3).mode ≠ 0 := by
      intro hc
      simp only [stepOf, h0] at hc
      by_cases a : s.row 3 mK = 1 <;> by_cases b : s.row 3 mB = 1 <;> simp [a, b] at hc
    rw [if_neg hmd] at hA
    refine Or.inr ⟨by rw [← sp, hpr, h0], by rw [← sv', hvd, h0, Nat.zero_mul], hA rfl⟩
  · have hmd : (stepOf (s.row 3) 3).mode = 0 := by simp [stepOf, h1]
    rw [if_pos hmd, if_pos hmd] at hV
    have := hV rfl
    simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero] at this
    refine Or.inl ⟨by rw [← sp, hpr, h1], ?_⟩
    rw [← sv', hvd, h1, Nat.one_mul]; exact this

end

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace A7Match

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows ZkFormal.NearV3.UpsV3 LinkSched Render.UpsGen

/-! ## Sums -/

theorem sum_parts (parts : List TreePart) (n : Nat) (hl : parts.length = n) (f : TreePart → Nat) (g : Nat → Nat)
    (h : ∀ k, k < n → ∀ q, parts[k]? = some q → f q = g k) :
    (parts.map f).sum = ((List.range n).map g).sum := by
  rw [map_range_getD f ⟨.RDB, .hash [], .hash [], 0⟩ parts, hl]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  apply h k hk'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

theorem sum_le_range (f g : Nat → Nat) : ∀ n, (∀ k, k < n → f k ≤ g k) →
    ((List.range n).map f).sum ≤ ((List.range n).map g).sum
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have := sum_le_range f g n (fun k hk => h k (by omega))
    have := h n (by omega)
    simp; omega

theorem sum_ite_eq (b j : Nat) : ∀ n, j < n → ((List.range n).map fun k => if k = j then b else 0).sum = b
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hj : j = n
    · subst hj
      rw [sum_zeros j _ (fun d hd => by rw [if_neg (by omega)])]
      simp
    · rw [sum_ite_eq b j n (by omega)]
      simp [show n ≠ j from fun e => hj e.symm]

/-- One extra charge at a distinct index. -/
theorem sum_le_plus (f g : Nat → Nat) (n j b : Nat) (hj : j < n)
    (h : ∀ k, k < n → f k + (if k = j then b else 0) ≤ g k) :
    ((List.range n).map f).sum + b ≤ ((List.range n).map g).sum := by
  have e := sum_ite_eq b j n hj
  have h2 := sum_le_range (fun k => f k + (if k = j then b else 0)) g n h
  have e3 : ((List.range n).map fun k => f k + (if k = j then b else 0)).sum =
      ((List.range n).map f).sum + ((List.range n).map fun k => if k = j then b else 0).sum := by
    generalize List.range n = l
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  omega

/-! ## The environment of the records -/

/-- **The `upsV3` environment of the records** from `HoldsP` (the hypotheses of `LinkSched.upsLink_holds`). -/
theorem upsEnv_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∃ (others : List Msg) (shaS shaR : Nat → List Fp → Nat) (othersU : List Msg) (ws : List WalkR)
      (K : Nat) (r0 rK : List Nat),
      UpsEnv r.nodes r.heads r.values others shaS shaR (fun i => toB (LinkVPost.pnOf r.accts i)) r.ups
        (fun τ => toB (Sched.svOf tr T_CODEC τ)) othersU ws ∧ RootChain r.heads (r.ups.map upsE) K r0 rK := by
  obtain ⟨sv, hsvd, hsv⟩ := schedVal_holds hp hsz hH T
  have L := trieLink_of hp hsz hH T W
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  subst hsvd
  refine ⟨_, _, _, _, _, _, _, _, upsEnv_B22 W.nodes W.heads W.values W.ups W.walks W.walkSteps L.parent
    L.vparent L.upb L.edge L.bmap (LinkKeynib.keynibOk_of hp hsz hH T W) (LinkUps.hbytesU_of hp hsz hH T W)
    (LinkUps.hothU_of hp hsz hH T W) ?_ (memdBal_of hH T) (by unfold P; omega) (by omega) ?_ ?_
    (rootBal_of hp hsz hH T) (midBal_of hH T) ?_ L.sha (LinkVPost.vpostOk_holds hp hsz hH T W)
    (LinkVPost.hvpostLen_of hH T W) hsv⟩
  · intro m hm
    apply digest_provided hH (t := T_UPS) (by decide)
    rw [ups_count T _ _ _ (by decide +kernel)]
    simp only [tcnt, Bool.false_eq_true, ite_false]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · have := heads_le L.parent; have := W.nodes.count; unfold P; omega

/-- The `RPLV` weight of `[vid]` is the length of the pre value at `vpos vid`. -/
theorem wV_le {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r) (vid : Nat) (hv : vid < P) :
    A7Assemble.wV r (Msg.toFp [vid]) ≤
      (valOf (valsOf3 r.nodes r.values) (vpos (vid0 r.values) vid)).length := by
  have h0 : vid0 r.values = 0 := by
    unfold vid0
    cases hr : r.values with
    | nil => rfl
    | cons e rest =>
      have := vid_small W.values (t := 0) (by rw [hr]; simp)
      simp only [hr, List.getElem_cons_zero] at this
      simp [this]
  have hp : vpos 0 vid = vid := by unfold vpos; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
  rw [h0, hp]
  have hw : A7Assemble.wV r (Msg.toFp [vid]) = (r.values.getD vid default).len := by
    simp [A7Assemble.wV, Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hv]
  rw [hw]
  by_cases ht' : vid < r.values.length
  · apply Nat.le_of_eq
    simp only [valOf, valsOf3, List.getElem?_map, List.getElem?_eq_getElem ht', Option.map_some,
      Option.getD_some, toB, List.length_map, List.getD_eq_getElem?_getD]
    have hsh := W.values.shape _ (List.getElem_mem ht')
    cases hz : r.values[vid].vz
    · exact (hsh.2 hz).1.symm
    · rw [(hsh.1 hz).1, (hsh.1 hz).2]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-! ## `UpsSegMatch` -/

/-- **`UpsSegMatch` from `HoldsP`**: (E1) `ups_trace` and (E2) `a7S_eq`, `a7Rpl_sum`, `a7Rplv_sum`, `nD_eq`. -/
theorem upsSegMatch_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    A7Pre.UpsSegMatch tr r := by
  obtain ⟨others, shaS, shaR, othersU, ws, K, r0, rK, E, hC⟩ := upsEnv_holds hp hsz hH T W
  intro s hs run hr
  obtain ⟨Lr, ps, fls, wsl, hL⟩ := ups_layout E.ups s hs
  obtain ⟨ci, ti, di, si, kd, sdx, hP⟩ := ups_plan E.ups hs hL
  obtain ⟨hplen, hpm⟩ := ups_trace E hs hL hP hC run hr
  have hvb := ups_vbytesE E hs hL hP
  have hvl := (ups_vlen E.ups E.sched hs hL hvb).2
  have hpb := ups_partsAllV E hs hL hP
  have X0 := ups_ext0V E hs hL hP
  have hRow := fun i x => rowLt E.ups hs i x
  refine ⟨?_, ?_, ?_⟩
  · -- outputs and the new value: `a7S`
    have hq : ∀ k (hk : k < ps.length), (ZkFormal.NearV3.nodeEnc (upsQ ci si ti (s.row 0 tX)
        (toB (Sched.svOf tr T_CODEC (s.row 0 tau))) kd sdx
        (srcOf (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) s ps) k)).length =
        ps[k].2 := by
      intro k hk
      have := congrArg List.length (hpb k hk).1
      simp only [rowsB, List.length_map, List.length_range] at this
      exact this.symm
    have ho : outputByteCharge run = ((List.range ps.length).map fun k => (ps.getD k (0, 0)).2).sum := by
      unfold outputByteCharge
      refine sum_parts run.parts ps.length hplen _ _ (fun k hk q hq' => ?_)
      obtain ⟨q', hq'', -, hout, -⟩ := hpm k hk
      rw [hq'] at hq''; cases hq''
      rw [hout, hq k hk, getD_ps hk]
    have hsum : (ps.map (·.2)).sum = ((List.range ps.length).map fun k => (ps.getD k (0, 0)).2).sum := by
      rw [map_range_getD _ (0, 0) ps]
    rw [a7S_eq E.ups hs hL hP]
    have : (toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)).length = Lr := hvl
    omega
  · -- `RPL`
    rw [a7Rpl_sum E.ups hs hL hP (A7Assemble.wN r), nD_eq E.ups hs hL hP W.a7ups]
    have hwN : ∀ n, n < P → A7Assemble.wN r (Msg.toFp [n]) = ((r.nodes.getD n default).v.ser false).length := by
      intro n hn; simp [A7Assemble.wN, Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have hsl : ∀ k (hk : k < ps.length), (NearSpecV3.nodeEnc (srcOf (Rpost r.nodes r.values)
        (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) s ps k)).length =
        ((r.nodes.getD (s.row ps[k].1 sN) default).v.ser false).length := by
      intro k hk
      have h1 := X0.srcEnc k hk
      have hn := part_sN E.node E.ups E.upb hs hL hP k hk
      have := congrArg List.length h1
      rw [List.length_map, postB_eq hn, ser_length_post3 (E.node.wf _ (List.getElem_mem hn))] at this
      rw [← TrieA7Post.enc_eq, ← this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    have hrep : TrieA7Repl.replacedCharge run = ((List.range ps.length).map fun k =>
        if TrieA7Repl.replK (UKind.all.getD (kd k) .RDB) then (NearSpecV3.nodeEnc (srcOf (Rpost r.nodes r.values)
          (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) s ps k)).length else 0).sum := by
      unfold TrieA7Repl.replacedCharge
      refine sum_parts run.parts ps.length hplen _ _ (fun k hk q hq' => ?_)
      obtain ⟨q', hq'', hkind, -, hsrc⟩ := hpm k hk
      rw [hq'] at hq''; cases hq''
      rw [← hkind]
      by_cases h2 : TrieA7Repl.replK q.kind = true
      · simp [h2, hsrc h2]
      · simp [h2]
    rw [hrep]
    have hlenP := hP.len
    obtain ⟨j, hj, hjr⟩ := termRepl hP.ix.1 hP.ix.2.1
    have hjps : j < ps.length := by omega
    obtain ⟨hjk, hj1, hj2, -, -, hjsd, -⟩ := hP.term j hjps hj
    have hjs := (hP.src j hjps (by omega)).1
    rw [hjsd] at hjs
    have := sum_le_plus (fun k => if nTof ci ti ≤ k then A7Assemble.wN r (Msg.toFp [s.row (ps.getD k (0, 0)).1 sN]) else 0)
      (fun k => if TrieA7Repl.replK (UKind.all.getD (kd k) .RDB) then (NearSpecV3.nodeEnc (srcOf (Rpost r.nodes r.values)
          (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) s ps k)).length else 0)
      ps.length j (A7Assemble.wN r (Msg.toFp [s.row 0 (11 + di)])) hjps (fun k hk => by
        simp only [getD_ps hk]
        by_cases hT : nTof ci ti ≤ k
        · have hkj : k ≠ j := by omega
          have hrk : TrieA7Repl.replK (UKind.all.getD (kd k) .RDB) = true := by
            rcases (hP.upper k hk hT).1 with h01 | h11
            · rcases (show kd k = 0 ∨ kd k = 1 by omega) with e | e <;> rw [e] <;> rfl
            · rw [h11]; rfl
          rw [if_pos hT, if_neg hkj, if_pos hrk, hsl k hk, hwN _ (hRow _ _)]; omega
        · rw [if_neg hT]
          by_cases hkj : k = j
          · subst hkj
            rw [if_pos rfl, hjk, if_pos hjr, hsl k hk, hjs, hwN _ (hRow _ _)]; omega
          · rw [if_neg hkj]; omega)
    omega
  · -- `RPLV`
    rw [a7Rplv_sum E.ups hs hL hP (A7Assemble.wV r)]
    have hle := A7Post.le_U (A7Post.tpost_le hH T W (UpsRows.upsE s).tau)
    split
    · rename_i hpres
      rcases ups_s0f E hC hs with ⟨-, hb⟩ | ⟨h0, -⟩
      · rcases ups_s0f_any E hC (valsOf3 r.nodes r.values) hs with ⟨-, ha⟩ | ⟨h0', -⟩
        · have g1 := A7TraceRun.trace_find_old _ _ _ run _ hr hb
          have g2 := A7TraceRun.le_find_gap _ _ _ (A7Post.tpost_le hH T W (UpsRows.upsE s).tau) ha hb
          have g3 := wV_le W (s.row 0 vid) (hRow 0 vid)
          omega
        · omega
      · omega
    · omega

open NearSpecV3 in
/-- **`RestFieldsV3.unfoldedBytes` (A7) closed** (with the `shape` and `source.applied` fields). -/
theorem unfoldedBytes_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    unfoldBytes cb (witnessOfV3 k (xOf r d)) ≤ UnfoldA7.B0 :=
  A7Pre.unfoldedBytes_of_match hp hw hsz hH W T d hs happ (upsSegMatch_holds hp hsz hH T W)

end A7Match

end ZkFormal.NearV3.Assembly
