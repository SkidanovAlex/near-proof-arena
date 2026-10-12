import ZkFormal.NearV3.Assembly.TrieUpsSched

/-!
# ZkFormal.NearV3.Assembly.TrieUpsMemd — the ups-internal `MEMD` bus

`upsV3` is the only table on `MEMD`: a non-root, non-`NLF` part's eight `MEM` rows send
`[τ, j, idx, rx, rb, qlen]` (`gMs`), and the receiving part's `MEM` rows receive
`[τ, jm, idx, mBv, mCv, clen]` (`gMr`).

* `uMsgs_memd`, `memd_congr`: the `MEMD` messages of a row read only the twelve `MEMD` columns
  (not the `UPB` counter `u`, not the next row);
* `instRow I rk`: the generated row of `rk` for the instance alone; **`view_memd`**: the aligned
  view's `MEMD` traffic is `Is.flatMap (memdI · sd)`, `memdI I sd` the instance's own rows' messages;
* **`RenderBundleV3.balancedAt_memd`**: the bundle `MEMD` balance from the per-instance pairing
  `MemdPair I` (`memdI I true ~ memdI I false` as field messages).
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsMemd

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Render.UpsRelay UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.Size
  TrieUpsRoot TrieUpsSched

set_option maxHeartbeats 800000

theorem uMsgs_memd (C D : URow) (sd : Bool) :
    uMsgs C D B_MEMD sd =
      if sd then
        (if Fp.ofNat (C UpsV3.gMs) = 1 then
          [reduceMessage [C UpsV3.tau, C UpsV3.j, C UpsV3.idx, C UpsV3.rx, C UpsV3.rb, C UpsV3.qlen]] else [])
      else
        (if Fp.ofNat (C UpsV3.gMr) = 1 then
          [reduceMessage [C UpsV3.tau, C UpsV3.jm, C UpsV3.idx, C UpsV3.mBv, C UpsV3.mCv, C UpsV3.clen]] else []) := by
  cases sd <;>
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD,
    uMult, uev, Expr.evalWith, uEnv, Dsl.c, reduceMessage] <;>
  split <;> simp_all

/-- The twelve columns the `MEMD` messages read. -/
def memdCols : List Nat :=
  [UpsV3.gMs, UpsV3.gMr, UpsV3.tau, UpsV3.j, UpsV3.idx, UpsV3.rx, UpsV3.rb, UpsV3.qlen,
    UpsV3.jm, UpsV3.mBv, UpsV3.mCv, UpsV3.clen]

theorem memd_congr (C C' D D' : URow) (sd : Bool) (h : ∀ x ∈ memdCols, C x = C' x) :
    uMsgs C D B_MEMD sd = uMsgs C' D' B_MEMD sd := by
  rw [uMsgs_memd, uMsgs_memd]
  simp only [memdCols, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- The generated row `rk` of instance `I` alone. -/
def instRow (I : UpsInst) (rk : RK) : URow := generatedRow [I] 0 (0, rk)

theorem qCell_memd (I : UpsInst) (k p u u' : Nat) : ∀ x ∈ memdCols, qCell I k p u x = qCell I k p u' x := by
  intro x hx
  simp only [memdCols, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [qCell, isPC, qRowCell, qRow, UpsV3.gMs, UpsV3.gMr, UpsV3.tau, UpsV3.j, UpsV3.idx, UpsV3.rx,
      UpsV3.rb, UpsV3.qlen, UpsV3.jm, UpsV3.mBv, UpsV3.mCv, UpsV3.clen]

theorem generated_memd (Is : List UpsInst) (q i : Nat) (rk : RK) (hi : i < Is.length) :
    ∀ x ∈ memdCols, generatedRow Is q (i, rk) x = instRow (inst Is i) rk x := by
  intro x hx
  have h0 : inst [inst Is i] 0 = inst Is i := rfl
  simp only [instRow, generatedRow, rowCell, h0]
  cases rk with
  | w t => rfl
  | v p => rfl
  | q k p => simp only []; rw [qCell_memd (inst Is i) k p (UpsGen.uU Is q) (UpsGen.uU [inst Is i] 0) x hx]

/-- The `MEMD` messages of one instance's rows. -/
def memdI (I : UpsInst) (sd : Bool) : List ZkFormal.Near.Msg :=
  (recsI I).flatMap (fun rk => uMsgs (instRow I rk) (fun _ => 0) B_MEMD sd)

private theorem range_flat_map' {β : Type} (Is : List UpsInst) (g : UpsInst → List β) :
    (List.range Is.length).flatMap (fun i => g (inst Is i)) = Is.flatMap g := by
  have : (List.range Is.length).map (fun i => inst Is i) = Is := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rw [show List.flatMap g Is = List.flatMap g ((List.range Is.length).map fun i => inst Is i) by rw [this],
    List.flatMap_map]

/-- **`MEMD` traffic of the aligned ups view**, per instance. -/
theorem view_memd (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) (sd : Bool) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_MEMD sd) =
      Is.flatMap (fun I => memdI I sd) := by
  rw [aligned_view_bus Is hok t B_MEMD sd (fun i rk => uMsgs (instRow (inst Is i) rk) (fun _ => 0) B_MEMD sd)
    (fun q i rk D hi => memd_congr _ _ _ _ sd (generated_memd Is q i rk hi))
    (fun C C' D D' h => memd_congr C C' D D' sd (fun x hx => h x (by
      simp only [memdCols, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)))]
  exact range_flat_map' Is (fun I => memdI I sd)

/-- The per-instance `MEMD` pairing (open: see the lane log). -/
def MemdPair (I : UpsInst) : Prop :=
  ((memdI I true).map Msg.toFp).Perm ((memdI I false).map Msg.toFp)

theorem covers_memd (s : Bool) : Covers B_MEMD s (fun t => t == 7) = true := by
  cases s <;> decide +kernel
theorem pub_memd (s : Bool) (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_MEMD s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem flat_perm (Is : List UpsInst) (h : ∀ I ∈ Is, MemdPair I) :
    ((Is.flatMap (fun I => memdI I true)).map Msg.toFp).Perm ((Is.flatMap (fun I => memdI I false)).map Msg.toFp) := by
  induction Is with
  | nil => simp
  | cons I Is ih =>
    simp only [List.flatMap_cons, List.map_append]
    exact (h I (by simp)).append (ih (fun J hJ => h J (by simp [hJ])))

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`MEMD` balance of a bundle** from the per-instance pairing of its (aligned) ups component. -/
theorem balancedAt_memd (Is : List UpsInst) (hok : UpsRenderOk Is)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))))
    (hpair : ∀ I ∈ Is, MemdPair I) : R.BalancedAt B_MEMD := by
  intro m
  rw [R.sum_tables true _ m _ (covers_memd true), R.sum_tables false _ m _ (covers_memd false),
    pub_memd, pub_memd]
  have e7 := R.tf_ext 7 (by decide) hu B_MEMD (by decide) (by decide) (by decide)
  have hf : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e7.1, e7.2, sel,
    ite_true, Bool.false_eq_true, ite_false, upsTraffic, view_memd Is hok]
  have hp := (flat_perm Is hpair).count_eq m
  simp only [cnt]
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly.TrieUpsMemd
