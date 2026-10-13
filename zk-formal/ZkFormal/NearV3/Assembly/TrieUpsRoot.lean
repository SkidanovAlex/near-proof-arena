import ZkFormal.NearV3.Assembly.TrieUpsNative
import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootRecords
import ZkFormal.NearV3.Rcpt.Candidates.PublicRootTraffic
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootHeader
import ZkFormal.NearV3.Rcpt.Candidates.CompactRootCells
import ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootCells

/-!
# ZkFormal.NearV3.Assembly.TrieUpsRoot — `MIDROOT` (and the ups side of `ROOT`)

`upsV3` receives `MIDROOT [τ, rid] ++ mid` on the `W0` row of every instance and sends
`ROOT [τ + 1] ++ post` on its `W3` row; all other rows are silent on these buses.  The
compact-table lemmas (`compact_midroot_row`, `compact_root_row`) are ported to `upsV3`: the two
tables have the same interactions on these buses and the same cells on `W`/`V` rows, and `Q`
rows are silent (`sf = wt3 = 0`).

* `aligned_view_midroot`, `aligned_view_root` — the aligned ups view's `MIDROOT` receives /
  `ROOT` sends are `insts.map ([τ, rid] ++ mid)` / `insts.map ([τ + 1] ++ post)` (no other
  `MIDROOT`/`ROOT` traffic);
* `balancedAt_midroot` — bundle level, from the record identity `headSends hs MIDROOT =
  insts.map ([τ, rid] ++ mid)`;
* `midroot_accepted` — that identity for the honest heads and native ranked instances.
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsRoot

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Render.UpsRelay UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.Size

set_option maxHeartbeats 800000

theorem uMsgs_midroot (C D : URow) (sd : Bool) : uMsgs C D B_MIDROOT sd = compactMsgs C D B_MIDROOT sd := by
  simp [compactMsgs, compactInteractions, uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_EDGE, B_BMAP, B_UPB, B_MEMD]

theorem uMsgs_root (C D : URow) (sd : Bool) : uMsgs C D B_ROOT sd = compactMsgs C D B_ROOT sd := by
  simp [compactMsgs, compactInteractions, uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_EDGE, B_BMAP, B_UPB, B_MEMD]

theorem gen_w (Is : List UpsInst) (q i t : Nat) : generatedRow Is q (i, .w t) = compactGeneratedRow Is q (i, .w t) := rfl
theorem gen_v (Is : List UpsInst) (q i p : Nat) : generatedRow Is q (i, .v p) = compactGeneratedRow Is q (i, .v p) := rfl

theorem midroot_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) (hl : (inst Is i).mid.length = 32) :
    uMsgs (generatedRow Is q (i, rk)) D B_MIDROOT false =
      if rk = .w 0 then [reduceMessage ([(inst Is i).tau, (inst Is i).rid] ++ (inst Is i).mid)] else [] := by
  rw [uMsgs_midroot]
  cases rk with
  | w t => rw [gen_w]; exact compact_midroot_row Is q i _ D hl
  | v p => rw [gen_v]; exact compact_midroot_row Is q i _ D hl
  | q k p =>
    have hs : generatedRow Is q (i, .q k p) UpsV3.sf = 0 := rfl
    rw [compact_midroot_silent _ _ hs]; rfl

theorem root_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) (hl : (inst Is i).post.length = 32) :
    uMsgs (generatedRow Is q (i, rk)) D B_ROOT true =
      if rk = .w 3 then [reduceMessage ([(inst Is i).tau + 1] ++ (inst Is i).post)] else [] := by
  rw [uMsgs_root]
  cases rk with
  | w t => rw [gen_w]; exact compact_root_row Is q i _ D hl
  | v p => rw [gen_v]; exact compact_root_row Is q i _ D hl
  | q k p =>
    have hs : generatedRow Is q (i, .q k p) UpsV3.wt3 = 0 := rfl
    rw [compact_root_silent _ _ hs]; rfl

theorem midroot_send_nil (C D : URow) : uMsgs C D B_MIDROOT true = [] := by
  rw [uMsgs_midroot]; exact compact_midroot_send C D
theorem root_recv_nil (C D : URow) : uMsgs C D B_ROOT false = [] := by
  rw [uMsgs_root]; exact compact_root_recv C D

/-- Messages on these buses only read columns `< 200`. -/
theorem midroot_congr (C C' D D' : URow) (h : ∀ x < 200, C x = C' x) :
    uMsgs C D B_MIDROOT false = uMsgs C' D' B_MIDROOT false := by
  rw [uMsgs_midroot, uMsgs_midroot, compact_midroot_recv, compact_midroot_recv]
  have hr : (List.range 32).map (fun i => C (UpsV3.reg i)) = (List.range 32).map (fun i => C' (UpsV3.reg i)) := by
    apply List.map_congr_left
    intro i hi
    exact h _ (by simp [UpsV3.reg] at hi ⊢; omega)
  rw [h UpsV3.sf (by decide), h UpsV3.tau (by decide), h UpsV3.rootRid (by decide), hr]

theorem root_congr (C C' D D' : URow) (h : ∀ x < 200, C x = C' x) :
    uMsgs C D B_ROOT true = uMsgs C' D' B_ROOT true := by
  rw [uMsgs_root, uMsgs_root, compact_root_send, compact_root_send]
  have hr : (List.range 32).map (fun i => C (UpsV3.reg i)) = (List.range 32).map (fun i => C' (UpsV3.reg i)) := by
    apply List.map_congr_left
    intro i hi
    exact h _ (by simp [UpsV3.reg] at hi ⊢; omega)
  rw [h UpsV3.wt3 (by decide), h UpsV3.tau (by decide), hr]

private theorem hz {α : Type} (xs : List α) : xs.flatMap (fun _ => ([] : List ZkFormal.Near.Msg)) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

theorem instance_midroot (Is : List UpsInst) (i : Nat) (pos : RK → Nat) (next : RK → URow)
    (hl : (inst Is i).mid.length = 32) :
    (recsI (inst Is i)).flatMap (fun rk => uMsgs (generatedRow Is (pos rk) (i, rk)) (next rk) B_MIDROOT false) =
      [reduceMessage ([(inst Is i).tau, (inst Is i).rid] ++ (inst Is i).mid)] := by
  simp only [midroot_row Is _ i _ _ hl, recsI, List.flatMap_append, List.flatMap_map, List.flatMap_assoc]
  simp [List.range_succ, hz]

theorem instance_root (Is : List UpsInst) (i : Nat) (pos : RK → Nat) (next : RK → URow)
    (hl : (inst Is i).post.length = 32) :
    (recsI (inst Is i)).flatMap (fun rk => uMsgs (generatedRow Is (pos rk) (i, rk)) (next rk) B_ROOT true) =
      [reduceMessage ([(inst Is i).tau + 1] ++ (inst Is i).post)] := by
  simp only [root_row Is _ i _ _ hl, recsI, List.flatMap_append, List.flatMap_map, List.flatMap_assoc]
  simp [List.range_succ, hz]

private theorem map_range_getD' {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

private theorem flat_congr' {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- The aligned trace's segment rows agree with the generated rows on the columns. -/
theorem aligned_rows (Is : List UpsInst) (hok : UpsRenderOk Is) (t i : Nat) (hi : i < Is.length) (d : Nat)
    (hd : d < (recsI (inst Is i)).length) :
    ∀ x < 200, (segOf (upsTraceAligned Is) t (start Is i, (recsI (inst Is i)).length)).row d x =
      generatedRow Is (start Is i + d) (i, (recsI (inst Is i)).getD d default) x := by
  intro x hx
  have hh := padded_log_fits (R Is + 1) hok.ok.cap
  have hlog : (upsTraceAligned Is).log t = padLog22 (logOf (R Is + 1)) := rfl
  have hH : R Is + 1 ≤ (upsTraceAligned Is).height t := by
    unfold Trace.height; rw [hlog]; exact hh.1
  have hcell : ∀ r x, r < (upsTraceAligned Is).height t → x < 200 →
      (upsTraceAligned Is).cell t r x = ((cell Is r x : Int) : Fp) := by
    intro r x hr hx
    unfold Trace.height at hr; rw [hlog] at hr
    unfold upsTraceAligned
    rw [rowsTrace_mkTab _ _ _ t r x hr hx, Fp.ofNat_toNat]
  rw [segOf_row _ t _ hd]
  have hend : start Is i + (recsI (inst Is i)).length ≤ R Is := by
    rw [← start_succ, ← start_len]
    exact sum_mono (by omega)
  rw [rowC_cell hcell (by omega) hx]
  simp only [cell, show start Is i + d < R Is by omega, ite_true, recs_seg hi hd]
  rfl

/-- **The aligned ups view's `MIDROOT` receives.** -/
theorem aligned_view_midroot (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat)
    (hl : ∀ I ∈ Is, I.mid.length = 32) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_MIDROOT false) =
      (Is.map fun I => [I.tau, I.rid] ++ I.mid).map reduceMessage := by
  simp only [viewOf, segsOf, List.flatMap_map]
  have hinst : ∀ i, i < Is.length → (inst Is i) ∈ Is := by
    intro i hi
    simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  apply Eq.trans (b := (List.range Is.length).flatMap
    (fun i => [reduceMessage ([(inst Is i).tau, (inst Is i).rid] ++ (inst Is i).mid)]))
  · apply flat_congr'
    intro i hi
    have hi' := List.mem_range.mp hi
    unfold UpsSeg.msgs
    rw [segOf_len]
    rw [← instance_midroot Is i (fun rk => 0) (fun _ => fun _ => 0) (hl _ (hinst i hi'))]
    have he := congrArg (List.flatMap (fun r => uMsgs (generatedRow Is 0 (i, r)) (fun _ => 0) B_MIDROOT false))
      (map_range_getD' (recsI (inst Is i)) default)
    rw [List.flatMap_map] at he
    rw [← he]
    apply flat_congr'
    intro d hd
    refine (midroot_congr _ (generatedRow Is (start Is i + d) (i, (recsI (inst Is i)).getD d default)) _ (fun _ => 0)
      (aligned_rows Is hok t i hi' d (List.mem_range.mp hd))).trans ?_
    rw [midroot_row Is _ i _ _ (hl _ (hinst i hi')), midroot_row Is _ i _ _ (hl _ (hinst i hi'))]
  · rw [List.map_map]
    simp only [← List.map_eq_flatMap]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- **The aligned ups view's `ROOT` sends.** -/
theorem aligned_view_root (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat)
    (hl : ∀ I ∈ Is, I.post.length = 32) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_ROOT true) =
      (Is.map fun I => [I.tau + 1] ++ I.post).map reduceMessage := by
  simp only [viewOf, segsOf, List.flatMap_map]
  have hinst : ∀ i, i < Is.length → (inst Is i) ∈ Is := by
    intro i hi
    simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  apply Eq.trans (b := (List.range Is.length).flatMap
    (fun i => [reduceMessage ([(inst Is i).tau + 1] ++ (inst Is i).post)]))
  · apply flat_congr'
    intro i hi
    have hi' := List.mem_range.mp hi
    unfold UpsSeg.msgs
    rw [segOf_len]
    rw [← instance_root Is i (fun rk => 0) (fun _ => fun _ => 0) (hl _ (hinst i hi'))]
    have he := congrArg (List.flatMap (fun r => uMsgs (generatedRow Is 0 (i, r)) (fun _ => 0) B_ROOT true))
      (map_range_getD' (recsI (inst Is i)) default)
    rw [List.flatMap_map] at he
    rw [← he]
    apply flat_congr'
    intro d hd
    refine (root_congr _ (generatedRow Is (start Is i + d) (i, (recsI (inst Is i)).getD d default)) _ (fun _ => 0)
      (aligned_rows Is hok t i hi' d (List.mem_range.mp hd))).trans ?_
    rw [root_row Is _ i _ _ (hl _ (hinst i hi')), root_row Is _ i _ _ (hl _ (hinst i hi'))]
  · rw [List.map_map]
    simp only [← List.map_eq_flatMap]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem view_midroot_send (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_MIDROOT true) = [] := by
  simp [viewOf, UpsSeg.msgs, midroot_send_nil]

theorem view_root_recv (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_ROOT false) = [] := by
  simp [viewOf, UpsSeg.msgs, root_recv_nil]

end ZkFormal.NearV3.Assembly.TrieUpsRoot

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
  Rcpt.Candidates.NodePostUpdate

theorem covers_midroot_send : Covers B_MIDROOT true (fun t => t == 3) = true := by decide +kernel
theorem covers_midroot_recv : Covers B_MIDROOT false (fun t => t == 7) = true := by decide +kernel
theorem covers_root_send : Covers B_ROOT true (fun t => t == 7) = true := by decide +kernel
theorem covers_root_recv : Covers B_ROOT false (fun t => t == 3) = true := by decide +kernel
theorem pub_midroot (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_MIDROOT s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`MIDROOT` balance of a bundle**: heads send the instances' mid roots, which the aligned
ups component receives. -/
theorem balancedAt_midroot (hs : List HeadE) (Js : List UpsInst) (hok : UpsRenderOk Js)
    (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (hl : ∀ I ∈ Js, I.mid.length = 32)
    (hrec : headSends hs B_MIDROOT = Js.map (fun I => [I.tau, I.rid] ++ I.mid)) :
    R.BalancedAt B_MIDROOT := by
  intro m
  rw [R.sum_tables true _ m _ covers_midroot_send, R.sum_tables false _ m _ covers_midroot_recv,
    pub_midroot, pub_midroot]
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  have e7 := R.tf_ext 7 (by decide) hu B_MIDROOT (by decide) (by decide) (by decide)
  have hf3 : (List.range 25).filter (fun t => t == 3) = [3] := by decide
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf3, hf7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e3, e7.1, e7.2, sel, ite_true,
    Bool.false_eq_true, ite_false, headTraffic, upsTraffic, cnt]
  rw [TrieUpsRoot.aligned_view_midroot Js hok T_UPS hl, reduceMessages_toFp, hrec]

/-- **`ROOT` balance of a bundle** from the public endpoint messages, the heads' input roots,
the ups output roots and the root chain. -/
theorem balancedAt_root (hs : List HeadE) (Js : List UpsInst) (hok : UpsRenderOk Js)
    (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (hl : ∀ I ∈ Js, I.post.length = 32) (r0 rK : ZkFormal.Near.Msg) (Lin Lout : List ZkFormal.Near.Msg)
    (hpubT : ∀ m, pubCount nearAirV3 pub B_ROOT true m = cnt [r0] m)
    (hpubF : ∀ m, pubCount nearAirV3 pub B_ROOT false m = cnt [rK] m)
    (hin : headRecvs hs B_ROOT = Lin) (hout : Js.map (fun I => [I.tau + 1] ++ I.post) = Lout)
    (hchain : r0 :: Lout = Lin ++ [rK]) :
    R.BalancedAt B_ROOT := by
  intro m
  rw [R.sum_tables true _ m _ covers_root_send, R.sum_tables false _ m _ covers_root_recv, hpubT, hpubF]
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  have e7 := R.tf_ext 7 (by decide) hu B_ROOT (by decide) (by decide) (by decide)
  have hf3 : (List.range 25).filter (fun t => t == 3) = [3] := by decide
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  rw [hf3, hf7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e3, e7.1, e7.2, sel, ite_true,
    Bool.false_eq_true, ite_false, headTraffic, upsTraffic, cnt]
  rw [TrieUpsRoot.aligned_view_root Js hok T_UPS hl, reduceMessages_toFp, hout, hin]
  have := congrArg (fun xs : List ZkFormal.Near.Msg => (xs.map Msg.toFp).count m) hchain
  simp only [List.map_cons, List.map_append, List.map_nil, List.count_cons, List.count_append,
    List.count_nil] at this ⊢
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.Assembly.TrieUpsRoot

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.NearV3
  ZkFormal.NearV3.Assembly Rcpt.Candidates.NodePostUpdate

/-- **The public `ROOT` endpoints and the root chain of an accepted witness**, for the prepared
statement of ANY hint (the bundle's public vector `pubOf (preparedBytes p 0)`). -/
theorem root_endpoints_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    (hlen : (Public.preparedBytes p 0).length < ZkFormal.Algebra.P) :
    let pub := ZkFormal.Udr.pubOf Fp (Public.preparedBytes p 0)
    let r0 : ZkFormal.Near.Msg := [0] ++ k.slotB2.prevStateRoot.map UInt8.toNat
    let rK : ZkFormal.Near.Msg := [steps.length + 1] ++ k.H.prevStateRoot.map UInt8.toNat
    (∀ msg, pubCount nearAirV3 pub B_ROOT true msg = cnt [r0] msg) ∧
    (∀ msg, pubCount nearAirV3 pub B_ROOT false msg = cnt [rK] msg) ∧
    r0 :: nativeRootRecords 0 (m.result.trie :: steps.map ImplicitStepV3.post) =
      nativeInputRoots 0 (m.pre :: steps.map ImplicitStepV3.pre) ++ [rK] := by
  have hc : checkD0 cb wb = .ok () := by
    unfold checkD0a at h
    obtain ⟨u, hu, _⟩ := ReexecV3D0.bind_ok' h
    cases u; exact hu
  obtain ⟨hpre, hpost, hK⟩ := prepared_trace_root_endpoints hp hk hw hc hv
  have hl4 : (Public.preparedBytes p 0).length < 256 ^ 4 := by
    have : ZkFormal.Algebra.P < 256 ^ 4 := by decide
    omega
  refine ⟨fun msg => ?_, fun msg => ?_, accepted_root_chain hk hw hc hm hv⟩
  · have := (prepared_public_root_counts nearAirV3 hp 0 rfl hl4 msg).1
    rw [this, hpre]; rfl
  · have := (prepared_public_root_counts nearAirV3 hp 0 rfl hl4 msg).2
    rw [this, hpost, hK]; rfl

end ZkFormal.NearV3.Assembly.TrieUpsRoot
