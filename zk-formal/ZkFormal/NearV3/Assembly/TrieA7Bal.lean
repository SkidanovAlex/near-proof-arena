import ZkFormal.NearV3.Assembly.TrieA7Val
import ZkFormal.NearV3.Assembly.TrieA7Ups
import ZkFormal.NearV3.Assembly.TrieBusBalance

/-!
# ZkFormal.NearV3.Assembly.TrieA7Bal — `RPL`/`RPLV` balance of a bundle from record-level data

`RPL` (70) is used by `nodeA7` (receives) and `upsA7` (sends) only, `RPLV` (71) by `valA7` and
`upsA7`; no public segment touches them (kernel checks).  For a bundle whose node, value and ups
components are the honest A7 traces (`nodeA7Trace ns T_NODE (selN ns S)`,
`valA7Trace es T_VAL (selV es SV)`, `upsA7Trace Js T_UPS`):

* `balancedAt_rpl`: `RPL` balances iff (it suffices that) the ups `RPL` messages
  `Js.flatMap upsRplMsgs` are a permutation of the selected node record ids
  `((range |ns|).filter S).map ([·])`;
* `balancedAt_rplv`: the same for `Js.flatMap upsRplvMsgs` and the selected value records.

The remaining semantic obligation (open): for the honest native choice, the ups instances'
terminal records `N_D`, upper-part sources `sN` and old-value ids `vid` are distinct node/value
record ids of `TrieNative.nodes`/`vals`, so that `S`/`SV` := "is one of them" makes the
permutations hold.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render ZkFormal.NearV3.UnfoldA7
  ZkFormal.NearV3.Assembly.TrieA7

theorem covers_rpl_send : Covers B_RPL true (fun t => t == 7) = true := by decide +kernel
theorem covers_rpl_recv : Covers B_RPL false (fun t => t == 2) = true := by decide +kernel
theorem covers_rplv_send : Covers B_RPLV true (fun t => t == 7) = true := by decide +kernel
theorem covers_rplv_recv : Covers B_RPLV false (fun t => t == 4) = true := by decide +kernel

theorem pub_rpl (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_RPL s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m
theorem pub_rplv (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_RPLV s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- The count of an A7 component on an appended-only bus is the count of the appended
interactions' trace traffic. -/
theorem cnt_ext (t : Nat) (ht : t < nearAirV3.tables.length) (base js : List Interaction)
    (hT : nearAirV3.tables[t].interactions = base ++ js) (tr : Trace Fp) (htr : (R ⟨t, ht⟩).tr = tr)
    (b : Nat) (hoff : (base.all fun i => i.bus != b) = true) (s : Bool) (m : List Fp) :
    cnt (sel s (R.tf t) b) m = cnt (sel s (traceTraffic js tr t pub) b) m := by
  rw [R.cnt_tf t ht, hT, tableBusCount_app, htr,
    tableBusCount_off_side base tr t pub b s m (fun i hi hb => by
      have := List.all_eq_true.mp hoff i hi; simp [hb] at this),
    Nat.zero_add]
  exact (count_sel (traceTraffic_exact js tr t pub) b s m)

/-- **`RPL` balance of a bundle** from the record-level permutation. -/
theorem balancedAt_rpl (ns : List NodeS3) (hn : NodeOk ns) (S : Nat → Bool) (Js : List UpsInst)
    (hu : UpsRenderOk Js)
    (htn : (R ⟨T_NODE, by decide⟩).tr = nodeA7Trace ns T_NODE (selN ns S))
    (htu : (R ⟨T_UPS, by decide⟩).tr = upsA7Trace Js T_UPS)
    (hperm : (Js.flatMap upsRplMsgs).Perm (((List.range ns.length).filter S).map fun n => [n])) :
    R.BalancedAt B_RPL := by
  intro m
  rw [R.sum_tables true _ m _ covers_rpl_send, R.sum_tables false _ m _ covers_rpl_recv, pub_rpl, pub_rpl]
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 2) = [2] := by decide
  rw [hf7, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_ext 7 (by decide) ZkFormal.NearV3.UpsV3.table.interactions UnfoldA7.Ups.interactions rfl _ htu B_RPL
      (by decide +kernel),
    R.cnt_ext 2 (by decide) ZkFormal.NearV3.NodeV3.tableU.interactions UnfoldA7.Node.interactions rfl _ htn B_RPL
      (by decide +kernel)]
  simp only [sel, ite_true, Bool.false_eq_true, ite_false]
  show cnt ((traceTraffic UnfoldA7.Ups.interactions (upsA7Trace Js T_UPS) T_UPS pub).sends B_RPL) m =
    cnt ((traceTraffic UnfoldA7.Node.interactions (nodeA7Trace ns T_NODE (selN ns S)) T_NODE pub).recvs B_RPL) m
  rw [ups_rpl_sends Js hu pub, node_rpl_recvs ns hn S pub]
  exact (hperm.map Msg.toFp).count_eq m

/-- **`RPLV` balance of a bundle** from the record-level permutation. -/
theorem balancedAt_rplv (es : List ValE) (hv : ValOk es) (SV : Nat → Bool) (Js : List UpsInst)
    (hu : UpsRenderOk Js)
    (htv : (R ⟨T_VAL, by decide⟩).tr = valA7Trace es T_VAL (selV es SV))
    (htu : (R ⟨T_UPS, by decide⟩).tr = upsA7Trace Js T_UPS)
    (hperm : (Js.flatMap upsRplvMsgs).Perm (((List.range es.length).filter SV).map fun n => [n])) :
    R.BalancedAt B_RPLV := by
  intro m
  rw [R.sum_tables true _ m _ covers_rplv_send, R.sum_tables false _ m _ covers_rplv_recv, pub_rplv, pub_rplv]
  have hf7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
  have hf4 : (List.range 25).filter (fun t => t == 4) = [4] := by decide
  rw [hf7, hf4]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_ext 7 (by decide) ZkFormal.NearV3.UpsV3.table.interactions UnfoldA7.Ups.interactions rfl _ htu B_RPLV
      (by decide +kernel),
    R.cnt_ext 4 (by decide) ZkFormal.NearV3.ValV3.table.interactions UnfoldA7.Val.interactions rfl _ htv B_RPLV
      (by decide +kernel)]
  simp only [sel, ite_true, Bool.false_eq_true, ite_false]
  show cnt ((traceTraffic UnfoldA7.Ups.interactions (upsA7Trace Js T_UPS) T_UPS pub).sends B_RPLV) m =
    cnt ((traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es SV)) T_VAL pub).recvs B_RPLV) m
  rw [ups_rplv_sends Js hu pub, val_rpl_recvs es hv SV pub]
  exact (hperm.map Msg.toFp).count_eq m

end RenderBundleV3

end ZkFormal.NearV3.Assembly
