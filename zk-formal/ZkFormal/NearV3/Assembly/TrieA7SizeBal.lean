import ZkFormal.NearV3.Assembly.TrieA7Size
import ZkFormal.NearV3.Render.HonestBalanceRcpt

/-!
# ZkFormal.NearV3.Assembly.TrieA7SizeBal — the bundle `SIZE` balance (tags 0–5)

`SIZE` (18) is sent by `nodeA7` (2), `valA7` (4), `upsA7` (7) and `srcp` (20) and received by
`sizeA7` (21) only; no public segment touches it (kernel checks).

**`balancedAt_size`**: a bundle whose node / value / size components carry the honest A7 traffic
(`Traffic.append` of the base traffic and the appended interactions' trace traffic — what
`nodeRenderV3`, `valRenderV3`, `sizeRenderV3` produce), whose ups trace is `upsA7Trace Js`, whose
srcp component sends the honest `srcpTraffic bs` on `SIZE`, and whose size table is built from
`honestSizeV ns es bs` with the A7 row values `yN 0/1/2 = nodeA7Total ns S, valA7Total es SV,
upsA7Total Js`, balances on `SIZE`: tags 0–2 by `honest_size_balance`, tags 3–5 by
`node_size_sends` / `val_size_sends` / `ups_size_sends` against `size_a7_recvs`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render ZkFormal.NearV3.UnfoldA7
  ZkFormal.NearV3.Assembly.TrieA7

theorem covers_size_send : Covers B_SIZE true (fun t => t == 2 || t == 4 || t == 7 || t == 20) = true := by
  decide +kernel
theorem covers_size_recv : Covers B_SIZE false (fun t => t == 21) = true := by decide +kernel

theorem pub_size (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_SIZE s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem cnt_app (a b : List Msg) (m : List Fp) : cnt (a ++ b) m = cnt a m + cnt b m := by
  simp [cnt, List.count_append]

theorem toFp_mod (a x : Nat) : Msg.toFp [a, x % P] = Msg.toFp [a, x] := by
  simp only [Msg.toFp, List.map_cons, List.map_nil, Fp.ofNat, Nat.mod_mod]

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem tf_eq (t : Nat) (ht : t < nearAirV3.tables.length) : R.tf t = (R ⟨t, ht⟩).tf := by
  simp only [tf, ht, ↓reduceDIte]

/-- **`SIZE` balance of a bundle** (all six tags). -/
theorem balancedAt_size (ns : List NodeS3) (hn : NodeOk ns) (S : Nat → Bool) (es : List ValE) (hv : ValOk es)
    (SV : Nat → Bool) (Js : List UpsInst) (hu : UpsRenderOk Js) (bs : List SrcpB) (yN : Nat → Nat)
    (hfn : (R ⟨T_NODE, by decide⟩).tf = Traffic.append (nodeTraffic3 ns)
      (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace ns T_NODE (selN ns S)) T_NODE pub))
    (hfv : (R ⟨T_VAL, by decide⟩).tf = Traffic.append (valTraffic es)
      (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es SV)) T_VAL pub))
    (htu : (R ⟨T_UPS, by decide⟩).tr = upsA7Trace Js T_UPS)
    (hfs : (R ⟨T_SIZE, by decide⟩).tf = Traffic.append (sizeTraffic (honestSizeV ns es bs))
      (traceTraffic UnfoldA7.Size.interactions (sizeA7Trace pub (honestSizeV ns es bs) T_SIZE yN) T_SIZE pub))
    (hfp : (R.tf T_SRCP).sends B_SIZE = (srcpTraffic bs).sends B_SIZE)
    (hy0 : yN 0 = nodeA7Total ns S) (hy1 : yN 1 = valA7Total es SV) (hy2 : yN 2 = upsA7Total Js) :
    R.BalancedAt B_SIZE := by
  intro m
  rw [R.sum_tables true _ m _ covers_size_send, R.sum_tables false _ m _ covers_size_recv, pub_size, pub_size]
  have hf1 : (List.range 25).filter (fun t => t == 2 || t == 4 || t == 7 || t == 20) = [2, 4, 7, 20] := by
    decide
  have hf2 : (List.range 25).filter (fun t => t == 21) = [21] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_ext 7 (by decide) ZkFormal.NearV3.UpsV3.table.interactions UnfoldA7.Ups.interactions rfl _ htu B_SIZE
      (by decide +kernel)]
  have e2 : R.tf 2 = _ := (R.tf_eq 2 (by decide)).trans hfn
  have e4 : R.tf 4 = _ := (R.tf_eq 4 (by decide)).trans hfv
  have e21 : R.tf 21 = _ := (R.tf_eq 21 (by decide)).trans hfs
  have e20 : (R.tf 20).sends B_SIZE = _ := hfp
  rw [e2, e4, e21]
  simp only [sel, ite_true, Bool.false_eq_true, ite_false, Traffic.append]
  rw [show (7 : Nat) = T_UPS from rfl]
  rw [e20, ups_size_sends Js hu pub, node_size_sends ns hn S pub, val_size_sends es hv SV pub, size_a7_recvs,
    cnt_app, cnt_app, cnt_app]
  have hb := congrArg (fun l => cnt l m) (honest_size_balance ns es bs)
  simp only [cnt_app] at hb
  have h3 : cnt [[3, yN 0 % P], [4, yN 1 % P], [5, yN 2 % P]] m =
      cnt [[3, nodeA7Total ns S]] m + cnt [[4, valA7Total es SV]] m + cnt [[5, upsA7Total Js]] m := by
    simp only [cnt, List.map_cons, List.map_nil, toFp_mod, hy0, hy1, hy2]
    simp only [List.count_cons, List.count_nil]
    omega
  rw [h3]
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
