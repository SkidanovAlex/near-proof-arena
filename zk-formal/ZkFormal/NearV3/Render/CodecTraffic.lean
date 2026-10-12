import ZkFormal.NearV3.Render.CodecRender

/-!
# Codec traffic: reduction to the descriptor rows

`pad_rowTraffic`: zero padding rows carry no messages; `rows_traffic`: the trace-free traffic
`rowsTrafficFp Codec.table.interactions (codecCell Bs) 22 t pub b s` of table 11 is the concatenation, over
the descriptor rows `r < |allDescs Bs|`, of the row traffic of the row function reading
`lookup (allDescs Bs)[r]!.asg`.  (First step of the per-bus message lists.)
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.Near

instance : Inhabited Desc := ⟨.hdr ⟨0, 0, 0, false, 0, 0, 0⟩ 0⟩

/-- The row function of one descriptor. -/
def dRow (d : Desc) (r : Nat) : Trace Fp := rowFn (fun _ c => lookup d.asg c 0) 22 r

theorem multNat_go_zero {tr : Trace Fp} {t r : Nat} {pub : List Fp} :
    ∀ (l : List Expr) (k : Nat), (∀ e ∈ l, e.eval tr t r pub = 0) →
      Interaction.multNat.go tr t r pub l k = 0
  | [], _, _ => rfl
  | e :: l, k, h => by
    simp only [Interaction.multNat.go]
    rw [h e (List.mem_cons_self ..), multNat_go_zero l (k + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have : (0 : Fp) ≠ 1 := by decide
    simp [this]

theorem pad_rowTraffic (Bs : List Blk) (r : Nat) (hr : (allDescs Bs).length ≤ r) (t : Nat)
    (pub : List Fp) (b : Nat) (s : Bool) :
    rowTraffic Codec.table.interactions (rowFn (codecCell Bs) 22 r) t r pub b s = [] := by
  have hz : ∀ c, (rowFn (codecCell Bs) 22 r).cell t r c = 0 := by
    intro c
    change Fp.ofNat (codecCell Bs r c) = 0
    unfold codecCell
    rw [natCell_pad _ r hr]; rfl
  have hm := CodecPadding.physical_mult_zero _ t r pub hz
  unfold rowTraffic
  apply List.flatMap_eq_nil_iff.mpr
  intro i hi
  split
  · rw [show i.multNat (rowFn (codecCell Bs) 22 r) t r pub = 0 from
      multNat_go_zero i.mult 0 (hm i hi)]
    rfl
  · rfl

theorem rowFn_desc (Bs : List Blk) (r : Nat) (hr : r < (allDescs Bs).length) :
    rowFn (codecCell Bs) 22 r = dRow (allDescs Bs)[r]! r := by
  unfold dRow rowFn
  congr
  funext _ _ c
  unfold codecCell
  rw [natCell_desc _ r hr, getElem!_pos _ r hr]

/-- **The codec traffic is the traffic of its descriptor rows.** -/
theorem rows_traffic (Bs : List Blk) (hcap : (allDescs Bs).length ≤ 2 ^ 22) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) :
    rowsTrafficFp Codec.table.interactions (codecCell Bs) 22 t pub b s =
      (List.range (allDescs Bs).length).flatMap fun r =>
        rowTraffic Codec.table.interactions (dRow (allDescs Bs)[r]! r) t r pub b s := by
  unfold rowsTrafficFp
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ 22 = (allDescs Bs).length + m := ⟨2 ^ 22 - (allDescs Bs).length, by omega⟩
  rw [hm, List.range_add, List.flatMap_append]
  have h2 : ((List.range m).map ((allDescs Bs).length + ·)).flatMap
      (fun r => rowTraffic Codec.table.interactions (rowFn (codecCell Bs) 22 r) t r pub b s) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨j, _, rfl⟩ := hr
    exact pad_rowTraffic Bs _ (by omega) t pub b s
  rw [h2, List.append_nil]
  apply flatMap_congr_rt
  intro r hr
  rw [rowFn_desc Bs r (List.mem_range.mp hr)]

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near
open ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E

theorem dRow_col (d : Desc) (r t : Nat) (pub : List Fp) (c : Nat) (nx : Bool) :
    (Expr.col c nx).eval (dRow d r) t r pub = Fp.ofNat (lookup d.asg c 0) := rfl

set_option maxRecDepth 65536 in
/-- `S0F` (received once per instance, on the first header row): `[τ, pres, vid]`. -/
theorem hdr_s0f (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_S0F false =
      if p = 0 then [[Fp.ofNat I.tv, Fp.ofNat (b2n I.pres), Fp.ofNat I.vid]] else [] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false]
  simp only [Interaction.multNat, Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil,
    c, dRow_col, Desc.asg]
  simp only [hdrA, instA, regA, pbits, qbits, lookup_app, lookup_ite, lookup_cons, lookup_nil,
    List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, kF, tau, pres, vid, act, kH, pos, NN, nn, base, fair, itz, zt, bpost, bpre, vbg,
    ihp, ehp, pbit, prbit, reg_0, reg_1, reg_2, reg_3, reg_4, reg_5, reg_6, reg_7, reg_8, reg_9, reg_10,
    reg_11, reg_12, reg_13, reg_14, reg_15, reg_16, reg_17, reg_18, reg_19, reg_20, reg_21, reg_22,
    reg_23, reg_24, reg_25, reg_26, reg_27, reg_28, reg_29, reg_30, reg_31, Nat.reduceEqDiff,
    ite_true, ite_false]
  have h1 : Fp.ofNat 1 = 1 := rfl
  have h0 : Fp.ofNat 0 ≠ 1 := by decide
  by_cases hp : p = 0 <;> simp [hp, h1, h0]

end ZkFormal.NearV3.Render.Cdc
