import ZkFormal.NearV3.Render.SchedBusProc
import ZkFormal.NearV3.Candidates.MemComparisonPhysical

/-!
# Memory table (14) traffic on `SOP` (receives) and `SFIN` (sends), over all runs
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.MemBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Candidates MemConcatCells
open ZkFormal.NearV3.Render.ProcBus (nf cast_eq f0 f1)

def mSop (X : MV) : List (List Fp) :=
  List.replicate (if Fp.ofNat X.act = 1 then 1 else 0)
    [Fp.ofNat X.addr, Fp.ofNat X.t, Fp.ofNat X.isRd + ((2:Nat):Fp) * Fp.ofNat X.isGr, Fp.ofNat X.vin,
      Fp.ofNat X.v, Fp.ofNat X.inc, Fp.ofNat X.ok, Fp.ofNat X.cc]

def mFin (X : MV) : List (List Fp) :=
  List.replicate (if Fp.ofNat X.lst = 1 then 1 else 0) [Fp.ofNat X.addr, Fp.ofNat X.v, Fp.ofNat X.w]

theorem row_sop (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic Mem.interactions (trace rs) t r pub B_SOP false = mSop ((records rs).getD r padV) := by
  simp [mSop,Mem.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.smul, Mem.opE,
    trace,SchedHeight.trace,cell,B_SCMP,B_SOP,B_SFIN, MV.cell, Mem.act, Mem.addr, Mem.t, Mem.isRd, Mem.isGr,
    Mem.vin, Mem.v, Mem.inc, Mem.ok, Mem.cc]

theorem row_fin (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic Mem.interactions (trace rs) t r pub B_SFIN true = mFin ((records rs).getD r padV) := by
  simp [mFin,Mem.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    trace,SchedHeight.trace,cell,B_SCMP,B_SOP,B_SFIN, MV.cell, Mem.lst, Mem.addr, Mem.v, Mem.w]

theorem sop_init (g : Gen.Seg) : mSop (initV g) = [nf (sopInit g)] := by
  simp [mSop, initV, sopInit, nf, f1, OP_INIT, ProcBus.cast_eq]
  all_goals decide
theorem sop_op (g : Gen.Seg) (i tp : Nat) (o : Gen.MOp) (ho : ProcActualMemoryTags.OpTag o) :
    mSop (opV g i tp o) = [nf (sopOp g o)] := by
  rcases ho.1 with h | h <;> simp [mSop, opV, sopOp, nf, f1, h, OP_READ, OP_GRANT, b2n, ProcBus.cast_eq] <;> decide
theorem sop_pad : mSop padV = [] := by simp [mSop, padV, f0]
theorem fin_pad : mFin padV = [] := by simp [mFin, padV, f0]

theorem sop_ops (g : Gen.Seg) : ∀ (k tp : Nat) (os : List Gen.MOp), (∀ o ∈ os, ProcActualMemoryTags.OpTag o) →
    (opsVs g k tp os).flatMap mSop = os.map (fun o => nf (sopOp g o))
  | _, _, [], _ => rfl
  | k, tp, o :: os, h => by
    rw [opsVs, List.flatMap_cons, sop_op g _ _ o (h o (by simp)), sop_ops g (k + 1) o.t os (fun x hx => h x (by simp [hx]))]
    rfl

theorem sop_seg (g : Gen.Seg) (hg : ProcActualMemoryTagSegments.SegTag g) :
    (segVs g).flatMap mSop = (sopInit g :: g.ops.map (sopOp g)).map nf := by
  rw [segVs, List.flatMap_cons, sop_init, sop_ops g 0 0 g.ops hg]
  simp

theorem lst_le (g : Gen.Seg) : ∀ X ∈ segVs g, X.lst ≤ 1 := by
  have hops : ∀ k tp os, ∀ X ∈ opsVs g k tp os, X.lst ≤ 1 := by
    intro k tp os
    induction os generalizing k tp with
    | nil => simp [opsVs]
    | cons o os ih =>
      intro X hX
      simp only [opsVs, List.mem_cons] at hX
      rcases hX with rfl | hX
      · simp only [opV, b2n]; split <;> omega
      · exact ih _ _ X hX
  intro X hX
  simp only [segVs, List.mem_cons] at hX
  rcases hX with rfl | hX
  · simp only [initV, b2n]; split <;> omega
  · exact hops _ _ _ X hX

theorem fin_rowMsgs (X : MV) (h : X.lst ≤ 1) : mFin X = (rowMsgs B_SFIN true X).map nf := by
  rw [rowMsgs_fin]
  rcases (show X.lst = 0 ∨ X.lst = 1 by omega) with h0 | h0 <;> simp [mFin, h0, f0, f1, finMsg, nf]

theorem fin_seg (g : Gen.Seg) : (segVs g).flatMap mFin = [nf [g.addr, g.vfin, g.wfin]] := by
  rw [Complete.flatMap_congr' (fun X hX => fin_rowMsgs X (lst_le g X hX)), ← List.map_flatMap, seg_fin]
  rfl

theorem gen_physical (F : MV → List (List Fp)) (b : Nat) (sd : Bool)
    (hrow : ∀ rs t r pub, rowTraffic Mem.interactions (trace rs) t r pub b sd = F ((records rs).getD r padV))
    (hpad : F padV = []) (rs : List Run) (hcap : (MemConcatCells.rows rs).size ≤ 2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r => rowTraffic Mem.interactions (trace rs) t r pub b sd) =
      (records rs).flatMap F := by
  have hc : (records rs).length ≤ 2^22 := by rw [← length]; exact hcap
  simp only [hrow]
  rw [show 2^22=(records rs).length+(2^22-(records rs).length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(records rs).length)).flatMap
      (fun j=>F ((records rs).getD ((records rs).length+j) padV))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    have he:(records rs).getD ((records rs).length+j) padV=padV := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (records rs).length≤(records rs).length+j)]
    rw [he, hpad]
  rw [hz,List.append_nil,ProcComparisonPhysical.range_flatMap]

def sopML (rs : List Run) : List (List Fp) := rs.flatMap fun R => (sopList R.segs).map nf
def finML (rs : List Run) : List (List Fp) := rs.flatMap fun R => (finList R.segs).map nf

theorem count_sop (rs : List Run) (hcap : (MemConcatCells.rows rs).size ≤ 2^22)
    (hg : ∀ R ∈ rs, ∀ g ∈ R.segs, ProcActualMemoryTagSegments.SegTag g) (t : Nat) (pub msg : List Fp) :
    tableBusCount Mem.interactions (trace rs) t pub B_SOP false msg = (sopML rs).count msg := by
  rw [tableBusCount_eq]
  have hp := gen_physical mSop _ _ row_sop sop_pad rs hcap t pub
  have he : (records rs).flatMap mSop = sopML rs := by
    simp only [records, memVs, List.flatMap_assoc, sopML, sopList, List.map_flatMap]
    apply Complete.flatMap_congr'
    intro R hR
    apply Complete.flatMap_congr'
    intro g hg'
    exact sop_seg g (hg R hR g hg')
  rw [← he, ← hp]; rfl

theorem count_fin (rs : List Run) (hcap : (MemConcatCells.rows rs).size ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Mem.interactions (trace rs) t pub B_SFIN true msg = (finML rs).count msg := by
  rw [tableBusCount_eq]
  have hp := gen_physical mFin _ _ row_fin fin_pad rs hcap t pub
  have he : (records rs).flatMap mFin = finML rs := by
    simp only [records, memVs, List.flatMap_assoc, finML, finList]
    apply Complete.flatMap_congr'
    intro R _
    rw [Complete.flatMap_congr' (fun g _ => fin_seg g)]
    induction R.segs with
    | nil => rfl
    | cons g segs ih => simp [ih]
  rw [← he, ← hp]; rfl

end ZkFormal.NearV3.Render.MemBus
