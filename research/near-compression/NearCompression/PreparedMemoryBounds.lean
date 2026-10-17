import NearCompression.PreparedMemoryAddress
import NearCompression.PreparedFunctionRow
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def preparedMemorySum19 (term : Nat→Expr) : Expr :=
  .add (preparedGasSumTree term 4 0)
    (.add (preparedGasSumTree term 1 16) (term 18))
def preparedMemoryWidth (i : Nat) : Nat := [4,8,1,1,2,2,1,1,2,2,4,4,4,8,1,2,1,2,4].getD i 0
def preparedMemoryWidthExpr : Expr :=
  preparedMemorySum19 (fun i=>.mul (.col i false) (.const (preparedMemoryWidth i)))
def preparedMemoryCarryExpr (base : Nat) : Expr :=
  .add (.mul (.const 1) (.col base false)) (.mul (.const 2) (.col (base+1) false))
def preparedMemoryBoundsEquations : List Expr := [
  .add (preparedMemorySum19 (fun i=>.col i false)) (.neg (.const 1)),
  .add (.add (.add (preparedGasBits 179) preparedMemoryWidthExpr) (preparedGasBits 421))
    (.neg (.mul (.const 65536) (preparedMemoryCarryExpr 456))),
  .add (.add (.add (preparedGasBits 195) (preparedGasBits 437)) (preparedMemoryCarryExpr 456))
    (.neg (.add (preparedGasBits 212) (.mul (.const 65536) (preparedMemoryCarryExpr 458)))),
  .add (.add (.add (.col 211 false) (.col 453 false)) (preparedMemoryCarryExpr 458)) (.neg (.col 228 false))]
def PreparedMemoryBoundsHolds (row : Nat→Fp) : Prop :=
  PreparedMemoryAddressHolds row ∧ ∀e∈preparedMemoryBoundsEquations,e.evalWith (preparedGasEnv row [])=0

private theorem sum19_eval (row : Nat→Fp) (term : Nat→Expr) :
    (preparedMemorySum19 term).evalWith (preparedGasEnv row [])=
      preparedFieldSum 19 (fun i=>(term i).evalWith (preparedGasEnv row [])) := by
  simp only [preparedMemorySum19,preparedGasSumTree,preparedFieldSum,Expr.evalWith,Nat.reduceAdd,Nat.reducePow]
  change _ = _
  simp only [preparedGasEnv,instructionAddEnv]
  grind

theorem prepared_memory_bounds_opcode (row : Nat→Fp) (holds : PreparedMemoryBoundsHolds row) :
    ∃selected,selected<19 ∧ (∀i,i<19→row i=if i=selected then 1 else 0) ∧
      preparedMemoryWidth selected∈[1,2,4,8] ∧
      preparedMemoryWidthExpr.evalWith (preparedGasEnv row [])=Fp.ofNat (preparedMemoryWidth selected) := by
  have h:=holds.2 _ (List.mem_cons_self ..)
  change (preparedMemorySum19 (fun i=>.col i false)).evalWith (preparedGasEnv row []) + -(1:Fp)=0 at h
  rw [sum19_eval] at h
  have sum : preparedFieldSum 19 row=1 := by change preparedFieldSum 19 row + -(1:Fp)=0 at h;grind
  obtain ⟨selected,hs,hot⟩:=prepared_onehot 19 0 row (by decide)
    (by intro i hi;simpa only [Nat.zero_add] using prepared_memory_address_boolean row holds.1 i (by omega))
    (by simpa only [Nat.zero_add] using sum)
  simp only [Nat.zero_add] at hot
  refine ⟨selected,hs,hot,?_,?_⟩
  · have all : ∀i:Fin 19,preparedMemoryWidth i∈[1,2,4,8] := by decide
    exact all ⟨selected,hs⟩
  · unfold preparedMemoryWidthExpr
    rw [sum19_eval]
    exact prepared_sum_select 19 selected row (fun i=>Fp.ofNat (preparedMemoryWidth i)) hs hot

private theorem carry_nat (row : Nat→Fp) (holds : PreparedMemoryAddressHolds row) (base : Nat)
    (hb : base+1<460) :
    ((preparedMemoryCarryExpr base).evalWith (preparedGasEnv row [])).toNat=
      (row base).toNat+2*(row (base+1)).toNat := by
  have a:=prepared_memory_address_boolean row holds base (by omega)
  have b:=prepared_memory_address_boolean row holds (base+1) hb
  change (Fp.add (Fp.mul (Fp.ofNat 1) (row base)) (Fp.mul (Fp.ofNat 2) (row (base+1)))).toNat=_
  simp only [Fp.toNat_add,Fp.toNat_mul,Fp.toNat_ofNat]
  have p1:(row base).toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have p2:2*(row (base+1)).toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have p3:(row base).toNat+2*(row (base+1)).toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have one : 1%ZkFormal.Algebra.P=1 := by decide
  have two : 2%ZkFormal.Algebra.P=2 := by decide
  rw [one,two,Nat.one_mul]
  change ((row base).toNat%ZkFormal.Algebra.P+(2*(row (base+1)).toNat)%ZkFormal.Algebra.P)%ZkFormal.Algebra.P=_
  rw [Nat.mod_eq_of_lt p1,Nat.mod_eq_of_lt p2,Nat.mod_eq_of_lt p3]

private theorem bounded_sum (a b ci out co : Fp)
    (ha:a.toNat<65536) (hb:b.toNat<65536) (hc:ci.toNat≤8)
    (ho:out.toNat<65536) (hco:co.toNat≤3)
    (h:a+b+ci=out+(65536:Fp)*co) :
    a.toNat+b.toNat+ci.toNat=out.toNat+65536*co.toNat := by
  have hn:=congrArg Fp.toNat h
  change (Fp.add (Fp.add a b) ci).toNat=(Fp.add out (Fp.mul (Fp.ofNat 65536) co)).toNat at hn
  simp only [Fp.toNat_add,Fp.toNat_mul,Fp.toNat_ofNat] at hn
  have p1:a.toNat+b.toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have p2:a.toNat+b.toNat+ci.toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have p3:65536*co.toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  have p4:out.toNat+65536*co.toNat<ZkFormal.Algebra.P:=by unfold ZkFormal.Algebra.P;omega
  change ((a.toNat+b.toNat)%ZkFormal.Algebra.P+ci.toNat)%ZkFormal.Algebra.P=
    (out.toNat+(65536*co.toNat)%ZkFormal.Algebra.P)%ZkFormal.Algebra.P at hn
  simpa only [Nat.mod_eq_of_lt p1,Nat.mod_eq_of_lt p2,Nat.mod_eq_of_lt p3,Nat.mod_eq_of_lt p4] using hn

/-- Exact successful access bound, derived over naturals from the source
carry equations. The memory page count still must be authenticated by EXEC. -/
theorem prepared_memory_bounds_success (row : Nat→Fp) (holds : PreparedMemoryBoundsHolds row) :
    ∃width,width∈[1,2,4,8] ∧
      preparedMemoryWidthExpr.evalWith (preparedGasEnv row [])=Fp.ofNat width ∧
      preparedMemoryAddressWord row 115+preparedMemoryAddressWord row 147+width≤
        ((preparedMemoryAddressLimb row 212).toNat+65536*(row 228).toNat)*65536 := by
  obtain ⟨selected,_,_,widths,decode⟩:=prepared_memory_bounds_opcode row holds
  let width:=preparedMemoryWidth selected
  have wb : width≤8 := by
    change width∈[1,2,4,8] at widths
    simp only [List.mem_cons,List.not_mem_nil,or_false] at widths
    omega
  have wf : (Fp.ofNat width).toNat=width := by
    rw [Fp.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    unfold ZkFormal.Algebra.P;omega
  have get (i : Fin 4) := holds.2 (preparedMemoryBoundsEquations[i]) (List.getElem_mem i.isLt)
  have h0:=get ⟨1,by decide⟩;have h1:=get ⟨2,by decide⟩;have h2:=get ⟨3,by decide⟩
  let c0:=(preparedMemoryCarryExpr 456).evalWith (preparedGasEnv row [])
  let c1:=(preparedMemoryCarryExpr 458).evalWith (preparedGasEnv row [])
  have cb (base : Nat) (hb:base+1<460):
      ((preparedMemoryCarryExpr base).evalWith (preparedGasEnv row [])).toNat≤3 := by
    rw [carry_nat row holds.1 base hb]
    have a:=prepared_memory_address_boolean row holds.1 base (by omega)
    have b:=prepared_memory_address_boolean row holds.1 (base+1) hb
    omega
  have b (base : Nat) (hb:base+16≤460):=prepared_memory_address_limb_bound row holds.1 base hb
  change preparedMemoryAddressLimb row 179+preparedMemoryWidthExpr.evalWith (preparedGasEnv row [])+
    preparedMemoryAddressLimb row 421 + -((65536:Fp)*c0)=0 at h0
  rw [decode] at h0
  have l0:=bounded_sum (preparedMemoryAddressLimb row 179) (preparedMemoryAddressLimb row 421)
    (Fp.ofNat width) 0 c0 (b 179 (by decide)) (b 421 (by decide)) (by rw [wf];exact wb)
    (by decide) (cb 456 (by decide)) (by change _ = _;grind)
  change preparedMemoryAddressLimb row 195+preparedMemoryAddressLimb row 437+c0+
    -(preparedMemoryAddressLimb row 212+(65536:Fp)*c1)=0 at h1
  have l1:=bounded_sum _ _ c0 _ c1 (b 195 (by decide)) (b 437 (by decide))
    (by have x : c0.toNat≤3:=cb 456 (by decide);omega) (b 212 (by decide)) (cb 458 (by decide)) (by grind)
  change row 211+row 453+c1+ -row 228=0 at h2
  have bit (i:Nat) (hi:i<460):=prepared_memory_address_boolean row holds.1 i hi
  have l2:=bounded_sum (row 211) (row 453) c1 (row 228) 0
    (by have x:=bit 211 (by decide);omega) (by have x:=bit 453 (by decide);omega)
    (by have x : c1.toNat≤3:=cb 458 (by decide);omega) (by have x:=bit 228 (by decide);omega) (by decide) (by grind)
  have addr:=prepared_memory_address_exact row holds.1
  refine ⟨width,widths,decode,?_⟩
  rw [wf] at l0
  have zero:(0:Fp).toNat=0:=rfl
  rw [zero] at l0 l2
  simp only [preparedMemoryAddressWord,Nat.reduceAdd] at addr ⊢
  omega
end NearCompression
