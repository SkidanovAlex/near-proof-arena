import NearCompression.PreparedWasmConstruct
import ZkFormal.Chacha.Bus
import ZkFormal.V2.VerifierDefs

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air ZkFormal.V2 NearSpecV3.Wasm

def preparedBoundaryPC : Expr := preparedBalancedSum (fun i=>.mul (.const i) (.col i false)) 4 0

def preparedBoundaryMessage : List Expr :=
  [preparedBoundaryPC,preparedSPIndexPython false,.col 25 false,.col 26 false] ++
  (List.range 4).map (fun i=>preparedGasBits (283+16*i)) ++
  (List.range 8).flatMap (fun slot=>(List.range 2).map (fun limb=>preparedGasBits (27+32*slot+16*limb)))

def preparedBoundaryInteraction (last : Bool) : Interaction :=
  {bus:=if last then 1 else 0,send:=true,msg:=preparedBoundaryMessage,mult:=[if last then .isLast else .isFirst]}
def preparedBoundarySegment (last : Bool) : PubSeg :=
  {bus:=if last then 1 else 0,send:=false,width:=24,countAt:=if last then 4 else 0,start:=if last then 32 else 8}
def preparedBoundaryTable (constraints : List Expr) : Table :=
  {width:=449,maxLog:=5,constraints:=constraints,interactions:=[preparedBoundaryInteraction false,preparedBoundaryInteraction true]}
def preparedBoundaryAir (constraints : List Expr) : AirP :=
  {tables:=[preparedBoundaryTable constraints],numBuses:=2,numPub:=216,maxPub:=216,
    pubSegs:=[preparedBoundarySegment false,preparedBoundarySegment true]}

def preparedBoundaryCountsCheck (pub : List Fp) : Bool :=
  decide ((preparedBoundarySegment false).count pub=1 ∧ (preparedBoundarySegment true).count pub=1)

def preparedPublicBoundary (pub : List Fp) (last : Bool) : List Fp :=
  (List.range 24).map (fun i=>pub.getD ((if last then 32 else 8)+i) 0)

theorem prepared_public_boundary_record (pub : List Fp) (last : Bool) :
    (preparedBoundarySegment last).record pub 0=preparedPublicBoundary pub last := by
  cases last <;> rfl

theorem prepared_boundary_public_messages (constraints : List Expr) (pub : List Fp)
    (counts : preparedBoundaryCountsCheck pub=true) :
    pubMsgs (preparedBoundaryAir constraints) pub=
      [(0,false,preparedPublicBoundary pub false),(1,false,preparedPublicBoundary pub true)] := by
  have count:=of_decide_eq_true counts
  simp only [pubMsgs,preparedBoundaryAir,List.flatMap_cons,List.flatMap_nil,PubSeg.msgs,
    count.1,count.2,List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
    List.cons_append,List.append_nil,prepared_public_boundary_record]
  rfl

theorem prepared_boundary_no_table_receives (constraints : List Expr) (tr : Trace Fp)
    (pub : List Fp) (bus : Nat) (message : List Fp) :
    busCount (preparedBoundaryAir constraints).toAir tr pub bus false message=0 := by
  simp [busCount,busCount.go,preparedBoundaryAir,preparedBoundaryTable,
    ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.rowTraffic,preparedBoundaryInteraction]
  have empty : ∀ rows : List Nat,rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
    intro rows;induction rows <;> simp_all
  rw [empty];rfl

/-- Natural V2 bus balance authenticates the complete24-field boundary message.
This uses the actual first/last interaction and public receive segment; it
cannot be obtained from TableLocal alone. -/
theorem prepared_boundary_message_bound (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (counts : preparedBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    (preparedBoundaryInteraction last).msgVal tr 0 r pub=preparedPublicBoundary pub last := by
  have active : (preparedBoundaryInteraction last).multNat tr 0 r pub≠0 := by
    cases last <;> simp only [Bool.false_eq_true,ite_false,ite_true] at endpoint ⊢ <;>
      simp [Interaction.multNat,Interaction.multNat.go,preparedBoundaryInteraction,Expr.eval,Expr.evalWith,rowEnv,endpoint]
  have member : preparedBoundaryInteraction last∈(preparedBoundaryTable constraints).interactions := by
    cases last <;> simp [preparedBoundaryTable]
  have traffic:=ZkFormal.Chacha.tableBusCount_pos hr member active
  let message:=(preparedBoundaryInteraction last).msgVal tr 0 r pub
  have nonzero : busCount (preparedBoundaryAir constraints).toAir tr pub (if last then 1 else 0) true message≠0 := by
    simpa only [busCount,busCount.go,preparedBoundaryAir,Nat.add_zero,preparedBoundaryInteraction,message] using traffic
  have balance:=holds.balance (if last then 1 else 0) message
  rw [prepared_boundary_no_table_receives] at balance
  have publicMessages:=prepared_boundary_public_messages constraints pub counts
  have sendZero : pubCount (preparedBoundaryAir constraints) pub (if last then 1 else 0) true message=0 := by
    cases last <;> simp [pubCount,publicMessages]
  rw [sendZero,Nat.add_zero,Nat.zero_add] at balance
  have receiveNonzero : pubCount (preparedBoundaryAir constraints) pub (if last then 1 else 0) false message≠0 := by
    rw [←balance];exact nonzero
  by_cases same : message=preparedPublicBoundary pub last
  · exact same
  · have zero : pubCount (preparedBoundaryAir constraints) pub (if last then 1 else 0) false message=0 := by
      cases last <;> simp [pubCount,publicMessages,Ne.symm same]
    exact False.elim (receiveNonzero zero)

def preparedPublicGas (pub : List Fp) (last : Bool) : Nat :=
  preparedGasWord (fun i=>(pub.getD ((if last then 32 else 8)+4+i) 0).toNat)

theorem prepared_boundary_gas_field (tr : Trace Fp) (pub : List Fp) (r i : Nat) (last : Bool)
    (hi : i<4) :
    ((preparedBoundaryInteraction last).msgVal tr 0 r pub).getD (4+i) 0=
      preparedGasLimb (tr.cell 0 r) pub 283 i := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with eq|eq|eq|eq <;> subst i <;> rfl

theorem prepared_public_gas_field (pub : List Fp) (i : Nat) (last : Bool) (hi : i<4) :
    (preparedPublicBoundary pub last).getD (4+i) 0=pub.getD ((if last then 32 else 8)+4+i) 0 := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with eq|eq|eq|eq <;> subst i <;> cases last <;> rfl

/-- Four separately authenticated limbs reconstruct the exact64-bit gas value,
without reducing the whole word to one field element. -/
theorem prepared_boundary_gas_bound (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (counts : preparedBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    preparedGasValue (tr.cell 0 r) pub=preparedPublicGas pub last := by
  have message:=prepared_boundary_message_bound constraints tr pub holds counts last r hr endpoint
  have limb (i : Nat) (hi : i<4) := congrArg (fun msg:List Fp=>msg.getD (4+i) 0) message
  have exactLimb (i : Nat) (hi : i<4) :
      preparedGasLimb (tr.cell 0 r) pub 283 i=pub.getD ((if last then 32 else 8)+4+i) 0 := by
    simpa only [prepared_boundary_gas_field tr pub r i last hi,prepared_public_gas_field pub i last hi] using limb i hi
  unfold preparedGasValue preparedPublicGas preparedGasWord
  dsimp only
  rw [exactLimb 0 (by decide),exactLimb 1 (by decide),exactLimb 2 (by decide),exactLimb 3 (by decide)]

theorem prepared_boundary_status_bound (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (counts : preparedBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    tr.cell 0 r 25=pub.getD ((if last then 32 else 8)+2) 0 ∧
    tr.cell 0 r 26=pub.getD ((if last then 32 else 8)+3) 0 := by
  have message:=prepared_boundary_message_bound constraints tr pub holds counts last r hr endpoint
  have done:=congrArg (fun msg:List Fp=>msg.getD 2 0) message
  have fail:=congrArg (fun msg:List Fp=>msg.getD 3 0) message
  cases last <;> exact ⟨done,fail⟩

/-- Initial gas provenance now comes from the real public bus. The external
host comparison is a public-statement check, not an assumed row equality. -/
theorem prepared_boundary_initial_gas (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (counts : preparedBoundaryCountsCheck pub=true) (positive : 0<tr.height 0)
    (host : St) (pf : PFunc)
    (claim : preparedPublicGas pub false=host.gas.remaining-pf.prologueGas) :
    preparedGasValue (tr.cell 0 0) pub=host.gas.remaining-pf.prologueGas := by
  rw [prepared_boundary_gas_bound constraints tr pub holds counts false 0 positive rfl,claim]

end NearCompression
