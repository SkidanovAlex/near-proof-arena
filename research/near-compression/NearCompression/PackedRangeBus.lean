import ZkFormal.V2.VerifierDefs
import NearCompression.PackedConcreteRewrite
import ZkFormal.Chacha.Bus

/-! Byte ranges from the concrete receiver constraints and exact natural bus
balance. Cryptographic acceptance-to-HoldsP is not supplied by this module. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def packedRangeValue : Expr :=
  preparedGasSumTree (fun i=>.mul (.const (2^i)) (.col i false)) 3 0

def packedRangeReceive : Interaction :=
  {bus:=4,send:=false,msg:=[packedRangeValue],
    mult:=(List.range 16).map (fun i=>.col (8+i) false)}

def packedRangeSend (column : Nat) : Interaction :=
  {bus:=4,send:=true,msg:=[.col column false],mult:=[.const 1]}

def packedRangeTable : Table :=
  {width:=24,maxLog:=22,constraints:=(List.range 24).map preparedGasBoolean,
    interactions:=[packedRangeReceive]}

theorem packed_range_value_bound (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (holds : ∀ e∈packedRangeTable.constraints,e.eval tr t r pub=0) :
    (packedRangeValue.eval tr t r pub).toNat<256 := by
  have bits : ∀ k,k<8 → (tr.cell t r k).toNat≤1 := by
    intro k hk
    have h:=holds (preparedGasBoolean k) (List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩)
    change tr.cell t r k*(tr.cell t r k+ -(1:Fp))+ -(0:Fp)=0 at h
    apply instruction_add_boolean_bound
    grind
  have eq : packedRangeValue.eval tr t r pub =
      (instructionBitExpr 0 8).evalWith (instructionAddEnv (tr.cell t r)) := by
    simp only [packedRangeValue,preparedGasSumTree,instructionBitExpr,Expr.eval,
      Expr.evalWith,rowEnv,instructionAddEnv,Nat.reduceAdd,Nat.reducePow,
      Bool.false_eq_true,ite_false]
    simp only [←Fp.ofNat_def]
    grind
  rw [eq]
  exact instruction_bit_expr_bound (tr.cell t r) 8 0 (by decide)
    (by simpa using bits)

/-- A positive receiver count must name a byte, even when receiver rows are
repeated, unordered, or have zero multiplicity. No enumeration assumption. -/
theorem packed_range_received_bound (tr : Trace Fp) (pub : List Fp) (t : Nat) (value : Fp)
    (constraints : ∀ r,r<tr.height t → ∀ e∈packedRangeTable.constraints,e.eval tr t r pub=0)
    (positive : tableBusCount [packedRangeReceive] tr t pub 4 false [value]≠0) :
    value.toNat<256 := by
  obtain ⟨r,hr,i,hi,_,_,message,_⟩:=ZkFormal.Chacha.exists_of_tableBusCount positive
  have same : i=packedRangeReceive := List.mem_singleton.mp hi
  subst i
  have eq : packedRangeValue.eval tr t r pub=value := by
    simpa [Interaction.msgVal,packedRangeReceive] using message
  rw [←eq]
  exact packed_range_value_bound tr pub t r (constraints r hr)

/-- The public statement may not inject alternative range messages. Receiver
isolation and constraint membership are structural obligations on the AIR. -/
theorem packed_range_from_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP air pub tr) (rangeTable : Nat)
    (noPublic : ∀ seg∈air.pubSegs,seg.bus≠4)
    (receiver : ∀ t, t<air.tables.length → ∀ i∈air.tables[t]!.interactions,
      i.bus=4 → i.send=false → t=rangeTable ∧ i=packedRangeReceive)
    (rangeConstraints : ∀ ht : rangeTable<air.tables.length,
      ∀ e∈packedRangeTable.constraints,e∈air.tables[rangeTable].constraints)
    (t r column : Nat) (ht : t<air.tables.length) (hr : r<tr.height t)
    (sender : packedRangeSend column∈air.tables[t]!.interactions) :
    (tr.cell t r column).toNat<256 := by
  let message : List Fp := [tr.cell t r column]
  have mult : (packedRangeSend column).multNat tr t r pub≠0 := by
    change (1:Nat)≠0
    decide
  have positive := ZkFormal.Chacha.tableBusCount_pos hr sender mult
  have ge := ZkFormal.Chacha.busCount_go_ge tr pub 4 true message air.tables 0 t ht
  have sendPositive : busCount air.toAir tr pub 4 true message≠0 := by
    change tableBusCount air.tables[t]!.interactions tr t pub 4 true message≠0 at positive
    simp only [Nat.zero_add] at ge
    unfold busCount
    omega
  have noPub (side : Bool) : pubCount air pub 4 side message=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member bus
    exact False.elim (noPublic seg member bus)
  have balance:=holds.balance 4 message
  rw [noPub true,noPub false,Nat.add_zero,Nat.add_zero] at balance
  have receivePositive : busCount air.toAir tr pub 4 false message≠0 := by
    rw [←balance]
    exact sendPositive
  obtain ⟨s,hs,count⟩:=ZkFormal.Chacha.busCount_go_pos tr pub 4 false message air.tables 0 receivePositive
  simp only [Nat.zero_add] at count
  obtain ⟨row,hrow,i,hi,bus,side,msg,_⟩:=ZkFormal.Chacha.exists_of_tableBusCount count
  obtain ⟨tableEq,interactionEq⟩:=receiver s hs i hi bus side
  subst s
  subst i
  have msgEq : packedRangeValue.eval tr rangeTable row pub=tr.cell t r column := by
    simpa [Interaction.msgVal,packedRangeReceive,message] using msg
  rw [←msgEq]
  apply packed_range_value_bound tr pub rangeTable row
  intro e he
  exact holds.constr rangeTable hs row hrow e (rangeConstraints hs e he)

/-- Checkable AIR structure needed to isolate the range receiver. -/
structure PackedRangeSource (air : AirP) (rangeTable : Nat) : Prop where
  noPublic : ∀ seg∈air.pubSegs,seg.bus≠4
  receiver : ∀ t,t<air.tables.length → ∀ i∈air.tables[t]!.interactions,
    i.bus=4 → i.send=false → t=rangeTable ∧ i=packedRangeReceive
  constraints : ∀ ht : rangeTable<air.tables.length,
    ∀ e∈packedRangeTable.constraints,e∈air.tables[rangeTable].constraints

/-- Both current and cyclic next-row range premises follow from HoldsP. -/
theorem packed_macro_ranges_from_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP air pub tr) (rangeTable : Nat) (source : PackedRangeSource air rangeTable)
    (regions : List (Nat × Nat)) (t r : Nat) (ht : t<air.tables.length) (hr : r<tr.height t)
    (senders : ∀ base∈packedMacroBases regions,
      packedRangeSend (packedColumnIndex regions base)∈air.tables[t]!.interactions ∧
      packedRangeSend (packedColumnIndex regions (base+8))∈air.tables[t]!.interactions) :
    PackedMacroRanges regions (rowEnv tr t r pub) := by
  intro base hb nx
  let row := if nx then (r+1)%tr.height t else r
  have rowBound : row<tr.height t := by
    cases nx
    · exact hr
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  constructor
  · exact packed_range_from_holds air tr pub holds rangeTable source.noPublic
      source.receiver source.constraints t row _ ht rowBound (senders base hb).1
  · exact packed_range_from_holds air tr pub holds rangeTable source.noPublic
      source.receiver source.constraints t row _ ht rowBound (senders base hb).2

/-- Concrete expression rewriting no longer requires external byte bounds. -/
theorem packed_rewrite_from_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP air pub tr) (rangeTable : Nat) (source : PackedRangeSource air rangeTable)
    (regions : List (Nat × Nat)) (consistent : PackedLayoutConsistent regions)
    (t r : Nat) (ht : t<air.tables.length) (hr : r<tr.height t)
    (senders : ∀ base∈packedMacroBases regions,
      packedRangeSend (packedColumnIndex regions base)∈air.tables[t]!.interactions ∧
      packedRangeSend (packedColumnIndex regions (base+8))∈air.tables[t]!.interactions)
    (e e' : Expr) (rewritten : packedRewrite (packedConcreteMacro regions)
      (packedConcreteColumn regions) e=some e') :
    e'.eval tr t r pub=e.evalWith (packedLiftEnv regions (rowEnv tr t r pub)) := by
  exact packed_concrete_rewrite_eval regions consistent (rowEnv tr t r pub) rfl rfl rfl
    (packed_macro_ranges_from_holds air tr pub holds rangeTable source regions t r ht hr senders)
    e e' rewritten

end NearCompression
