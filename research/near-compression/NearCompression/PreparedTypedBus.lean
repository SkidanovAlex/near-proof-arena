import NearCompression.PreparedCodeBus
import NearCompression.PreparedTypedLiteral
import NearCompression.PreparedLocalsBus
import ZkFormal.Chacha.Bus
import ZkFormal.V2.VerifierDefs

set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

def preparedTypedBusRecord (pc fn op imm fee has kind block branch target localStart highImm typedStart : Nat) : List Expr :=
  [preparedCodeBits fn,preparedCodeBits (fn+16),preparedCodeBits pc,preparedCodeBits (pc+16)] ++
  (List.range 4).map (fun i=>.col (op+i) false) ++ [preparedCodeBits imm,preparedCodeBits (imm+16)] ++
  (List.range 4).map (fun i=>preparedCodeBits (fee+16*i)) ++ [.col has false] ++
  (List.range 6).map (fun i=>.col (kind+i) false) ++ List.replicate 4 (.const 0) ++
  [.col block false,.col branch false,preparedCodeBits target,preparedCodeBits (target+16)] ++
  (List.range 3).map (fun i=>.col (localStart+i) false) ++
  [preparedCodeBits highImm,preparedCodeBits (highImm+16)] ++ (List.range 3).map (fun i=>.col (typedStart+i) false)
def preparedTypedBusFetch : Interaction :=
  {bus:=2,send:=true,mult:=[.const 1],msg:=preparedTypedBusRecord 0 573 466 470 502 566 567 605 606 607 683 1214 1280}
def preparedTypedBusReceive : Interaction :=
  {bus:=2,send:=false,mult:=(List.range 25).map (fun i=>.col (172+i) false),
    msg:=preparedTypedBusRecord 1 33 65 69 101 165 166 198 199 200 232 235 267}
def preparedTypedBusPublish : Interaction :=
  {bus:=3,send:=true,mult:=[.col 0 false],msg:=preparedTypedBusReceive.msg}
def preparedTypedBusPublicSegment : PubSeg :=
  {bus:=3,send:=false,width:=37,countAt:=8,start:=118}
def preparedTypedBusExecTable (constraints boundary : List Expr) : Table :=
  {width:=1285,maxLog:=22,constraints:=constraints,interactions:=[
    {bus:=0,send:=true,mult:=[.isFirst],msg:=boundary},
    {bus:=1,send:=true,mult:=[.isLast],msg:=boundary},preparedTypedBusFetch]}
def preparedTypedBusDataTable (constraints : List Expr) : Table :=
  {width:=270,maxLog:=22,constraints:=constraints,interactions:=[preparedTypedBusReceive,preparedTypedBusPublish]}
def preparedTypedBusAir (execConstraints codeConstraints boundary : List Expr) (codeLength : Nat) : AirP :=
  {tables:=[preparedTypedBusExecTable execConstraints boundary,preparedTypedBusDataTable codeConstraints],
    numBuses:=4,numPub:=118+37*codeLength,maxPub:=118+37*codeLength,pubSegs:=[
      {bus:=0,send:=false,width:=51,countAt:=0,start:=12},
      {bus:=1,send:=false,width:=51,countAt:=4,start:=63},preparedTypedBusPublicSegment]}
/-- A reusable exact-zero fact for natural bit multiplicity; no field sum. -/
theorem prepared_typed_bus_mult_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (xs : List Expr) (zero : ∀ e∈xs,e.eval tr t r pub=0) (k : Nat) :
    Interaction.multNat.go tr t r pub xs k=0 := by
  induction xs generalizing k with
  | nil => rfl
  | cons e es ih =>
    have h:=zero e (by simp)
    rw [Interaction.multNat.go,h,ite_eq_right (by decide),Nat.zero_add]
    exact ih (fun a ha=>zero a (by simp [ha])) (k+1)

theorem prepared_typed_bus_receive_active (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈table.constraints)
    (r : Nat) (hr : r<tr.height t) (used : preparedTypedBusReceive.multNat tr t r pub≠0) :
    tr.cell t r 0=1 := by
  have boolean:=prepared_code_boolean table tr t pub source localH r hr 0 (by decide)
  by_cases active : tr.cell t r 0=1
  · exact active
  · have zero : tr.cell t r 0=0 := by
      apply Fp.ext
      have notOne : (tr.cell t r 0).toNat≠1 := by
        intro eq
        apply active
        apply Fp.ext
        exact eq
      change (tr.cell t r 0).toNat=0
      omega
    apply False.elim
    apply used
    unfold Interaction.multNat preparedTypedBusReceive
    apply prepared_typed_bus_mult_zero
    intro e he
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
    have h:=localH.constr r hr _ (inactive i (List.mem_range.mp hi))
    change ((1:Fp)+ -tr.cell t r 0)*(tr.cell t r (172+i)+ -(0:Fp))=0 at h
    rw [zero] at h
    change tr.cell t r (172+i)=0
    grind

/-- The only receiver on fetch bus2 is the concrete CODE table. -/
theorem prepared_typed_bus_receive_count (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (message : List Fp) :
    busCount (preparedTypedBusAir ec cc boundary count).toAir tr pub 2 false message=
      tableBusCount [preparedTypedBusReceive] tr 1 pub 2 false message := by
  simp only [busCount,busCount.go,preparedTypedBusAir,preparedTypedBusExecTable,preparedTypedBusDataTable,Nat.add_zero]
  rw [ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.tableBusCount_eq]
  simp only [ZkFormal.Chacha.rowTraffic,List.flatMap_cons,List.flatMap_nil,preparedTypedBusFetch,
    preparedTypedBusReceive,preparedTypedBusPublish,Nat.reduceEqDiff,Bool.true_eq_false,
    and_false,ite_false,and_true,ite_true,List.append_nil]
  have empty (rows : List Nat) : rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
    induction rows <;> simp_all
  rw [empty]
  simp

/-- Every EXEC fetch matches an actually used CODE row by exact natural balance. -/
theorem prepared_typed_bus_fetch_matched (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr)
    (r : Nat) (hr : r<tr.height 0) :
    ∃ s,s<tr.height 1 ∧ preparedTypedBusReceive.msgVal tr 1 s pub=preparedTypedBusFetch.msgVal tr 0 r pub ∧
      preparedTypedBusReceive.multNat tr 1 s pub≠0 := by
  let air:=preparedTypedBusAir ec cc boundary count
  let message:=preparedTypedBusFetch.msgVal tr 0 r pub
  have mult : preparedTypedBusFetch.multNat tr 0 r pub≠0 := by change (1:Nat)≠0;decide
  have tablePositive:=ZkFormal.Chacha.tableBusCount_pos hr
    (show preparedTypedBusFetch∈(preparedTypedBusExecTable ec boundary).interactions by simp [preparedTypedBusExecTable]) mult
  have ge:=ZkFormal.Chacha.busCount_go_ge tr pub 2 true message air.tables 0 0 (by change 0<2;decide)
  have nonzero : busCount air.toAir tr pub 2 true message≠0 := by
    change tableBusCount (preparedTypedBusExecTable ec boundary).interactions tr 0 pub 2 true message≤_ at ge
    change tableBusCount (preparedTypedBusExecTable ec boundary).interactions tr 0 pub 2 true message≠0 at tablePositive
    unfold busCount
    omega
  have noPublic (side : Bool) : pubCount air pub 2 side message=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member bus
    simp only [air,preparedTypedBusAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> simp [preparedTypedBusPublicSegment] at bus
  have balance:=holds.balance 2 message
  rw [noPublic true,noPublic false,Nat.add_zero,Nat.add_zero] at balance
  have receivePositive : tableBusCount [preparedTypedBusReceive] tr 1 pub 2 false message≠0 := by
    rw [←prepared_typed_bus_receive_count ec cc boundary count tr pub message,←balance]
    exact nonzero
  obtain ⟨s,hs,i,hi,_,_,msg,mult⟩:=ZkFormal.Chacha.exists_of_tableBusCount receivePositive
  have same : i=preparedTypedBusReceive:=List.mem_singleton.mp hi
  subst i
  exact ⟨s,hs,msg,mult⟩

theorem prepared_typed_bus_no_public_table_receives (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (message : List Fp) :
    busCount (preparedTypedBusAir ec cc boundary count).toAir tr pub 3 false message=0 := by
  simp only [busCount,busCount.go,preparedTypedBusAir,preparedTypedBusExecTable,preparedTypedBusDataTable,Nat.add_zero]
  rw [ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.tableBusCount_eq]
  simp only [ZkFormal.Chacha.rowTraffic,List.flatMap_cons,List.flatMap_nil,preparedTypedBusFetch,
    preparedTypedBusReceive,preparedTypedBusPublish,Nat.reduceEqDiff,Bool.true_eq_false,
    and_false,false_and,ite_false,List.append_nil]
  have empty (rows : List Nat) : rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
    induction rows <;> simp_all
  rw [empty,empty]
  rfl

theorem prepared_typed_bus_public_count_record (ec cc boundary : List Expr) (count : Nat)
    (pub : List Fp) (message : List Fp)
    (positive : pubCount (preparedTypedBusAir ec cc boundary count) pub 3 false message≠0) :
    ∃ j,j<preparedTypedBusPublicSegment.count pub ∧ preparedTypedBusPublicSegment.record pub j=message := by
  unfold pubCount at positive
  obtain ⟨entry,member⟩:=List.exists_mem_of_length_pos (Nat.pos_of_ne_zero positive)
  obtain ⟨member,eq⟩:=List.mem_filter.mp member
  have eq:=of_decide_eq_true eq
  subst entry
  unfold pubMsgs at member
  obtain ⟨seg,segments,messages⟩:=List.mem_flatMap.mp member
  obtain ⟨msg,inSegment,eq⟩:=List.mem_map.mp messages
  simp only [preparedTypedBusAir,List.mem_cons,List.not_mem_nil,or_false] at segments
  rcases segments with rfl|rfl|rfl
  · cases eq
  · cases eq
  · have eq : msg=message:=congrArg Prod.snd (congrArg Prod.snd eq)
    subst msg
    obtain ⟨j,hj,eq⟩:=List.mem_map.mp inSegment
    exact ⟨j,List.mem_range.mp hj,eq⟩

/-- Every active CODE descriptor is one of the exact public 37-field records. -/
theorem prepared_typed_bus_published (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr)
    (s : Nat) (hs : s<tr.height 1) (active : tr.cell 1 s 0=1) :
    ∃ j,j<preparedTypedBusPublicSegment.count pub ∧
      preparedTypedBusPublicSegment.record pub j=preparedTypedBusReceive.msgVal tr 1 s pub := by
  let air:=preparedTypedBusAir ec cc boundary count
  let message:=preparedTypedBusReceive.msgVal tr 1 s pub
  have mult : preparedTypedBusPublish.multNat tr 1 s pub≠0 := by
    simp only [Interaction.multNat,Interaction.multNat.go,preparedTypedBusPublish,Expr.eval,
      Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,active,ite_true,Nat.pow_zero,Nat.add_zero]
    decide
  have tablePositive:=ZkFormal.Chacha.tableBusCount_pos hs
    (show preparedTypedBusPublish∈(preparedTypedBusDataTable cc).interactions by simp [preparedTypedBusDataTable]) mult
  have ge:=ZkFormal.Chacha.busCount_go_ge tr pub 3 true message air.tables 0 1 (by change 1<2;decide)
  have nonzero : busCount air.toAir tr pub 3 true message≠0 := by
    change tableBusCount (preparedTypedBusDataTable cc).interactions tr 1 pub 3 true message≤_ at ge
    change tableBusCount (preparedTypedBusDataTable cc).interactions tr 1 pub 3 true message≠0 at tablePositive
    unfold busCount
    omega
  have sendZero : pubCount air pub 3 true message=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member _
    simp only [air,preparedTypedBusAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> decide
  have balance:=holds.balance 3 message
  rw [sendZero,prepared_typed_bus_no_public_table_receives,Nat.add_zero,Nat.zero_add] at balance
  apply prepared_typed_bus_public_count_record ec cc boundary count pub message
  rw [←balance]
  exact nonzero

theorem prepared_typed_bus_table_local (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr) :
    TableLocal (preparedTypedBusDataTable cc) tr 1 pub := by
  have ht : 1<(preparedTypedBusAir ec cc boundary count).tables.length := by change 1<2;decide
  exact ⟨(holds.logBound 1 ht).1,(holds.logBound 1 ht).2,holds.constr 1 ht,holds.bits 1 ht⟩

/-- Authenticated fetch composition, including natural lookup multiplicities.
CODE uniqueness is derived from source constraints, not public-record assumptions. -/
theorem prepared_typed_bus_fetch_authenticated (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedTypedBusDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (r : Nat) (hr : r<tr.height 0) :
    ∃ s j,s<tr.height 1 ∧ tr.cell 1 s 0=1 ∧ preparedCodePC (tr.cell 1 s)=s ∧
      j<preparedTypedBusPublicSegment.count pub ∧
      preparedTypedBusReceive.msgVal tr 1 s pub=preparedTypedBusFetch.msgVal tr 0 r pub ∧
      preparedTypedBusPublicSegment.record pub j=preparedTypedBusFetch.msgVal tr 0 r pub := by
  have localH:=prepared_typed_bus_table_local ec cc boundary count tr pub holds
  obtain ⟨s,hs,message,mult⟩:=prepared_typed_bus_fetch_matched ec cc boundary count tr pub holds r hr
  have active:=prepared_typed_bus_receive_active (preparedTypedBusDataTable cc) tr 1 pub source localH inactive s hs mult
  have index:=prepared_code_pc_index (preparedTypedBusDataTable cc) tr 1 pub source localH s hs active
  obtain ⟨j,hj,published⟩:=prepared_typed_bus_published ec cc boundary count tr pub holds s hs active
  exact ⟨s,j,hs,active,index,hj,message,published.trans message⟩

theorem prepared_typed_bus_message_pc (tr : Trace Fp) (pub : List Fp) (r s : Nat)
    (message : preparedTypedBusReceive.msgVal tr 1 s pub=preparedTypedBusFetch.msgVal tr 0 r pub) :
    preparedCodePC (tr.cell 1 s)=preparedCodeExecPC (tr.cell 0 r) := by
  have lo:=congrArg (fun xs:List Fp=>xs.getD 2 0) message
  have hi:=congrArg (fun xs:List Fp=>xs.getD 3 0) message
  change (preparedCodeBits 1).eval tr 1 s pub=(preparedCodeBits 0).eval tr 0 r pub at lo
  change (preparedCodeBits 17).eval tr 1 s pub=(preparedCodeBits 16).eval tr 0 r pub at hi
  rw [prepared_code_bits_eval,prepared_code_bits_eval] at lo hi
  change preparedCodeLimb (tr.cell 1 s) 1=preparedCodeLimb (tr.cell 0 r) 0 at lo
  change preparedCodeLimb (tr.cell 1 s) 17=preparedCodeLimb (tr.cell 0 r) 16 at hi
  unfold preparedCodePC preparedCodeExecPC
  rw [lo,hi]

/-- The authenticated CODE row is the exact numeric EXEC PC; no caller-supplied
lookup equation or unique-public-record hypothesis is needed. -/
theorem prepared_typed_bus_fetch_at_pc (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedTypedBusDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<tr.height 1 ∧ tr.cell 1 pc 0=1 ∧
      preparedTypedBusReceive.msgVal tr 1 pc pub=preparedTypedBusFetch.msgVal tr 0 r pub ∧
      (∃ j,j<preparedTypedBusPublicSegment.count pub ∧
        preparedTypedBusPublicSegment.record pub j=preparedTypedBusFetch.msgVal tr 0 r pub) ∧
      (∀ s,s<tr.height 1 → tr.cell 1 s 0=1 →
        preparedTypedBusReceive.msgVal tr 1 s pub=preparedTypedBusFetch.msgVal tr 0 r pub → s=pc) := by
  obtain ⟨s,j,hs,active,index,hj,message,published⟩:=
    prepared_typed_bus_fetch_authenticated ec cc boundary count tr pub holds source inactive r hr
  have selected:=prepared_typed_bus_message_pc tr pub r s message
  have same : s=preparedCodeExecPC (tr.cell 0 r):=index.symm.trans selected
  subst s
  refine ⟨hs,active,message,⟨j,hj,published⟩,?_⟩
  intro other ho ha hm
  have exactPC:=prepared_typed_bus_message_pc tr pub r other hm
  have otherIndex:=prepared_code_pc_index (preparedTypedBusDataTable cc) tr 1 pub source
    (prepared_typed_bus_table_local ec cc boundary count tr pub holds) other ho ha
  exact otherIndex.symm.trans exactPC

/-- Exact generated control AIR equals the parametric bus interface above. -/
theorem prepared_typed_bus_literal_air (count localCount : Nat) :
    preparedTypedLiteralAir count localCount=preparedTypedBusAir
      (preparedTypedLiteralExec localCount) preparedTypedLiteralCode preparedTypedLiteralBoundary count := by
  rfl

private theorem typed_code_member (i : Nat) (hi : i<621) (e : Expr)
    (eq : preparedTypedLiteralCode[i]'hi=e) : e∈preparedTypedLiteralCode := by
  rw [←eq]
  exact List.getElem_mem hi

theorem prepared_typed_bus_literal_boolean :
    ∀ i,i<198 → preparedGasBoolean i∈preparedTypedLiteralCode := by
  have all : ∀ i:Fin 198,preparedTypedLiteralCode[i.val]'(by change _<621;omega)=preparedGasBoolean i.val := by decide
  intro i hi
  exact typed_code_member i (by omega) _ (all ⟨i,hi⟩)

theorem prepared_typed_bus_literal_order :
    PreparedCodeOrderSource (preparedTypedBusDataTable preparedTypedLiteralCode) := by
  refine ⟨prepared_typed_bus_literal_boolean,?_,?_,?_,?_⟩
  · have all : ∀ i:Fin 32,preparedTypedLiteralCode[271+2*i.val]'(by change _<621;omega)=preparedCodeFirstPC i.val := by decide
    intro i hi
    exact typed_code_member (271+2*i) (by omega) _ (all ⟨i,hi⟩)
  · exact typed_code_member 335 (by decide) _ rfl
  · exact typed_code_member 336 (by decide) _ rfl
  · exact typed_code_member 337 (by decide) _ rfl

theorem prepared_typed_bus_literal_inactive :
    ∀ i,i<25 → preparedCodeInactive (172+i)∈preparedTypedLiteralCode := by
  have all : ∀ i:Fin 25,preparedTypedLiteralCode[509+i.val]'(by change _<621;omega)=preparedCodeInactive (172+i.val) := by decide
  intro i hi
  exact typed_code_member (509+i) (by omega) _ (all ⟨i,hi⟩)

/-- Literal AIR alone authenticates every fetched 37-field descriptor, including
branch tags and prepared block destination, against an exact public record. -/
theorem prepared_typed_literal_fetch (count localCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir count localCount) pub tr) (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<tr.height 1 ∧ tr.cell 1 pc 0=1 ∧
      preparedTypedBusReceive.msgVal tr 1 pc pub=preparedTypedBusFetch.msgVal tr 0 r pub ∧
      ∃ j,j<preparedTypedBusPublicSegment.count pub ∧
        preparedTypedBusPublicSegment.record pub j=preparedTypedBusFetch.msgVal tr 0 r pub := by
  rw [prepared_typed_bus_literal_air] at holds
  have h:=prepared_typed_bus_fetch_at_pc _ _ _ count tr pub holds
    prepared_typed_bus_literal_order prepared_typed_bus_literal_inactive r hr
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

end NearCompression
