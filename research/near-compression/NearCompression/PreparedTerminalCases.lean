import NearCompression.PreparedAddTableLocal

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Structural source obligations, never local polynomial-validity premises. -/
structure PreparedTerminalSource (table : Table) where
  gasMiddle : List Expr
  gasTail : List Expr
  gasSource : table.constraints=preparedGasSourceConstraints gasMiddle gasTail
  flagMembers : ∀ e∈[preparedFailureInvariantPython,preparedDoneStepPython,preparedFailureStepPython],e∈table.constraints
  gasMembers : ∀ i,i<4 → preparedGasStepPython i∈table.constraints

theorem prepared_terminal_flags_local (row next pub : Nat → Fp)
    (active : row 25=0)
    (inv : preparedFailureInvariantPython.evalWith (preparedRowEnv row next pub 0 0)=0)
    (done : preparedDoneStepPython.evalWith (preparedRowEnv row next pub 0 0)=0)
    (failed : preparedFailureStepPython.evalWith (preparedRowEnv row next pub 0 0)=0) :
    row 26=0 ∧ next 26=row 414 ∧
      next 25=row 414+preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*
        (preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0) := by
  change row 26*((1:Fp)+ -row 25)+ -(0:Fp)=0 at inv
  change (1:Fp)*(next 25+ -(row 25+(((1:Fp)+ -row 25)*row 414+
    preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*(preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0))))=0 at done
  change (1:Fp)*(next 26+ -(row 26+((1:Fp)+ -row 25)*row 414))=0 at failed
  rw [active] at inv done failed
  grind

theorem prepared_terminal_flags_table (table : Table) (source : PreparedTerminalSource table)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0) :
    tr.cell t r 26=0 ∧ tr.cell t (r+1) 26=tr.cell t r 414 ∧
      tr.cell t (r+1) 25=tr.cell t r 414+
        preparedSuccessExpr.evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) 0 0)*
        (preparedFetchPython 3).evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) 0 0) := by
  apply prepared_terminal_flags_local _ _ _ active
  · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (source.flagMembers _ (by simp))
    simp [preparedFailureInvariantPython,preparedActiveExpr,preparedNoFirst]
  · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (source.flagMembers _ (by simp))
    simp [preparedDoneStepPython,preparedTransitionEq,preparedActiveExpr,preparedSuccessExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst]
  · apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (source.flagMembers _ (by simp))
    simp [preparedFailureStepPython,preparedTransitionEq,preparedActiveExpr,preparedNoFirst]

theorem prepared_gas_updates_table (table : Table) (source : PreparedTerminalSource table)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t) :
    ∀ i,i<4 → (preparedGasStepPython i).evalWith
      (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun j => pub.getD j 0) 0 0)=0 := by
  intro i hi
  apply prepared_table_nonlast_eval table tr t r pub localH nonlast _ (source.gasMembers i hi)
  simp [preparedGasStepPython,preparedTransitionEq,preparedTransitionBits,preparedSuccessExpr,preparedActiveExpr,preparedBalancedSum,preparedNoFirst]

theorem prepared_gas_failure_freeze (row next : Nat → Fp) (pub : List Fp)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next (fun i => pub.getD i 0) 0 0)=0)
    (updates : ∀ i,i<4 → (preparedGasStepPython i).evalWith (preparedRowEnv row next (fun i => pub.getD i 0) 0 0)=0) :
    preparedGasValue next pub=preparedGasValue row pub := by
  have limbs (i : Nat) (hi : i<4) : preparedGasLimb next pub 283 i=preparedGasLimb row pub 283 i := by
    have h:=updates i hi
    simp only [preparedGasStepPython,preparedTransitionEq,Expr.evalWith] at h
    rw [success,prepared_transition_bits_horner,prepared_transition_bits_horner,prepared_transition_bits_horner] at h
    unfold preparedGasLimb
    rw [prepared_gas_bits_horner,prepared_gas_bits_horner]
    change (1:Fp)*(_+ -((0:Fp)*_+((1:Fp)+ -0)*_))=0 at h
    grind
  simp only [preparedGasValue,preparedGasWord]
  rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]

/-- Exhaustion is derived from public canonical fees, not an assumed borrow bit.
The GAS columns encode the fast counter g; burnt/sync is outside this row projection. -/
theorem prepared_table_exhaustion (table : Table) (source : PreparedTerminalSource table)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (exhausted : preparedGasValue (tr.cell t r) pub<preparedFeeValue (tr.cell t r) pub) :
    tr.cell t r 414=1 ∧ tr.cell t r 26=0 ∧ tr.cell t (r+1) 25=1 ∧ tr.cell t (r+1) 26=1 ∧
      preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub := by
  have gas:=prepared_gas_table_local table source.gasMiddle source.gasTail source.gasSource tr t r pub localH (by omega) publicBounds
  have oneNat : (tr.cell t r 414).toNat=1 := gas.1.mpr exhausted
  have one : tr.cell t r 414=1 := by rw [←Fp.ofNat_toNat (tr.cell t r 414),oneNat];rfl
  have success : preparedSuccessExpr.evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) 0 0)=0 := by
    change ((1:Fp)+ -tr.cell t r 25)*((1:Fp)+ -tr.cell t r 414)=0
    rw [active,one];grind
  have flags:=prepared_terminal_flags_table table source tr t r pub localH nonlast active
  rw [one,success] at flags
  have nextDone : tr.cell t (r+1) 25=1 := by grind
  exact ⟨one,flags.1,nextDone,flags.2.1,
    prepared_gas_failure_freeze _ _ pub success (prepared_gas_updates_table table source tr t r pub localH nonlast)⟩


theorem prepared_quiet_projection (row next pub : Nat → Fp)
    (choices : preparedRowChoices row next pub 0 0) (nextChoices : preparedRowChoices next next pub 0 0)
    (holds : PreparedAddTransitionHolds row next pub)
    (advance : preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)=0)
    (quiet : ∀ i,i<3 → preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*
      (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=0) :
    (∀ i,i<16 → next i=row i) ∧ (∀ i,i<9 → next (16+i)=row (16+i)) ∧
      (∀ slot,slot<8 → preparedStackWord next slot=preparedStackWord row slot) := by
  have q0:=quiet 0 (by decide);have q1:=quiet 1 (by decide);have q2:=quiet 2 (by decide)
  have pc : ∀ i,i<16 → next i=row i := by
    intro i hi
    have h:=holds (preparedPCStepPython i) (by
      apply List.mem_append_left;apply List.mem_append_left
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
    simp only [preparedPCStepPython,preparedTransitionEq,Expr.evalWith] at h
    rw [advance] at h
    change (1:Fp)*(next i+ -(((1:Fp)+ -0)*row i+0*_))=0 at h
    grind
  obtain ⟨_,⟨sp,hsp,hspc⟩⟩:=prepared_row_pc_sp row next pub 0 0 choices
  obtain ⟨_,⟨nsp,hnsp,hnspc⟩⟩:=prepared_row_pc_sp next next pub 0 0 nextChoices
  have hs:=holds preparedSPStepPython (by simp [preparedAddTransitionConstraints])
  simp only [preparedSPStepPython,preparedTransitionEq,Expr.evalWith] at hs
  rw [prepared_sp_index_selected row next pub true nsp hnsp hnspc,
    prepared_sp_index_selected row next pub false sp hsp hspc] at hs
  have eq : Fp.ofNat nsp=Fp.ofNat sp := by
    change (1:Fp)*(Fp.ofNat nsp+ -(Fp.ofNat sp+
      preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*
      ((preparedFetchPython 0).evalWith (preparedRowEnv row next pub 0 0)+
        -((preparedFetchPython 1).evalWith (preparedRowEnv row next pub 0 0)+
          (preparedFetchPython 2).evalWith (preparedRowEnv row next pub 0 0)))))=0 at hs
    grind
  have spEq : nsp=sp := by
    have h:=congrArg Fp.toNat eq
    rw [Fp.toNat_ofNat,Fp.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (show nsp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
      Nat.mod_eq_of_lt (show sp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)] at h
    exact h
  have limbEq (slot limb : Nat) (hslot : slot<8) (hl : limb<2) :
      preparedTransitionStackLimb next slot limb=preparedTransitionStackLimb row slot limb := by
    have h:=holds (preparedStackStepPython slot limb) (by
      apply List.mem_append_right;apply List.mem_flatMap.mpr
      exact ⟨slot,List.mem_range.mpr hslot,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩)
    simp only [preparedStackStepPython,preparedTransitionEq,Expr.evalWith] at h
    rw [prepared_transition_bits_horner,prepared_transition_bits_horner,prepared_transition_bits_horner] at h
    simp only [preparedRowEnv,←Fp.ofNat_def] at h q0 q1 q2
    unfold preparedTransitionStackLimb
    grind
  refine ⟨pc,?_,?_⟩
  · intro i hi
    rw [hspc i hi,hnspc i hi,spEq]
  · intro slot hslot
    rw [prepared_stack_word_limbs,prepared_stack_word_limbs,limbEq slot 0 hslot (by decide),limbEq slot 1 hslot (by decide)]

/-- Exact source end requires an empty live stack before successful return. -/
def preparedEndDepthPython : Expr :=
  .add (.mul preparedSuccessExpr (.mul (preparedFetchPython 3) (.add (.const 1) (.neg (.col 16 false))))) (.neg (.const 0))

theorem prepared_table_exhaustion_projection (table : Table) (source : PreparedTerminalSource table)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (exhausted : preparedGasValue (tr.cell t r) pub<preparedFeeValue (tr.cell t r) pub) :
    tr.cell t (r+1) 25=1 ∧ tr.cell t (r+1) 26=1 ∧
      preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub ∧
      (∀ i,i<16 → tr.cell t (r+1) i=tr.cell t r i) ∧
      (∀ i,i<9 → tr.cell t (r+1) (16+i)=tr.cell t r (16+i)) ∧
      (∀ slot,slot<8 → preparedStackWord (tr.cell t (r+1)) slot=preparedStackWord (tr.cell t r) slot) := by
  have result:=prepared_table_exhaustion table source tr t r pub localH nonlast active publicBounds exhausted
  have success : preparedSuccessExpr.evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) 0 0)=0 := by
    change ((1:Fp)+ -tr.cell t r 25)*((1:Fp)+ -tr.cell t r 414)=0
    rw [result.1];grind
  have freeze:=prepared_quiet_projection (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0)
    (prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource tr t r pub localH (by omega) _)
    (prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource tr t (r+1) pub localH nonlast _)
    (prepared_table_add_transitions table prefixPart middle dead transitionSource tr t r pub localH nonlast)
    (by change preparedSuccessExpr.evalWith _ * _=0;rw [success];grind)
    (by intro i hi;rw [success];grind)
  exact ⟨result.2.2.1,result.2.2.2.1,result.2.2.2.2,freeze.1,freeze.2.1,freeze.2.2⟩


theorem prepared_table_end (table : Table) (source : PreparedTerminalSource table)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (endMember : preparedEndDepthPython∈table.constraints)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicEnd : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 → pub.getD (56+10*pc+tag) 0=if tag=3 then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub) :
    tr.cell t r 16=1 ∧ tr.cell t (r+1) 25=1 ∧ tr.cell t (r+1) 26=0 ∧
      preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub-preparedFeeValue (tr.cell t r) pub ∧
      (∀ i,i<16 → tr.cell t (r+1) i=tr.cell t r i) ∧
      (∀ i,i<9 → tr.cell t (r+1) (16+i)=tr.cell t r (16+i)) ∧
      (∀ slot,slot<8 → preparedStackWord (tr.cell t (r+1)) slot=preparedStackWord (tr.cell t r) slot) := by
  let row:=tr.cell t r
  let next:=tr.cell t (r+1)
  let pf:=fun i => pub.getD i 0
  change row 25=0 at active
  have choices : preparedRowChoices row next pf 0 0:=
    prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource tr t r pub localH (by omega) next
  have nextChoices : preparedRowChoices next next pf 0 0:=
    prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource tr t (r+1) pub localH nonlast next
  have extracted:=prepared_gas_extract_source source.gasMiddle source.gasTail row
    (tr.cell t ((r+1)%tr.height t)) pub (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0) (by
      intro e he
      have h:=localH.constr r (by omega) e (by rw [source.gasSource];exact he)
      rw [Expr.eval,prepared_gas_row_env] at h
      exact h)
  have feeBounds:=prepared_gas_public_fee_bounds row next pub 0 0 choices publicBounds
  have gas:=prepared_gas_borrow_sound row pub extracted.1 feeBounds
  have zeroNat : (row 414).toNat=0:=gas.2.1.mpr enoughGas
  have zero : row 414=0 := by rw [←Fp.ofNat_toNat (row 414),zeroNat];rfl
  obtain ⟨⟨pc,hpc,hp⟩,_⟩:=prepared_row_pc_sp row next pf 0 0 choices
  have selected : row pc=1 := by simpa only [ite_true] using hp pc hpc
  have op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pf 0 0)=if i=3 then 1 else 0 := by
    intro i hi
    exact prepared_opcode_selected row next pf 0 0 pc 3 hpc hp (publicEnd pc hpc selected) i hi
  have success : preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)=1 := by
    change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)=1
    rw [active,zero];grind
  have endOne : (preparedFetchPython 3).evalWith (preparedRowEnv row next pf 0 0)=1 := by simpa using op 3 (by decide)
  have depth:=prepared_table_nonlast_eval table tr t r pub localH nonlast _ endMember (by
    simp [preparedEndDepthPython,preparedSuccessExpr,preparedActiveExpr,preparedFetchPython,preparedBalancedSum,preparedNoFirst])
  change preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)*
    ((preparedFetchPython 3).evalWith (preparedRowEnv row next pf 0 0)*((1:Fp)+ -row 16))+ -(0:Fp)=0 at depth
  rw [success,endOne] at depth
  have spZero : row 16=1 := by grind
  have flags:=prepared_terminal_flags_table table source tr t r pub localH nonlast active
  change row 26=0 ∧ next 26=row 414 ∧ next 25=row 414+
    preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)*(preparedFetchPython 3).evalWith (preparedRowEnv row next pf 0 0) at flags
  rw [zero,success,endOne] at flags
  have nextDone : next 25=1 := by grind
  have quiet : ∀ i,i<3 → preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)*
      (preparedFetchPython i).evalWith (preparedRowEnv row next pf 0 0)=0 := by
    intro i hi
    rw [success,op i (by omega)]
    have ne : i≠3 := by omega
    simp only [ne,ite_false]
    grind
  have freeze:=prepared_quiet_projection row next pf choices nextChoices
    (prepared_table_add_transitions table prefixPart middle dead transitionSource tr t r pub localH nonlast)
    (by change preparedSuccessExpr.evalWith _*((1:Fp)+ -(preparedFetchPython 3).evalWith _)=0;rw [success,endOne];grind) quiet
  exact ⟨spZero,nextDone,flags.2.1,prepared_next_gas_success row next pub extracted.1 feeBounds success zero
    (prepared_gas_updates_table table source tr t r pub localH nonlast),freeze.1,freeze.2.1,freeze.2.2⟩

end NearCompression
