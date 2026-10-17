import NearCompression.PreparedTerminalCases

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

def preparedImmediateWord (row next pub : Nat → Fp) : Nat :=
  ((preparedFetchPython 4).evalWith (preparedRowEnv row next pub 0 0)).toNat+
    65536*((preparedFetchPython 5).evalWith (preparedRowEnv row next pub 0 0)).toNat

theorem prepared_stack_pointer_next (push : Bool) (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=(if push then 0 else 2) then 1 else 0)
    (sp nsp : Nat) (hs : sp<9) (hn : nsp<9)
    (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (following : ∀ i,i<9 → next (16+i)=if i=nsp then 1 else 0) :
    nsp+(if push then 0 else 1)=sp+(if push then 1 else 0) := by
  have h:=holds preparedSPStepPython (by simp [preparedAddTransitionConstraints])
  have h0:=op 0 (by decide);have h1:=op 1 (by decide);have h2:=op 2 (by decide)
  simp only [preparedSPStepPython,preparedTransitionEq,Expr.evalWith] at h
  rw [prepared_sp_index_selected row next pub true nsp hn following,
    prepared_sp_index_selected row next pub false sp hs current,success,h0,h1,h2] at h
  have eq : Fp.ofNat nsp+Fp.ofNat (if push then 0 else 1)=Fp.ofNat sp+Fp.ofNat (if push then 1 else 0) := by
    cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,preparedRowEnv,←Fp.ofNat_def] at h ⊢ <;> grind
  have natEq:=congrArg Fp.toNat eq
  change (Fp.add (Fp.ofNat nsp) (Fp.ofNat (if push then 0 else 1))).toNat=
    (Fp.add (Fp.ofNat sp) (Fp.ofNat (if push then 1 else 0))).toNat at natEq
  rw [Fp.toNat_add,Fp.toNat_add,Fp.toNat_ofNat,Fp.toNat_ofNat,Fp.toNat_ofNat,Fp.toNat_ofNat] at natEq
  have sn : sp<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  have nn : nsp<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt sn,Nat.mod_eq_of_lt nn,
    Nat.mod_eq_of_lt (show 0<ZkFormal.Algebra.P by decide),Nat.mod_eq_of_lt (show 1<ZkFormal.Algebra.P by decide),Nat.add_zero] at natEq ⊢
  · rw [Nat.mod_eq_of_lt (show nsp+1<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)] at natEq
    exact natEq
  · rw [Nat.mod_eq_of_lt (show sp+1<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)] at natEq
    exact natEq

theorem prepared_stack_case_limb_next (push : Bool) (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=(if push then 0 else 2) then 1 else 0)
    (sp : Nat) (hs : sp<9) (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (slot limb : Nat) (hslot : slot<8) (hl : limb<2) :
    preparedTransitionStackLimb next slot limb=
      if push then (if slot=sp then (preparedFetchPython (4+limb)).evalWith (preparedRowEnv row next pub 0 0)
        else preparedTransitionStackLimb row slot limb)
      else (if slot+1=sp then 0 else preparedTransitionStackLimb row slot limb) := by
  have h:=holds (preparedStackStepPython slot limb) (by
    apply List.mem_append_right;apply List.mem_flatMap.mpr
    exact ⟨slot,List.mem_range.mpr hslot,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩)
  have h0:=op 0 (by decide);have h1:=op 1 (by decide);have h2:=op 2 (by decide)
  simp only [preparedStackStepPython,preparedTransitionEq,Expr.evalWith] at h
  rw [success,h0,h1,h2,prepared_transition_bits_horner,prepared_transition_bits_horner,prepared_transition_bits_horner] at h
  have pslot:=current slot (by omega)
  have pnext:=current (slot+1) (by omega)
  simp only [←Nat.add_assoc] at pnext
  simp only [preparedRowEnv,←Fp.ofNat_def] at h ⊢
  rw [pslot,pnext] at h
  unfold preparedTransitionStackLimb
  cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff] at h ⊢
  · by_cases eq:slot+1=sp <;> simp only [eq,ite_true,ite_false] at h ⊢ <;> grind
  · by_cases eq:slot=sp <;> simp only [eq,ite_true,ite_false] at h ⊢ <;> grind


theorem prepared_stack_case_word_next (push : Bool) (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=(if push then 0 else 2) then 1 else 0)
    (sp : Nat) (hs : sp<9) (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (slot : Nat) (hslot : slot<8) :
    preparedStackWord next slot=if push then (if slot=sp then preparedImmediateWord row next pub else preparedStackWord row slot)
      else (if slot+1=sp then 0 else preparedStackWord row slot) := by
  have h0:=prepared_stack_case_limb_next push row next pub holds success op sp hs current slot 0 hslot (by decide)
  have h1:=prepared_stack_case_limb_next push row next pub holds success op sp hs current slot 1 hslot (by decide)
  rw [prepared_stack_word_limbs,h0,h1]
  cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · by_cases eq:slot+1=sp
    · simp only [eq,ite_true];rfl
    · simp only [eq,ite_false];exact (prepared_stack_word_limbs row slot).symm
  · by_cases eq:slot=sp
    · simp only [eq,ite_true];rfl
    · simp only [eq,ite_false];exact (prepared_stack_word_limbs row slot).symm

def PreparedStackProjection (push : Bool) (row next pub : Nat → Fp) : Prop :=
  ∃ pc sp,pc<15 ∧ sp<9 ∧ (if push then sp<8 else 1≤sp) ∧
    (∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
    (∀ i,i<16 → next i=if i=pc+1 then 1 else 0) ∧
    (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
    (∀ i,i<9 → next (16+i)=if i=(if push then sp+1 else sp-1) then 1 else 0) ∧
    (∀ slot,slot<8 → preparedStackWord next slot=
      if push then (if slot=sp then preparedImmediateWord row next pub else preparedStackWord row slot)
      else (if slot+1=sp then 0 else preparedStackWord row slot))

theorem prepared_stack_case_projection (push : Bool) (row next pub : Nat → Fp)
    (choices : preparedRowChoices row next pub 0 0) (nextChoices : preparedRowChoices next next pub 0 0)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=(if push then 0 else 2) then 1 else 0) :
    PreparedStackProjection push row next pub := by
  obtain ⟨⟨pc,hpc,hp⟩,⟨sp,hsp,hs⟩⟩:=prepared_row_pc_sp row next pub 0 0 choices
  obtain ⟨⟨npc,hnpc,hnp⟩,⟨nsp,hnsp,hns⟩⟩:=prepared_row_pc_sp next next pub 0 0 nextChoices
  have endZero : (preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0)=0 := by
    have h:=op 3 (by decide)
    cases push <;> simpa using h
  have advance : preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)=1 := by
    change preparedSuccessExpr.evalWith _*((1:Fp)+ -(preparedFetchPython 3).evalWith _)=1
    rw [success,endZero];grind
  have pn:=prepared_add_pc_next row next pub holds advance pc npc hpc hnpc hp hnp
  have sn:=prepared_stack_pointer_next push row next pub holds success op sp nsp hsp hnsp hs hns
  have index : nsp=(if push then sp+1 else sp-1) := by
    cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at sn ⊢ <;> omega
  have bound : if push then sp<8 else 1≤sp := by
    cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at sn ⊢ <;> omega
  rw [pn] at hnp
  rw [index] at hns
  exact ⟨pc,sp,by omega,hsp,bound,hp,hnp,hs,hns,
    fun slot hslot => prepared_stack_case_word_next push row next pub holds success op sp hsp hs slot hslot⟩

theorem prepared_table_const_drop (push : Bool) (table : Table) (source : PreparedTerminalSource table)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicImmediates : ∀ pc,pc<16 → ∀ limb,limb<2 → (pub.getD (56+10*pc+(4+limb)) 0).toNat<65536)
    (publicOp : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
      pub.getD (56+10*pc+tag) 0=if tag=(if push then 0 else 2) then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub) :
    tr.cell t r 26=0 ∧ tr.cell t (r+1) 25=0 ∧ tr.cell t (r+1) 26=0 ∧
      preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub-preparedFeeValue (tr.cell t r) pub ∧
      preparedImmediateWord (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0)<4294967296 ∧
      PreparedStackProjection push (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0) := by
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
  have op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pf 0 0)=if i=(if push then 0 else 2) then 1 else 0 := by
    intro i hi
    exact prepared_opcode_selected row next pf 0 0 pc (if push then 0 else 2) hpc hp (publicOp pc hpc selected) i hi
  have success : preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)=1 := by
    change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)=1
    rw [active,zero];grind
  have endZero : (preparedFetchPython 3).evalWith (preparedRowEnv row next pf 0 0)=0 := by
    have h:=op 3 (by decide)
    cases push <;> simpa using h
  have flags:=prepared_terminal_flags_table table source tr t r pub localH nonlast active
  change row 26=0 ∧ next 26=row 414 ∧ next 25=row 414+
    preparedSuccessExpr.evalWith (preparedRowEnv row next pf 0 0)*(preparedFetchPython 3).evalWith (preparedRowEnv row next pf 0 0) at flags
  rw [zero,success,endZero] at flags
  have nextDone : next 25=0 := by grind
  have immediate (i : Nat) (hi : i<2) :
      ((preparedFetchPython (4+i)).evalWith (preparedRowEnv row next pf 0 0)).toNat<65536 := by
    rw [prepared_fetch_python_eval,prepared_fetch_selected row next pf 0 0 pc hpc hp]
    exact publicImmediates pc hpc i hi
  have bound : preparedImmediateWord row next pf<4294967296 := by
    have h0:=immediate 0 (by decide);have h1:=immediate 1 (by decide)
    change ((preparedFetchPython 4).evalWith (preparedRowEnv row next pf 0 0)).toNat<65536 at h0
    change ((preparedFetchPython 5).evalWith (preparedRowEnv row next pf 0 0)).toNat<65536 at h1
    unfold preparedImmediateWord
    omega
  exact ⟨flags.1,nextDone,flags.2.1,
    prepared_next_gas_success row next pub extracted.1 feeBounds success zero (prepared_gas_updates_table table source tr t r pub localH nonlast),bound,
    prepared_stack_case_projection push row next pf choices nextChoices
      (prepared_table_add_transitions table prefixPart middle dead transitionSource tr t r pub localH nonlast) success op⟩

end NearCompression
