import NearCompression.PreparedOperandBridge

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

def preparedActiveExpr : Expr := .add (.const 1) (.neg (.col 25 false))
def preparedSuccessExpr : Expr := .mul preparedActiveExpr (.add (.const 1) (.neg (.col 414 false)))
def preparedAdvanceExpr : Expr := .mul preparedSuccessExpr (.add (.const 1) (.neg (preparedFetchPython 3)))
def preparedTransitionEq (a b : Expr) : Expr := .mul .isTransition (.add a (.neg b))
def preparedPCStepPython (i : Nat) : Expr :=
  preparedTransitionEq (.col i true)
    (.add (.mul (.add (.const 1) (.neg preparedAdvanceExpr)) (.col i false))
      (.mul preparedAdvanceExpr (if i=0 then .const 0 else .col (i-1) false)))
def preparedPCOverflowPython : Expr :=
  .add (.mul preparedAdvanceExpr (.col 15 false)) (.neg (.const 0))
def preparedSPIndexPython (next : Bool) : Expr :=
  let term := fun i => .mul (.const i) (.col (16+i) next)
  .add (preparedBalancedSum term 3 0) (term 8)
def preparedSPStepPython : Expr :=
  preparedTransitionEq (preparedSPIndexPython true)
    (.add (preparedSPIndexPython false)
      (.mul preparedSuccessExpr (.add (preparedFetchPython 0)
        (.neg (.add (preparedFetchPython 1) (preparedFetchPython 2))))))
def preparedTransitionBits (base : Nat) (next : Bool) : Expr :=
  preparedBalancedSum (fun i => .mul (.const (2^i)) (.col (base+i) next)) 4 0
def preparedStackStepPython (slot limb : Nat) : Expr :=
  let old := preparedTransitionBits (27+32*slot+16*limb) false
  let push := .mul preparedSuccessExpr (.mul (preparedFetchPython 0) (.col (16+slot) false))
  let write := .mul preparedSuccessExpr (.mul (preparedFetchPython 1)
    (if slot+2≤8 then .col (16+slot+2) false else .const 0))
  let clear := .mul preparedSuccessExpr (.mul (.add (preparedFetchPython 1) (preparedFetchPython 2))
    (.col (16+slot+1) false))
  preparedTransitionEq (preparedTransitionBits (27+32*slot+16*limb) true)
    (.add (.mul (.add (.const 1) (.neg (.add (.add push write) clear))) old)
      (.add (.mul push (preparedFetchPython (4+limb)))
        (.mul write (preparedTransitionBits (415+16*limb) false))))

/-- Exact source indices 463..480 and 492,494,..522. -/
def preparedAddTransitionConstraints : List Expr :=
  (List.range 16).map preparedPCStepPython ++ [preparedPCOverflowPython,preparedSPStepPython] ++
    (List.range 8).flatMap (fun slot => (List.range 2).map (preparedStackStepPython slot))
def PreparedAddTransitionHolds (row next pub : Nat → Fp) : Prop :=
  ∀ e∈preparedAddTransitionConstraints,e.evalWith (preparedRowEnv row next pub 0 0)=0

theorem prepared_transition_bits_horner (row next pub : Nat → Fp) (base : Nat) (n : Bool) :
    (preparedTransitionBits base n).evalWith (preparedRowEnv row next pub 0 0)=
    (instructionBitExpr base 16).evalWith (instructionAddEnv (if n then next else row)) := by
  cases n <;>
    simp only [preparedTransitionBits,preparedBalancedSum,instructionBitExpr,Expr.evalWith,
      preparedRowEnv,instructionAddEnv,Nat.reduceAdd,Nat.reducePow,Nat.add_zero,Nat.add_assoc]
  all_goals simp only [←Fp.ofNat_def];grind

theorem prepared_sp_index_selected (row next pub : Nat → Fp) (n : Bool) (sp : Nat) (hs : sp<9)
    (onehot : ∀ i,i<9 → (if n then next else row) (16+i)=if i=sp then 1 else 0) :
    (preparedSPIndexPython n).evalWith (preparedRowEnv row next pub 0 0)=Fp.ofNat sp := by
  have chosen := prepared_sum_select 9 sp (fun i => (if n then next else row) (16+i)) Fp.ofNat hs onehot
  simp only [preparedSPIndexPython,preparedBalancedSum,Expr.evalWith,preparedRowEnv,Nat.reduceAdd,Nat.reducePow]
  simp only [preparedFieldSum,Nat.reduceAdd] at chosen
  cases n <;> simp only [Bool.false_eq_true,ite_false,ite_true] at chosen ⊢ <;>
    simp only [←Fp.ofNat_def] at chosen ⊢ <;> grind

theorem prepared_success_advance (row next pub : Nat → Fp)
    (active : row 25=0) (noBorrow : row 414=0)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=1 then 1 else 0) :
    preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1 ∧
    preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)=1 := by
  have endZero:=op 3 (by decide)
  change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)=1 ∧
    (((1:Fp)+ -row 25)*((1:Fp)+ -row 414))*((1:Fp)+ -(preparedFetchPython 3).evalWith (preparedRowEnv row next pub 0 0))=1
  rw [active,noBorrow,endZero]
  simp only [Nat.reduceEqDiff,ite_false]
  grind

theorem prepared_add_pc_next (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub) (advance : preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (pc npc : Nat) (hp : pc<16) (hn : npc<16)
    (current : ∀ i,i<16 → row i=if i=pc then 1 else 0)
    (following : ∀ i,i<16 → next i=if i=npc then 1 else 0) : npc=pc+1 := by
  have overflow:=holds preparedPCOverflowPython (by simp [preparedAddTransitionConstraints])
  change preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)*row 15+ -(0:Fp)=0 at overflow
  rw [advance,current 15 (by decide)] at overflow
  have bound : pc<15 := by
    by_cases h:pc=15
    · subst pc;simp only [ite_true] at overflow;grind
    · omega
  have h:=holds (preparedPCStepPython (pc+1)) (by
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨pc+1,List.mem_range.mpr (by omega),rfl⟩)
  change (1:Fp)*(next (pc+1)+ -(((1:Fp)+ -preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0))*row (pc+1)+
    preparedAdvanceExpr.evalWith (preparedRowEnv row next pub 0 0)*(if pc+1=0 then (.const 0:Expr) else .col (pc+1-1) false).evalWith (preparedRowEnv row next pub 0 0)))=0 at h
  rw [advance] at h
  simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,Expr.evalWith,preparedRowEnv] at h
  rw [current pc hp,following (pc+1) (by omega)] at h
  by_cases eq:pc+1=npc
  · omega
  · simp only [eq,ite_false,ite_true] at h;grind


theorem prepared_add_sp_next (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=1 then 1 else 0)
    (sp nsp : Nat) (hs : sp<9) (hn : nsp<9)
    (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (following : ∀ i,i<9 → next (16+i)=if i=nsp then 1 else 0) : nsp+1=sp := by
  have h:=holds preparedSPStepPython (by simp [preparedAddTransitionConstraints])
  have h0:=op 0 (by decide);have h1:=op 1 (by decide);have h2:=op 2 (by decide)
  change (1:Fp)*((preparedSPIndexPython true).evalWith (preparedRowEnv row next pub 0 0)+
    -((preparedSPIndexPython false).evalWith (preparedRowEnv row next pub 0 0)+
      preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)*
        ((preparedFetchPython 0).evalWith (preparedRowEnv row next pub 0 0)+
          -((preparedFetchPython 1).evalWith (preparedRowEnv row next pub 0 0)+
            (preparedFetchPython 2).evalWith (preparedRowEnv row next pub 0 0)))))=0 at h
  rw [prepared_sp_index_selected row next pub true nsp hn following,
    prepared_sp_index_selected row next pub false sp hs current,success,h0,h1,h2] at h
  simp only [Nat.reduceEqDiff,ite_true,ite_false] at h
  have eq : Fp.ofNat nsp+1=Fp.ofNat sp := by grind
  have natEq := congrArg Fp.toNat eq
  change (Fp.add (Fp.ofNat nsp) (Fp.ofNat 1)).toNat=(Fp.ofNat sp).toNat at natEq
  rw [Fp.toNat_add,Fp.toNat_ofNat,Fp.toNat_ofNat,Fp.toNat_ofNat] at natEq
  have nbound : nsp<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  have sbound : sp<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  have bound : nsp+1<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  simpa only [Nat.mod_eq_of_lt (show 1<ZkFormal.Algebra.P by decide),Nat.mod_eq_of_lt nbound,Nat.mod_eq_of_lt sbound,Nat.mod_eq_of_lt bound] using natEq

def preparedTransitionStackLimb (row : Nat → Fp) (slot limb : Nat) : Fp :=
  (instructionBitExpr (27+32*slot+16*limb) 16).evalWith (instructionAddEnv row)
def preparedTransitionResultLimb (row : Nat → Fp) (limb : Nat) : Fp :=
  (instructionBitExpr (415+16*limb) 16).evalWith (instructionAddEnv row)

theorem prepared_add_stack_limb_next (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=1 then 1 else 0)
    (sp : Nat) (hs : sp<9) (enough : 2≤sp)
    (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (slot limb : Nat) (hslot : slot<8) (hl : limb<2) :
    preparedTransitionStackLimb next slot limb =
      if slot=sp-2 then preparedTransitionResultLimb row limb
      else if slot=sp-1 then 0 else preparedTransitionStackLimb row slot limb := by
  have h:=holds (preparedStackStepPython slot limb) (by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨slot,List.mem_range.mpr hslot,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩)
  have h0:=op 0 (by decide);have h1:=op 1 (by decide);have h2:=op 2 (by decide)
  simp only [preparedStackStepPython,preparedTransitionEq,Expr.evalWith] at h
  rw [success,h0,h1,h2] at h
  rw [prepared_transition_bits_horner,prepared_transition_bits_horner,prepared_transition_bits_horner] at h
  have clear : row (16+slot+1)=if slot=sp-1 then 1 else 0 := by
    rw [Nat.add_assoc,current (slot+1) (by omega)]
    have eq : slot+1=sp ↔ slot=sp-1 := by omega
    simp only [eq]
  have write : (if slot+2≤8 then (.col (16+slot+2) false : Expr) else .const 0).evalWith
      (preparedRowEnv row next pub 0 0)=if slot=sp-2 then 1 else 0 := by
    by_cases bound:slot+2≤8
    · rw [if_pos bound]
      change row (16+slot+2)=_
      rw [Nat.add_assoc,current (slot+2) (by omega)]
      have eq : slot+2=sp ↔ slot=sp-2 := by omega
      simp only [eq]
    · rw [if_neg bound]
      have ne : slot≠sp-2 := by omega
      simp only [ne,ite_false]
      rfl
  rw [write] at h
  change (1:Fp)*(preparedTransitionStackLimb next slot limb+
    -(((1:Fp)+ -(((1:Fp)*((if (0:Nat)=1 then 1 else 0)*row (16+slot))+
      (1:Fp)*((if (1:Nat)=1 then 1 else 0)*(if slot=sp-2 then 1 else 0)))+
      (1:Fp)*(((if (1:Nat)=1 then 1 else 0)+(if (2:Nat)=1 then 1 else 0))*row (16+slot+1))))*
        preparedTransitionStackLimb row slot limb+
      ((1:Fp)*((if (0:Nat)=1 then 1 else 0)*row (16+slot))*(preparedFetchPython (4+limb)).evalWith (preparedRowEnv row next pub 0 0)+
        (1:Fp)*((if (1:Nat)=1 then 1 else 0)*(if slot=sp-2 then 1 else 0))*preparedTransitionResultLimb row limb)))=0 at h
  rw [clear] at h
  simp only [Nat.reduceEqDiff,ite_true,ite_false] at h
  by_cases a:slot=sp-2
  · have b:slot≠sp-1 := by omega
    simp only [a,b,ite_true,ite_false] at h ⊢
    grind
  · by_cases b:slot=sp-1
    · simp only [a,b,ite_true,ite_false] at h ⊢;grind
    · simp only [a,b,ite_true,ite_false] at h ⊢;grind


theorem prepared_stack_word_limbs (row : Nat → Fp) (slot : Nat) :
    preparedStackWord row slot=(preparedTransitionStackLimb row slot 0).toNat+
      65536*(preparedTransitionStackLimb row slot 1).toNat := by
  simp only [preparedStackWord,preparedTransitionStackLimb,Nat.mul_zero,Nat.add_zero,Nat.mul_one]

theorem prepared_add_result_limbs (row : Nat → Fp) :
    preparedAddResultWord row=(preparedTransitionResultLimb row 0).toNat+
      65536*(preparedTransitionResultLimb row 1).toNat := by
  simp only [preparedAddResultWord,preparedTransitionResultLimb,Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceAdd]

theorem prepared_add_stack_word_next (row next pub : Nat → Fp)
    (holds : PreparedAddTransitionHolds row next pub)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next pub 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=1 then 1 else 0)
    (sp : Nat) (hs : sp<9) (enough : 2≤sp)
    (current : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) (slot : Nat) (hslot : slot<8) :
    preparedStackWord next slot=if slot=sp-2 then preparedAddResultWord row
      else if slot=sp-1 then 0 else preparedStackWord row slot := by
  have h0:=prepared_add_stack_limb_next row next pub holds success op sp hs enough current slot 0 hslot (by decide)
  have h1:=prepared_add_stack_limb_next row next pub holds success op sp hs enough current slot 1 hslot (by decide)
  rw [prepared_stack_word_limbs,h0,h1]
  by_cases a:slot=sp-2
  · simp only [a,ite_true]
    exact (prepared_add_result_limbs row).symm
  · by_cases b:slot=sp-1
    · have ne : sp-1≠sp-2 := by omega
      simp only [a,b,ne,ite_false,ite_true];rfl
    · simp only [a,b,ite_false]
      exact (prepared_stack_word_limbs row slot).symm

/-- Successful add transition: actual integer PC/SP progression, both operands,
 wrapping result, written result, cleared popped slot, all other slots unchanged.
 No claim yet about frames, entry/exit/PREP, or full-machine state equality. -/
theorem prepared_add_transition_sound (row next pub : Nat → Fp)
    (choices : preparedRowChoices row next pub 0 0)
    (nextChoices : preparedRowChoices next next pub 0 0)
    (holds : PreparedAddTransitionHolds row next pub)
    (active : row 25=0) (noBorrow : row 414=0)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next pub 0 0)=if i=1 then 1 else 0)
    (depth : preparedAddDepthResidual.evalWith (preparedRowEnv row next pub 0 0)=0)
    (carries : ∀ i,i<2 → (preparedAddCarryPython i).evalWith (preparedRowEnv row next pub 0 0)=0) :
    ∃ pc sp,pc<15 ∧ 2≤sp ∧ sp<9 ∧
      (∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
      (∀ i,i<16 → next i=if i=pc+1 then 1 else 0) ∧
      (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
      (∀ i,i<9 → next (16+i)=if i=sp-1 then 1 else 0) ∧
      Num.binop 32 0 (preparedStackWord row (sp-2)) (preparedStackWord row (sp-1))=
        some (preparedAddResultWord row) ∧
      (∀ slot,slot<8 → preparedStackWord next slot=if slot=sp-2 then preparedAddResultWord row
        else if slot=sp-1 then 0 else preparedStackWord row slot) := by
  obtain ⟨⟨pc,hpc,hp⟩,_⟩:=prepared_row_pc_sp row next pub 0 0 choices
  obtain ⟨⟨npc,hnpc,hnp⟩,⟨nsp,hnsp,hns⟩⟩:=prepared_row_pc_sp next next pub 0 0 nextChoices
  have add:=op 1 (by decide)
  simp only [ite_true] at add
  obtain ⟨sp,hsp,enough,hs,binop⟩:=prepared_active_add_binop row next pub 0 0 choices active noBorrow add depth carries
  obtain ⟨success,advance⟩:=prepared_success_advance row next pub active noBorrow op
  have pnext:=prepared_add_pc_next row next pub holds advance pc npc hpc hnpc hp hnp
  have snext:=prepared_add_sp_next row next pub holds success op sp nsp hsp hnsp hs hns
  have sn : nsp=sp-1 := by omega
  rw [pnext] at hnp
  rw [sn] at hns
  exact ⟨pc,sp,by omega,enough,hsp,hp,hnp,hs,hns,binop,
    fun slot hslot => prepared_add_stack_word_next row next pub holds success op sp hsp enough hs slot hslot⟩

/-- Structural source context: the irrelevant prefix/middle and interleaved
 dead-slot constraints may be instantiated with the rest of the actual table. -/
def preparedAddTransitionSource (prefixPart middle : List Expr) (dead : Nat → Nat → Expr) : List Expr :=
  prefixPart ++ (List.range 16).map preparedPCStepPython ++ [preparedPCOverflowPython,preparedSPStepPython] ++ middle ++
    (List.range 8).flatMap (fun slot => (List.range 2).flatMap (fun limb => [dead slot limb,preparedStackStepPython slot limb]))

theorem prepared_add_transition_source_extract (row next pub : Nat → Fp)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (source : ∀ e∈preparedAddTransitionSource prefixPart middle dead,
      e.evalWith (preparedRowEnv row next pub 0 0)=0) : PreparedAddTransitionHolds row next pub := by
  intro e he
  apply source e
  simp only [preparedAddTransitionSource,List.mem_append]
  simp only [preparedAddTransitionConstraints,List.mem_append] at he
  rcases he with (hp|hc)|hs
  · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
  · exact Or.inl (Or.inl (Or.inr hc))
  · obtain ⟨slot,hslot,hl⟩:=List.mem_flatMap.mp hs
    obtain ⟨limb,hlimb,eq⟩:=List.mem_map.mp hl
    subst e
    exact Or.inr (List.mem_flatMap.mpr ⟨slot,hslot,List.mem_flatMap.mpr ⟨limb,hlimb,by simp⟩⟩)

end NearCompression
