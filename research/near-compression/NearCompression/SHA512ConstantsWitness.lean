import NearCompression.SHA512CombinedWitness
import NearCompression.SHA512Constants
import NearCompression.SHA512LimbDecode

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

/-- A materialized row constructor, avoiding repeated same execution. -/
def sha512ConstantsWitnessAt (v : Vars) (window : List Nat) (r col : Nat) : Fp :=
  if col<5152 then sha512CombinedWitnessRow v window (K.getD r 0) col
  else if col-5152=r then 1 else 0

/-- A 128-row instance; rows after 79 remain actual zero-key rounds. -/
def sha512ConstantsWitnessRow (initial : Vars) (window : List Nat) (r col : Nat) : Fp :=
  if col<5152 then
    (sha512CombinedWitnessTrace initial window (fun r => K.getD r 0) 7).cell 0 r col
  else if col-5152=r then 1 else 0

def sha512ConstantsWitnessTrace (initial : Vars) (window : List Nat) : Trace Fp :=
  ⟨fun _ => 7, fun _ r col => sha512ConstantsWitnessRow initial window r col⟩

def sha512ConstantsWitnessAir : Air := ⟨[sha512ConstantsTable],0,0⟩

theorem sha512_constants_witness_at (initial : Vars) (window : List Nat) (r col : Nat) :
    sha512ConstantsWitnessRow initial window r col=
      sha512ConstantsWitnessAt (sha512CombinedStateRun initial window (fun r => K.getD r 0) r)
        (sha512ScheduleWindowRun window r) r col := rfl

theorem sha512_constants_witness_prefix (initial : Vars) (window : List Nat) (r col : Nat)
    (hc : col<5152) : sha512ConstantsWitnessRow initial window r col=
      (sha512CombinedWitnessTrace initial window (fun r => K.getD r 0) 7).cell 0 r col := by
  simp only [sha512ConstantsWitnessRow,if_pos hc]

theorem sha512_constants_witness_phase (initial : Vars) (window : List Nat) (r i : Nat) :
    sha512ConstantsWitnessRow initial window r (5152+i)=if i=r then 1 else 0 := by
  simp only [sha512ConstantsWitnessRow,if_neg (by omega : ¬5152+i<5152),Nat.add_sub_cancel_left]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_constants_witness_combined_bound :
    sha512CombinedConstraints.all (fun e => decide (e.colBound≤5152))=true := by decide

theorem sha512_constants_witness_first (initial : Vars) (window : List Nat) (r i : Nat) :
    (sha512ConstantFirst i).eval (sha512ConstantsWitnessTrace initial window) 0 r []=0 := by
  by_cases hr : r=0
  · subst r
    change (1 : Fp)*(sha512ConstantsWitnessRow initial window 0 (5152+i)+ -Fp.ofNat (if i=0 then 1 else 0))=0
    rw [sha512_constants_witness_phase]
    split
    · change (1 : Fp)*(1 + -1)=0
      grind
    · change (1 : Fp)*(0 + -0)=0
      grind
  · simp only [sha512ConstantFirst,Expr.eval,Expr.evalWith,rowEnv,hr,ite_false]
    change (0 : Fp)*_=0
    grind

theorem sha512_constants_witness_step (initial : Vars) (window : List Nat) (r i : Nat)
    (hr : r<128) :
    (sha512ConstantStep i).eval (sha512ConstantsWitnessTrace initial window) 0 r []=0 := by
  by_cases last : r+1=128
  · simp only [sha512ConstantStep,Expr.eval,Expr.evalWith,rowEnv]
    change (if r+1=128 then (0 : Fp) else 1)*_=0
    rw [if_pos last]
    grind
  · have next : r+1<128 := by omega
    have hn : r+1<(sha512ConstantsWitnessTrace initial window).height 0 := next
    have hl : r+1≠(sha512ConstantsWitnessTrace initial window).height 0 := last
    simp only [sha512ConstantStep,Expr.eval,Expr.evalWith,rowEnv,hl,ite_false,
      Nat.mod_eq_of_lt hn,Bool.false_eq_true,ite_true]
    by_cases hi : i=0
    · subst i
      simp only [ite_true,Expr.evalWith]
      change (1 : Fp)*(sha512ConstantsWitnessRow initial window (r+1) (5152+0)+ -0)=0
      rw [sha512_constants_witness_phase,if_neg (by omega : ¬0=r+1)]
      grind
    · simp only [hi,ite_false,Expr.evalWith,Bool.false_eq_true]
      change (1 : Fp)*(sha512ConstantsWitnessRow initial window (r+1) (5152+i)+
        -sha512ConstantsWitnessRow initial window r (5152+(i-1)))=0
      rw [sha512_constants_witness_phase,sha512_constants_witness_phase]
      have eq : i=r+1 ↔ i-1=r := by omega
      simp only [eq]
      split <;> grind

theorem sha512_constants_witness_last (initial : Vars) (window : List Nat) (r : Nat) :
    sha512ConstantLast.eval (sha512ConstantsWitnessTrace initial window) 0 r []=0 := by
  change (if r+1=128 then (1 : Fp) else 0)*(sha512ConstantsWitnessRow initial window r (5152+127)+ -1)=0
  rw [sha512_constants_witness_phase]
  by_cases last : r+1=128
  · have eq : r=127 := by omega
    subst r
    change (1 : Fp)*(1 + -1)=0
    grind
  · rw [if_neg last]
    grind

theorem sha512_constants_witness_key_limb (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) (r limb : Nat) (hl : limb<4) :
    sha512ConstantsWitnessRow initial window r (4116+limb)=Fp.ofNat (sha512ConstantDigit r limb) := by
  let v := sha512CombinedStateRun initial window (fun r => K.getD r 0) r
  let w := (sha512ScheduleWindowRun window r).getD 0 0
  have bounds : sha512RoundInputBounds v (K.getD r 0) w :=
    sha512_combined_run_input_bounds initial valid window windowValid _ sha512_standard_keys_bound r
  have rh := sha512_round_witness_holds v (K.getD r 0) w bounds
  have inputs := sha512_round_witness_inputs v (K.getD r 0) w bounds
  have ranges (i : Nat) (hi : i<4) := instruction_add64_ranges _
    (sha512_round_add_holds _ rh 2 (by decide)) (4+i) (by omega)
  have limbEq := sha512_word_limb_field (sha512RoundAddRow (sha512RoundWitness v (K.getD r 0) w) 2)
    4 (K.getD r 0) ranges inputs.2.1 limb hl
  rw [sha512_constants_witness_prefix initial window r _ (by omega)]
  change sha512CombinedWitnessRow v (sha512ScheduleWindowRun window r) (K.getD r 0) (4116+limb)=_
  rw [show 4116+limb=2544+(1572+limb) by omega,sha512_combined_witness_round_prefix]
  simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd,sha512ConstantDigit,w] using limbEq

theorem sha512_constants_witness_binding (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) (r limb : Nat)
    (hr : r<128) (hl : limb<4) :
    (sha512ConstantBinding limb).eval (sha512ConstantsWitnessTrace initial window) 0 r []=0 := by
  change sha512ConstantsWitnessRow initial window r (4116+limb)+
    -(sha512ConstantSum limb 128).eval (sha512ConstantsWitnessTrace initial window) 0 r []=0
  rw [sha512_constants_sum_eval _ [] 0 r limb 128 (by decide)
    (fun i _ => sha512_constants_witness_phase initial window r i),if_pos hr,
    sha512_constants_witness_key_limb initial valid window windowValid r limb hl]
  grind

/-- Every required constraint is established from the actual constructors. -/
theorem sha512_constants_witness_holds (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) :
    Holds sha512ConstantsWitnessAir [] (sha512ConstantsWitnessTrace initial window) := by
  have combined := sha512_combined_witness_trace_holds initial valid window windowValid
    (fun r => K.getD r 0) sha512_standard_keys_bound 7 (by decide)
  constructor
  · intro t ht
    have eq : t=0 := by simpa [sha512ConstantsWitnessAir] using ht
    subst t
    change 1≤7 ∧ 7≤7
    decide
  · intro t ht r hr e he
    have eq : t=0 := by simpa [sha512ConstantsWitnessAir] using ht
    subst t
    change r<128 at hr
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · have bound := of_decide_eq_true (List.all_eq_true.mp sha512_constants_witness_combined_bound e he)
            rw [sha512_trace_prefix_eval e (sha512ConstantsWitnessTrace initial window)
              (sha512CombinedWitnessTrace initial window (fun r => K.getD r 0) 7) 0 r [] 5152 bound rfl
              (fun r col hc => sha512_constants_witness_prefix initial window r col hc)]
            exact combined.constr 0 (by decide) r hr e he
          · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
            exact sha512_constants_witness_first initial window r i
        · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
          exact sha512_constants_witness_step initial window r i hr
      · have eq : e=sha512ConstantLast := by simpa using he
        subst e
        exact sha512_constants_witness_last initial window r
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      exact sha512_constants_witness_binding initial valid window windowValid r i hr (List.mem_range.mp hi)
  · intro t ht r hr i hi
    have eq : t=0 := by simpa [sha512ConstantsWitnessAir] using ht
    subst t
    simp [sha512ConstantsWitnessAir,sha512ConstantsTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512ConstantsWitnessAir,sha512ConstantsTable]

theorem sha512_combined_inputs_prefix (row other : Nat → Fp)
    (same : ∀ col,col<5152 → row col=other col) :
    sha512CombinedVars row=sha512CombinedVars other ∧ sha512CombinedWindow row=sha512CombinedWindow other := by
  have bits (base : Nat) (hb : base+64≤5152) : sha512BitsWord row base=sha512BitsWord other base := by
    apply ZkFormal.Sha.Sound.ofBits_congr
    intro bit hb'
    rw [same _ (by omega)]
  have word (base : Nat) (hb : base+4≤5152) : instructionAdd64Word row base=instructionAdd64Word other base := by
    unfold instructionAdd64Word
    rw [same base (by omega),same (base+1) (by omega),same (base+2) (by omega),same (base+3) (by omega)]
  constructor
  · change Vars.mk (sha512BitsWord row 2544) (sha512BitsWord row 2608) (sha512BitsWord row 2672)
      (instructionAdd64Word row 4944) (sha512BitsWord row 3120) (sha512BitsWord row 3184)
      (sha512BitsWord row 3248) (instructionAdd64Word row 3696)=
      Vars.mk (sha512BitsWord other 2544) (sha512BitsWord other 2608) (sha512BitsWord other 2672)
      (instructionAdd64Word other 4944) (sha512BitsWord other 3120) (sha512BitsWord other 3184)
      (sha512BitsWord other 3248) (instructionAdd64Word other 3696)
    rw [bits 2544 (by decide),bits 2608 (by decide),bits 2672 (by decide),word 4944 (by decide),
      bits 3120 (by decide),bits 3184 (by decide),bits 3248 (by decide),word 3696 (by decide)]
  · apply List.map_congr_left
    intro i hi
    apply bits
    have bound : sha512ScheduleWindowBase i≤2480 := by
      unfold sha512ScheduleWindowBase
      split <;> omega
    omega

theorem sha512_constants_witness_inputs (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) :
    sha512CombinedVars (sha512ConstantsWitnessRow initial window 0)=initial ∧
    sha512CombinedWindow (sha512ConstantsWitnessRow initial window 0)=window := by
  have same := sha512_combined_inputs_prefix (sha512ConstantsWitnessRow initial window 0)
    ((sha512CombinedWitnessTrace initial window (fun r => K.getD r 0) 7).cell 0 0)
    (sha512_constants_witness_prefix initial window 0)
  have inputs := sha512_combined_witness_inputs initial window (K.getD 0 0) windowValid
    (sha512_combined_run_input_bounds initial valid window windowValid _ sha512_standard_keys_bound 0)
  exact ⟨same.1.trans inputs.1,same.2.trans inputs.2.1⟩

/-- Row 79 is the actual eighty-round endpoint for the supplied inputs. -/
theorem sha512_constants_witness_endpoint (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) :
    rounds initial K window=sha512CombinedOutput (sha512ConstantsWitnessRow initial window 79) := by
  have endpoint := sha512_constants_endpoint sha512ConstantsWitnessAir
    (sha512ConstantsWitnessTrace initial window) [] 0 (by decide) rfl
    (sha512_constants_witness_holds initial valid window windowValid)
  have inputs := sha512_constants_witness_inputs initial valid window windowValid
  change rounds (sha512CombinedVars (sha512ConstantsWitnessRow initial window 0)) K
    (sha512CombinedWindow (sha512ConstantsWitnessRow initial window 0))=_ at endpoint
  rw [inputs.1,inputs.2] at endpoint
  exact endpoint

end NearCompression
