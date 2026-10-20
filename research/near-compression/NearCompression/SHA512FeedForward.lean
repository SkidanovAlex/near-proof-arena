import NearCompression.SHA512Constants

/-! Feed-forward additions for one compression instance. Every row computes
the eight additions; row 79 is the cryptographic endpoint. Initial-state and
message/public-I/O binding, padding, and block chaining are separate. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

def sha512FeedForwardBase (i : Nat) : Nat := 5280+208*i
def sha512FeedForwardRow (row : Nat → Fp) (i : Nat) : Nat → Fp :=
  fun col => row (sha512FeedForwardBase i+col)
def sha512FeedForwardInputBase : Nat → Nat
  | 0 => 2544 | 1 => 2608 | 2 => 2672 | 3 => 4960
  | 4 => 3120 | 5 => 3184 | 6 => 3248 | _ => 3712
def sha512FeedForwardResultBase : Nat → Nat
  | 0 => 4880 | 1 => 2544 | 2 => 2608 | 3 => 2672
  | 4 => 5088 | 5 => 3120 | 6 => 3184 | _ => 3248
def sha512FeedForwardVarsWord (v : Vars) : Nat → Nat
  | 0 => v.a | 1 => v.b | 2 => v.c | 3 => v.d
  | 4 => v.e | 5 => v.f | 6 => v.g | _ => v.h

def sha512FeedForwardFirst (i bit : Nat) : Expr :=
  .mul .isFirst (.add (.col (sha512FeedForwardBase i+16+bit) false)
    (.neg (.col (sha512FeedForwardInputBase i+bit) false)))
def sha512FeedForwardStep (i bit : Nat) : Expr :=
  instructionSequenceConstraint (sha512FeedForwardBase i+16+bit,sha512FeedForwardBase i+16+bit)
def sha512FeedForwardResult (i bit : Nat) : Expr :=
  .add (.col (sha512FeedForwardBase i+80+bit) false)
    (.neg (.col (sha512FeedForwardResultBase i+bit) false))
def sha512FeedForwardAddConstraints : List Expr :=
  (List.range 8).flatMap (fun i => instructionAdd64Constraints.map (sha512RelocateExpr (sha512FeedForwardBase i)))
def sha512FeedForwardFirstConstraints : List Expr :=
  (List.range 8).flatMap (fun i => (List.range 64).map (sha512FeedForwardFirst i))
def sha512FeedForwardStepConstraints : List Expr :=
  (List.range 8).flatMap (fun i => (List.range 64).map (sha512FeedForwardStep i))
def sha512FeedForwardResultConstraints : List Expr :=
  (List.range 8).flatMap (fun i => (List.range 64).map (sha512FeedForwardResult i))
def sha512FeedForwardConstraints : List Expr :=
  sha512ConstantsConstraints ++ sha512FeedForwardAddConstraints ++ sha512FeedForwardFirstConstraints ++
    sha512FeedForwardStepConstraints ++ sha512FeedForwardResultConstraints
def sha512FeedForwardTable : Table := ⟨6944,sha512FeedForwardConstraints,[],7⟩
def sha512FeedForwardOutput (row : Nat → Fp) : List Nat :=
  (List.range 8).map (fun i => instructionAdd64Word (sha512FeedForwardRow row i) 8)

theorem sha512_ff_constants_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) :
    Holds ⟨[sha512ConstantsTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
  constructor
  · intro j hj
    have hz : j=0 := by simpa using hj
    subst j
    have h := holds.logBound t ht
    rw [table] at h
    exact h
  · intro j hj r hr e he
    have hz : j=0 := by simpa using hj
    subst j
    rw [←sha512_combined_relocate_eval,sha512_relocate_zero]
    have hc := holds.constr t ht r hr e
    rw [table] at hc
    exact hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ he))))
  · intro j hj r hr i hi
    have hz : j=0 := by simpa using hj
    subst j
    simp [sha512ConstantsTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512ConstantsTable]

set_option maxRecDepth 32768 in
theorem sha512_ff_add_local : instructionAdd64Constraints.all sha512CurrentExpr=true := by decide

theorem sha512_ff_add_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r i : Nat) (hr : r<tr.height t) (hi : i<8) :
    instructionAdd64Holds (sha512FeedForwardRow (tr.cell t r) i) := by
  intro e he
  have hc := holds.constr t ht r hr (sha512RelocateExpr (sha512FeedForwardBase i) e)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨e,he,rfl⟩⟩)))))
  rw [sha512_combined_relocate_eval] at hv
  rw [instruction_local_eval e _ 0 r pub (sha512_current_expr_local e
    (List.all_eq_true.mp sha512_ff_add_local e he))] at hv
  exact hv

theorem sha512_ff_first_bit (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    tr.cell t 0 (sha512FeedForwardBase i+16+bit) = tr.cell t 0 (sha512FeedForwardInputBase i+bit) := by
  have hc := holds.constr t ht 0 (Nat.two_pow_pos _) (sha512FeedForwardFirst i bit)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩⟩))))
  change (1 : Fp) * (tr.cell t 0 (sha512FeedForwardBase i+16+bit) +
    -tr.cell t 0 (sha512FeedForwardInputBase i+bit))=0 at hv
  grind

theorem sha512_ff_constant_bit (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    tr.cell t r (sha512FeedForwardBase i+16+bit) = tr.cell t 0 (sha512FeedForwardInputBase i+bit) := by
  induction r with
  | zero => exact sha512_ff_first_bit air tr pub t ht table holds i bit hi hb
  | succ r ih =>
    have hc := holds.constr t ht r (by omega) (sha512FeedForwardStep i bit)
    rw [table] at hc
    have hv := hc (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩⟩)))
    have link := instruction_sequence_eval_link tr pub t r
      (sha512FeedForwardBase i+16+bit) (sha512FeedForwardBase i+16+bit) hr hv
    rw [←link]
    exact ih (by omega)

theorem sha512_ff_result_bit (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r i bit : Nat) (hr : r<tr.height t) (hi : i<8) (hb : bit<64) :
    tr.cell t r (sha512FeedForwardBase i+80+bit) = tr.cell t r (sha512FeedForwardResultBase i+bit) := by
  have hc := holds.constr t ht r hr (sha512FeedForwardResult i bit)
  rw [table] at hc
  have hv := hc (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩⟩))
  change tr.cell t r (sha512FeedForwardBase i+80+bit) + -tr.cell t r (sha512FeedForwardResultBase i+bit)=0 at hv
  grind

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem sha512_ff_table_wf : sha512FeedForwardTable.wf ⟨[sha512FeedForwardTable],0,0⟩ 3=true := by decide

set_option maxRecDepth 65536 in
theorem sha512_ff_table_size :
    sha512FeedForwardTable.width=6944 ∧ sha512FeedForwardTable.constraints.length=10341 := by decide

theorem sha512_ff_input_words (row : Nat → Fp)
    (h : sha512RoundHolds (sha512CombinedRoundRow row)) (i : Nat) (hi : i<8) :
    sha512BitsWord row (sha512FeedForwardInputBase i) = sha512FeedForwardVarsWord (sha512CombinedVars row) i := by
  have d := sha512_round_add_bits _ h 6 0 (by decide) (by decide)
  have hh := sha512_round_add_bits _ h 0 0 (by decide) (by decide)
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases cases with hi | hi | hi | hi | hi | hi | hi | hi <;> subst i
  all_goals simp only [sha512FeedForwardInputBase,sha512FeedForwardVarsWord,sha512CombinedVars,sha512RoundVars]
  all_goals simp only [sha512BitsWord,sha512RoundBitsRow,sha512CombinedRoundRow,sha512RoundAddBase,
    ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd,Nat.zero_add] at d hh ⊢
  all_goals first | rfl | exact d.symm | exact hh.symm

theorem sha512_ff_output_words (row : Nat → Fp)
    (h : sha512RoundHolds (sha512CombinedRoundRow row)) (i : Nat) (hi : i<8) :
    sha512BitsWord row (sha512FeedForwardResultBase i) = sha512FeedForwardVarsWord (sha512CombinedOutput row) i := by
  have a := sha512_round_add_bits _ h 5 8 (by decide) (by decide)
  have e := sha512_round_add_bits _ h 6 8 (by decide) (by decide)
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases cases with hi | hi | hi | hi | hi | hi | hi | hi <;> subst i
  all_goals simp only [sha512FeedForwardResultBase,sha512FeedForwardVarsWord,sha512CombinedOutput,
    sha512RoundOutput,sha512RoundVars]
  all_goals simp only [sha512BitsWord,sha512RoundBitsRow,sha512CombinedRoundRow,sha512RoundAddBase,
    ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd,Nat.zero_add] at a e ⊢
  all_goals first | rfl | exact a.symm | exact e.symm

theorem sha512_ff_round_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512RoundHolds (sha512CombinedRoundRow (tr.cell t r)) := by
  have constants := sha512_ff_constants_holds air tr pub t ht table holds
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl constants
  have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl combined
  have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds r hr
  change sha512RoundHolds (fun col => tr.cell t r (2544+col))
  simpa only [sha512CombinedProjection,Nat.zero_add] using row

theorem sha512_ff_inputs (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r i : Nat) (hr : r<tr.height t) (hi : i<8) :
    instructionAdd64Word (sha512FeedForwardRow (tr.cell t r) i) 0 =
      sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell t 0)) i ∧
    instructionAdd64Word (sha512FeedForwardRow (tr.cell t r) i) 4 =
      sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell t r)) i := by
  have add := sha512_ff_add_holds air tr pub t ht table holds r i hr hi
  have a := sha512_add_word_bits _ add 0 (by decide)
  have b := sha512_add_word_bits _ add 4 (by decide)
  have aeq : sha512BitsWord (sha512FeedForwardRow (tr.cell t r) i) 16 =
      sha512BitsWord (tr.cell t 0) (sha512FeedForwardInputBase i) := by
    apply ofBits_congr
    intro bit hb
    have eq := sha512_ff_constant_bit air tr pub t ht table holds r hr i bit hi hb
    simpa only [sha512FeedForwardRow,Nat.add_assoc] using congrArg Fp.toNat eq
  have beq : sha512BitsWord (sha512FeedForwardRow (tr.cell t r) i) 80 =
      sha512BitsWord (tr.cell t r) (sha512FeedForwardResultBase i) := by
    apply ofBits_congr
    intro bit hb
    have eq := sha512_ff_result_bit air tr pub t ht table holds r i bit hr hi hb
    simpa only [sha512FeedForwardRow,Nat.add_assoc] using congrArg Fp.toNat eq
  have init := sha512_ff_input_words _ (sha512_ff_round_holds air tr pub t ht table holds 0 (Nat.two_pow_pos _)) i hi
  have result := sha512_ff_output_words _ (sha512_ff_round_holds air tr pub t ht table holds r hr) i hi
  exact ⟨a.trans (aeq.trans init),b.trans (beq.trans result)⟩

/-- Every feed-forward row adds the fixed initial state to its current round output. -/
theorem sha512_ff_output (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512FeedForwardOutput (tr.cell t r) = (List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell t 0)) i)
        (sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell t r)) i)) := by
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have eq := sha512_add_air_sound _ (sha512_ff_add_holds air tr pub t ht table holds r i hr bound)
  have inputs := sha512_ff_inputs air tr pub t ht table holds r i hr bound
  rw [inputs.1,inputs.2] at eq
  exact eq.symm

/-- Actual eighty-round result followed by all eight modular feed-forward additions. -/
theorem sha512_ff_endpoint (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512FeedForwardTable)
    (holds : Holds air pub tr) :
    sha512FeedForwardOutput (tr.cell t 79) = (List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell t 0)) i)
        (sha512FeedForwardVarsWord
          (rounds (sha512CombinedVars (tr.cell t 0)) K (sha512CombinedWindow (tr.cell t 0))) i)) := by
  have constants := sha512_ff_constants_holds air tr pub t ht table holds
  have height := sha512_constants_height _ _ pub 0 (by decide) rfl constants
  have endpoint := sha512_constants_endpoint _ _ pub 0 (by decide) rfl constants
  have bound : 79<tr.height t := by change tr.height t=128 at height; omega
  rw [sha512_ff_output air tr pub t ht table holds 79 bound]
  have endpoint' : rounds (sha512CombinedVars (tr.cell t 0)) K (sha512CombinedWindow (tr.cell t 0)) =
      sha512CombinedOutput (tr.cell t 79) := by
    simpa only [sha512CombinedProjection,Nat.zero_add] using endpoint
  rw [endpoint']

end NearCompression
