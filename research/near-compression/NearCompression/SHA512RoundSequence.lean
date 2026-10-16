import NearCompression.SHA512RoundTrace
import NearCompression.InstructionSequence

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound

def sha512RoundSequenceWordPairs : List (Nat × Nat) :=
  [(2336,0),(0,64),(64,128),(128,2416),(2544,576),(576,640),(640,704),(704,1168)]

def sha512RoundSequencePairs : List (Nat × Nat) :=
  sha512RoundSequenceWordPairs.flatMap (fun p => (List.range 64).map (fun bit => (p.1+bit,p.2+bit)))

def sha512RoundSequenceTable : Table :=
  instructionSequenceTable sha512RoundTable sha512RoundSequencePairs

/-- Each adder word equals its own constrained sixty-four bit representation. -/
theorem sha512_add_word_bits (row : Nat → Fp) (h : instructionAdd64Holds row)
    (base : Nat) (hb : base + 4 ≤ 12) :
    instructionAdd64Word row base = sha512BitsWord row (16+16*base) := by
  apply sha512_bit_word_binding
  · intro bit hbit
    let limb := base + bit / 16
    have hl : limb < 12 := by dsimp [limb]; omega
    have hm : bit % 16 < 16 := Nat.mod_lt _ (by decide)
    have hc := h (instructionBitConstraint (16+16*limb+bit%16))
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨limb,List.mem_range.mpr hl,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bit%16,List.mem_range.mpr hm,rfl⟩)⟩))
    have bound := instruction_add_boolean_bound _ hc
    have eq : 16+16*limb+bit%16 = 16+16*base+bit := by dsimp [limb]; omega
    change (row (16+16*limb+bit%16)).toNat ≤ 1 at bound
    simpa only [eq] using bound
  · intro i hi
    have hc := h (.add (.col (base+i) false) (.neg (instructionBitExpr (16+16*(base+i)) 16)))
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨base+i,List.mem_range.mpr (by omega),
        List.mem_cons_self ..⟩))
    change row (base+i) + -(instructionBitExpr (16+16*(base+i)) 16).evalWith (instructionAddEnv row) = 0 at hc
    have eq : 16+16*(base+i) = 16+16*base+16*i := by omega
    rw [eq] at hc
    grind

theorem sha512_sequence_row_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    sha512RoundHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc (List.mem_append_left _ he)
  rw [instruction_local_eval e tr t r pub (sha512_round_constraints_local e he)] at hv
  exact hv

theorem sha512_sequence_word_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) (r post pre : Nat)
    (pair : (post,pre) ∈ sha512RoundSequenceWordPairs) (next : r+1 < tr.height t) :
    sha512BitsWord (tr.cell t r) post = sha512BitsWord (tr.cell t (r+1)) pre := by
  apply ofBits_congr
  intro bit hb
  rw [instruction_sequence_trace_link air tr pub t ht sha512RoundTable sha512RoundSequencePairs
    table holds r (post+bit) (pre+bit)
    (List.mem_flatMap.mpr ⟨(post,pre),pair,List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩⟩) next]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_sequence_table_wf :
    sha512RoundSequenceTable.wf ⟨[sha512RoundSequenceTable],0,0⟩ 3 = true := by decide

set_option maxRecDepth 65536 in
theorem sha512_sequence_table_size :
    sha512RoundSequenceTable.width = 2608 ∧
    sha512RoundSequencePairs.length = 512 ∧
    sha512RoundSequenceTable.constraints.length = 3188 := by decide

/-- Adder inputs/outputs used by state chaining decode from these exact bit columns. -/
theorem sha512_round_add_bits (row : Nat → Fp) (h : sha512RoundHolds row)
    (adder base : Nat) (ha : adder < 7) (hb : base+4 ≤ 12) :
    instructionAdd64Word (sha512RoundAddRow row adder) base =
      sha512BitsWord row (sha512RoundAddBase adder+(16+16*base)) := by
  have eq := sha512_add_word_bits _ (sha512_round_add_holds row h adder ha) base hb
  simpa only [sha512BitsWord,sha512RoundAddRow,Nat.add_assoc] using eq

theorem sha512_sequence_state_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (next : r+1 < tr.height t) :
    sha512RoundVars (tr.cell t (r+1)) = sha512RoundOutput (tr.cell t r) := by
  have cur := sha512_sequence_row_holds air tr pub t ht table holds r (by omega)
  have nxt := sha512_sequence_row_holds air tr pub t ht table holds (r+1) next
  have a := sha512_round_add_bits _ cur 5 8 (by decide) (by decide)
  have e := sha512_round_add_bits _ cur 6 8 (by decide) (by decide)
  have d := sha512_round_add_bits _ nxt 6 0 (by decide) (by decide)
  have h := sha512_round_add_bits _ nxt 0 0 (by decide) (by decide)
  have link (post pre : Nat) (hp : (post,pre) ∈ sha512RoundSequenceWordPairs) :=
    sha512_sequence_word_link air tr pub t ht table holds r post pre hp next
  have l0 := link 2336 0 (by decide)
  have l1 := link 0 64 (by decide)
  have l2 := link 64 128 (by decide)
  have l3 := link 128 2416 (by decide)
  have l4 := link 2544 576 (by decide)
  have l5 := link 576 640 (by decide)
  have l6 := link 640 704 (by decide)
  have l7 := link 704 1168 (by decide)
  simp only [sha512RoundAddBase,Nat.reduceMul,Nat.reduceAdd] at a e d h
  unfold sha512RoundOutput sha512RoundVars
  rw [a,e,d,h]
  simp only [sha512BitsWord,sha512RoundBitsRow,Nat.reduceMul,Nat.reduceAdd,Nat.zero_add,←Nat.add_assoc] at l0 l1 l2 l3 l4 l5 l6 l7 ⊢
  rw [←l0,←l1,←l2,←l3,←l4,←l5,←l6,←l7]

/-- The rows follow actual SHA-512 rounds. Round constants and message words
remain independent per-row inputs; this is not a schedule or full hash proof. -/
theorem sha512_sequence_round_recurrence (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (next : r+1 < tr.height t) :
    sha512RoundVars (tr.cell t (r+1)) = NearSpecV3.SHA512.round
      (sha512RoundVars (tr.cell t r)) (sha512RoundK (tr.cell t r)) (sha512RoundW (tr.cell t r)) := by
  rw [sha512_sequence_state_link air tr pub t ht table holds r next]
  exact (sha512_round_full_output _ (sha512_sequence_row_holds air tr pub t ht table holds r (by omega))).symm

/-- No state wire links the final round back to the first round. -/
theorem sha512_sequence_final (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (last : r+1 = tr.height t) (e : Expr)
    (he : e ∈ instructionSequenceConstraints sha512RoundSequencePairs) :
    e.eval tr t r pub = 0 := by
  obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp he
  exact instruction_sequence_eval_final tr pub t r pair.1 pair.2 last

end NearCompression
