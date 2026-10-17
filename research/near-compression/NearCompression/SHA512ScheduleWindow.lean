import NearCompression.SHA512ScheduleTrace
import NearCompression.SHA512RoundSequence

/-! A complete sixteen-word rolling schedule window. These links authenticate
window evolution inside the trace; initial message bytes, round constants, and
compression-round consumption remain separate obligations. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

def sha512ScheduleWindowBase : Nat → Nat
  | 0 => 1440 | 1 => 576 | 2 => 1776 | 3 => 1840 | 4 => 1904 | 5 => 1968
  | 6 => 2032 | 7 => 2096 | 8 => 2160 | 9 => 1232 | 10 => 2224 | 11 => 2288
  | 12 => 2352 | 13 => 2416 | 14 => 0 | _ => 2480

def sha512ScheduleWindowWord (row : Nat → Fp) (i : Nat) : Nat :=
  sha512BitsWord row (sha512ScheduleWindowBase i)

def sha512ScheduleWindow (row : Nat → Fp) : List Nat :=
  (List.range 16).map (sha512ScheduleWindowWord row)

def sha512ScheduleWindowConstraints : List Expr :=
  sha512ScheduleConstraints ++ (List.range 768).map (fun bit => instructionBitConstraint (1776+bit))

def sha512ScheduleWindowTable : Table := ⟨2544,sha512ScheduleWindowConstraints,[],22⟩

def sha512ScheduleWindowPairs : List (Nat × Nat) :=
  (List.range 16).flatMap (fun i => (List.range 64).map (fun bit =>
    ((if i<15 then sha512ScheduleWindowBase (i+1) else 1712)+bit,sha512ScheduleWindowBase i+bit)))

def sha512ScheduleWindowSequenceTable : Table :=
  instructionSequenceTable sha512ScheduleWindowTable sha512ScheduleWindowPairs

theorem sha512_window_core_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    sha512ScheduleHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _ he))
  rw [instruction_local_eval e tr t r pub (sha512_schedule_constraints_local e he)] at hv
  exact hv

/-- The four core inputs and result use these exact bit encodings. -/
theorem sha512_window_core_words (row : Nat → Fp) (h : sha512ScheduleHolds row) :
    sha512ScheduleWindowWord row 0 = sha512ScheduleW0 row ∧
    sha512ScheduleWindowWord row 1 = sha512ScheduleW1 row ∧
    sha512ScheduleWindowWord row 9 = sha512ScheduleW9 row ∧
    sha512ScheduleWindowWord row 14 = sha512ScheduleW14 row ∧
    sha512BitsWord row 1712 = sha512ScheduleOutput row := by
  have a0 := sha512_add_word_bits _ (sha512_schedule_add_holds row h 0 (by decide)) 4 (by decide)
  have a1 := sha512_add_word_bits _ (sha512_schedule_add_holds row h 1 (by decide)) 4 (by decide)
  have a2 := sha512_add_word_bits _ (sha512_schedule_add_holds row h 2 (by decide)) 8 (by decide)
  simp only [sha512BitsWord,sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,
    Nat.reduceMul,Nat.reduceAdd] at a0 a1 a2
  refine ⟨a1.symm,?_,a0.symm,?_,a2.symm⟩ <;> rfl

theorem sha512_window_word_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (r i : Nat) (hi : i<16) (next : r+1 < tr.height t) :
    sha512ScheduleWindowWord (tr.cell t (r+1)) i =
      sha512BitsWord (tr.cell t r) (if i<15 then sha512ScheduleWindowBase (i+1) else 1712) := by
  apply ofBits_congr
  intro bit hb
  have eq := instruction_sequence_trace_link air tr pub t ht sha512ScheduleWindowTable
    sha512ScheduleWindowPairs table holds r
    ((if i<15 then sha512ScheduleWindowBase (i+1) else 1712)+bit) (sha512ScheduleWindowBase i+bit)
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩⟩) next
  rw [eq]

/-- Exact temporal binding to actual nextWindow, with no external word-link premises. -/
theorem sha512_schedule_window_recurrence (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (next : r+1 < tr.height t) :
    sha512ScheduleWindow (tr.cell t (r+1)) = nextWindow (sha512ScheduleWindow (tr.cell t r)) := by
  have h := sha512_window_core_holds air tr pub t ht table holds r (by omega)
  have words := sha512_window_core_words _ h
  have core := sha512_schedule_sound _ h
  have link (i : Nat) (hi : i<16) := sha512_window_word_link air tr pub t ht table holds r i hi next
  have l0 := link 0 (by decide); have l1 := link 1 (by decide)
  have l2 := link 2 (by decide); have l3 := link 3 (by decide)
  have l4 := link 4 (by decide); have l5 := link 5 (by decide)
  have l6 := link 6 (by decide); have l7 := link 7 (by decide)
  have l8 := link 8 (by decide); have l9 := link 9 (by decide)
  have l10 := link 10 (by decide); have l11 := link 11 (by decide)
  have l12 := link 12 (by decide); have l13 := link 13 (by decide)
  have l14 := link 14 (by decide); have l15 := link 15 (by decide)
  change [sha512ScheduleWindowWord (tr.cell t (r+1)) 0,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 1,sha512ScheduleWindowWord (tr.cell t (r+1)) 2,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 3,sha512ScheduleWindowWord (tr.cell t (r+1)) 4,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 5,sha512ScheduleWindowWord (tr.cell t (r+1)) 6,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 7,sha512ScheduleWindowWord (tr.cell t (r+1)) 8,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 9,sha512ScheduleWindowWord (tr.cell t (r+1)) 10,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 11,sha512ScheduleWindowWord (tr.cell t (r+1)) 12,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 13,sha512ScheduleWindowWord (tr.cell t (r+1)) 14,
    sha512ScheduleWindowWord (tr.cell t (r+1)) 15] = _
  rw [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15]
  simp only [show (15<15) = False from propext (by decide),ite_false]
  rw [words.2.2.2.2,core,←words.1,←words.2.1,←words.2.2.1,←words.2.2.2.1]
  rfl

theorem sha512_window_final (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (last : r+1 = tr.height t) (e : Expr)
    (he : e ∈ instructionSequenceConstraints sha512ScheduleWindowPairs) :
    e.eval tr t r pub = 0 := by
  obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp he
  exact instruction_sequence_eval_final tr pub t r pair.1 pair.2 last

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_window_table_wf :
    sha512ScheduleWindowTable.wf ⟨[sha512ScheduleWindowTable],0,0⟩ 3 = true ∧
    sha512ScheduleWindowSequenceTable.wf ⟨[sha512ScheduleWindowSequenceTable],0,0⟩ 3 = true := by decide

set_option maxRecDepth 65536 in
theorem sha512_window_table_size :
    sha512ScheduleWindowTable.width = 2544 ∧
    sha512ScheduleWindowTable.constraints.length = 2572 ∧
    sha512ScheduleWindowPairs.length = 1024 ∧
    sha512ScheduleWindowSequenceTable.constraints.length = 3596 := by decide

def sha512ScheduleWindowOutput (row : Nat → Fp) : List Nat :=
  (List.range 15).map (fun i => sha512ScheduleWindowWord row (i+1)) ++ [sha512ScheduleOutput row]

theorem sha512_schedule_window_output (row : Nat → Fp) (h : sha512ScheduleHolds row) :
    sha512ScheduleWindowOutput row = nextWindow (sha512ScheduleWindow row) := by
  have words := sha512_window_core_words row h
  unfold sha512ScheduleWindowOutput
  rw [sha512_schedule_sound row h,←words.1,←words.2.1,←words.2.2.1,←words.2.2.2.1]
  rfl

end NearCompression
