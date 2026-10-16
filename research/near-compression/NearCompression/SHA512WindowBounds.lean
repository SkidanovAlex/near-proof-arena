import NearCompression.SHA512ScheduleWindow

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound

theorem sha512_add_range_bit (row : Nat → Fp) (h : instructionAdd64Holds row)
    (limb bit : Nat) (hl : limb<12) (hb : bit<16) :
    (row (16+16*limb+bit)).toNat≤1 := by
  have hc := h (instructionBitConstraint (16+16*limb+bit))
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨limb,List.mem_range.mpr hl,
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩)⟩))
  exact instruction_add_boolean_bound _ hc

theorem sha512_add_word_bit (row : Nat → Fp) (h : instructionAdd64Holds row)
    (base bit : Nat) (hb : base+4≤12) (hbit : bit<64) :
    (row (16+16*base+bit)).toNat≤1 := by
  have bound := sha512_add_range_bit row h (base+bit/16) (bit%16) (by omega) (Nat.mod_lt _ (by decide))
  have eq : 16+16*(base+bit/16)+bit%16=16+16*base+bit := by omega
  rwa [eq] at bound

/-- Every bit of all sixteen decoded window words is Boolean under the actual AIR. -/
theorem sha512_window_bit_boolean (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length)
    (table : air.tables[t]=sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) (i : Nat) (hi : i<16) (bit : Nat) (hb : bit<64) :
    (tr.cell t r (sha512ScheduleWindowBase i+bit)).toNat≤1 := by
  have core := sha512_window_core_holds air tr pub t ht table holds r hr
  by_cases i0 : i=0
  · subst i
    have bound := sha512_add_word_bit _ (sha512_schedule_add_holds _ core 1 (by decide)) 4 bit (by decide) hb
    simpa only [sha512ScheduleWindowBase,sha512RoundAddRow,sha512RoundAddBase,
      ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  by_cases i1 : i=1
  · subst i
    have bound := sha512_bits_input_boolean _ (sha512_schedule_bits_holds _ core 1 (by decide)) bit (by omega)
    exact bound
  by_cases i9 : i=9
  · subst i
    have bound := sha512_add_word_bit _ (sha512_schedule_add_holds _ core 0 (by decide)) 4 bit (by decide) hb
    simpa only [sha512ScheduleWindowBase,sha512RoundAddRow,sha512RoundAddBase,
      ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  by_cases i14 : i=14
  · subst i
    have bound := sha512_bits_input_boolean _ (sha512_schedule_bits_holds _ core 0 (by decide)) bit (by omega)
    simpa only [sha512ScheduleWindowBase,sha512RoundBitsRow,Nat.mul_zero,Nat.zero_add] using bound
  have checked : ∀ i : Fin 16, i.val≠0 → i.val≠1 → i.val≠9 → i.val≠14 →
      1776≤sha512ScheduleWindowBase i.val ∧ sha512ScheduleWindowBase i.val+64≤2544 := by decide
  have span : 1776≤sha512ScheduleWindowBase i ∧ sha512ScheduleWindowBase i+64≤2544 :=
    checked ⟨i,hi⟩ i0 i1 i9 i14
  let col := sha512ScheduleWindowBase i+bit
  have lo : 1776≤col := by dsimp [col]; omega
  have high : col-1776<768 := by dsimp [col]; omega
  have ceq : 1776+(col-1776)=col := by omega
  have hc := holds.constr t ht r hr (instructionBitConstraint col)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨col-1776,List.mem_range.mpr high,by rw [ceq]⟩)))
  rw [instruction_local_eval _ tr t r pub (by simp [instructionBitConstraint,instructionLocalExpr])] at hv
  exact instruction_add_boolean_bound _ hv

theorem sha512_window_word_bound (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length)
    (table : air.tables[t]=sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (r i : Nat) (hr : r<tr.height t) (hi : i<16) :
    sha512ScheduleWindowWord (tr.cell t r) i<2^64 := by
  apply ofBits_lt
  intro bit hb
  exact sha512_window_bit_boolean air tr pub t ht table holds r hr i hi bit hb

end NearCompression
