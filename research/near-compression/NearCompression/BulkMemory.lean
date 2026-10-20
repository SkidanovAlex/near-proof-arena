import NearCompression.MemoryTable

/-! Actual byte loops and store/bulk-memory instruction simulation. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem for_in_plain_state_equiv (xs : List Nat) (f : Nat → St → St)
    (s t : St) (h : StateEquivalent s t)
    (hf : ∀ i u v, StateEquivalent u v → StateEquivalent (f i u) (f i v)) :
    StateEquivalent
      (forIn (m := Id) xs s fun i st => ForInStep.yield (f i st))
      (forIn (m := Id) xs t fun i st => ForInStep.yield (f i st)) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.forIn_cons]
    exact ih _ _ (hf x s t h)

theorem state_equiv_write_le (s t : St) (h : StateEquivalent s t) (a w v : Nat) :
    StateEquivalent (writeLE s a w v) (writeLE t a w v) := by
  unfold writeLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  apply for_in_plain_state_equiv _ _ s t h
  intro i u v huv
  exact state_equiv_write_byte u v huv _ _

theorem mem_fill_equiv (s t : St) (h : StateEquivalent s t) (d v n : Nat) :
    ResultEquivalent (memFill s d v n) (memFill t d v n) := by
  unfold memFill
  rw [state_equiv_mem_bytes s t h]
  split
  · exact ⟨h, rfl⟩
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    apply for_in_plain_state_equiv _ _ s t h
    intro i u v huv
    exact state_equiv_write_byte u v huv _ _

theorem store_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (op align off : Nat) :
    ResultEquivalent (exec cfg p s f pf (.store op align off))
      (exec cfg p t f pf (.store op align off)) := by
  obtain ⟨hv, hs⟩ := state_equiv_pop_n s t h
  obtain ⟨ha, hst⟩ := state_equiv_pop_n _ _ hs
  simp only [exec]
  rw [hv, ha, state_equiv_mem_bytes _ _ hst]
  split
  · exact ⟨hst, rfl⟩
  · exact state_equiv_set_frame _ _ (state_equiv_write_le _ _ hst _ _ _) _

/-- Pop the three numeric operands once, retaining exact values and state. -/
theorem bulk_memory_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : i = .memCopy ∨ i = .memFill ∨ ∃ seg, i = .memInit seg) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  obtain ⟨hn, hs⟩ := state_equiv_pop_n s t h
  obtain ⟨ha, hst⟩ := state_equiv_pop_n _ _ hs
  obtain ⟨hb, hsu⟩ := state_equiv_pop_n _ _ hst
  rcases covered with rfl | rfl | ⟨seg, rfl⟩
  all_goals simp only [exec]
  all_goals rw [hn, ha, hb]
  · exact result_equiv_bind _ _ (mem_copy_equiv _ _ hsu _ _ _) _ _
      (fun u v huv => state_equiv_set_frame u v huv _)
  · exact result_equiv_bind _ _ (mem_fill_equiv _ _ hsu _ _ _) _ _
      (fun u v huv => state_equiv_set_frame u v huv _)
  · exact result_equiv_bind _ _ (mem_init_equiv _ _ hsu _ _ _ _) _ _
      (fun u v huv => state_equiv_set_frame u v huv _)

end NearCompression
