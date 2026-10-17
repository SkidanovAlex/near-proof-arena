import NearCompression.BulkMemory

/-! Bulk table updates use identical table computations on related states.
No implementation of the existing loops is substituted. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_table_elements (s t : St) (h : StateEquivalent s t)
    (table : Array (Option Nat)) (elems : Array (Array (Option Nat))) :
    StateEquivalent { s with table, elems } { t with table, elems } :=
  ⟨congrArg (fun s : St => { s with table, elems }) h.core, h.real⟩

theorem table_init_equiv (s t : St) (h : StateEquivalent s t) (seg d src n : Nat) :
    ResultEquivalent (tableInit s seg d src n) (tableInit t seg d src n) := by
  have ht : s.table = t.table := by have he := congrArg St.table h.core; exact he
  have he : s.elems = t.elems := by have hh := congrArg St.elems h.core; exact hh
  unfold tableInit
  rw [ht, he]
  dsimp only
  split
  · exact ⟨h, rfl⟩
  · exact state_equiv_table_elements s t h _ _

def BulkTableInstruction : Instr → Prop
  | .tableFill _ | .tableCopy _ _ => True
  | _ => False

theorem bulk_table_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : BulkTableInstruction i) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  have ht : s.table = t.table := by have he := congrArg St.table h.core; exact he
  have hm : s.tableMax = t.tableMax := by have he := congrArg St.tableMax h.core; exact he
  have hp : s.pages = t.pages := by have he := congrArg St.pages h.core; exact he
  have he : s.elems = t.elems := by have hh := congrArg St.elems h.core; exact hh
  have hd : s.datas = t.datas := by have hh := congrArg St.datas h.core; exact hh
  cases i <;> simp only [BulkTableInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form, hv, ht, hm, hp, he, hd]
  all_goals split
  all_goals first
    | exact ⟨state_equiv_data_update s t h _ _ _ _ _ _, rfl⟩
    | exact state_equiv_set_frame _ _ (state_equiv_data_update s t h _ _ _ _ _ _) _

theorem table_init_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc) (seg tab : Nat) :
    ResultEquivalent (exec cfg p s f pf (.tableInit seg tab))
      (exec cfg p t f pf (.tableInit seg tab)) := by
  obtain ⟨hn, hs⟩ := state_equiv_pop_n s t h
  obtain ⟨ha, hst⟩ := state_equiv_pop_n _ _ hs
  obtain ⟨hb, hsu⟩ := state_equiv_pop_n _ _ hst
  simp only [exec]
  rw [hn, ha, hb]
  exact result_equiv_bind _ _ (table_init_equiv _ _ hsu _ _ _ _) _ _
    (fun u v huv => state_equiv_set_frame u v huv _)

end NearCompression
