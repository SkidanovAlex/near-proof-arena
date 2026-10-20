import NearCompression.StackControl

/-! Representation preservation for table access/growth and memory growth.
The existing bounds, allocation expressions and failure results are unchanged. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_data_update (s t : St) (h : StateEquivalent s t)
    (stack : Array Val) (table : Array (Option Nat)) (pages : Array ByteArray)
    (elems : Array (Array (Option Nat))) (datas : Array ByteArray) (tableMax : Nat) :
    StateEquivalent { s with stack, table, pages, elems, datas, tableMax }
      { t with stack, table, pages, elems, datas, tableMax } :=
  ⟨congrArg (fun s : St => { s with stack, table, pages, elems, datas, tableMax }) h.core, h.real⟩

def MemoryTableInstruction : Instr → Prop
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _
  | .memSize | .memGrow | .elemDrop _ | .dataDrop _ | .float _ => True
  | _ => False

theorem memory_table_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : MemoryTableInstruction i) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  have ht : s.table = t.table := by have he := congrArg St.table h.core; exact he
  have hm : s.tableMax = t.tableMax := by have he := congrArg St.tableMax h.core; exact he
  have hp : s.pages = t.pages := by have he := congrArg St.pages h.core; exact he
  have he : s.elems = t.elems := by have hh := congrArg St.elems h.core; exact hh
  have hd : s.datas = t.datas := by have hh := congrArg St.datas h.core; exact hh
  cases i <;> simp only [MemoryTableInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form, pushI32, pushV,
    hv, ht, hm, hp, he, hd]
  all_goals repeat' (split <;> (try simp_all only []))
  all_goals first
    | rfl
    | exact ⟨state_equiv_data_update s t h _ _ _ _ _ _, rfl⟩
    | exact state_equiv_set_frame _ _ (state_equiv_data_update s t h _ _ _ _ _ _) _

theorem state_equiv_read_le (s t : St) (h : StateEquivalent s t) (a w : Nat) :
    readLE s a w = readLE t a w := by
  have he := congrArg (fun s => readLE s a w) h.core
  exact he

theorem load_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (op align off : Nat) :
    ResultEquivalent (exec cfg p s f pf (.load op align off))
      (exec cfg p t f pf (.load op align off)) := by
  obtain ⟨hv, hs⟩ := state_equiv_pop_n s t h
  simp only [exec]
  rcases he : loadSpec op with ⟨w, sgn, is64⟩
  simp only [he]
  rw [hv, state_equiv_mem_bytes _ _ hs, state_equiv_read_le _ _ hs]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact ⟨hs, rfl⟩
    | exact state_equiv_set_frame _ _ (state_equiv_push_v _ _ hs _) _

end NearCompression
