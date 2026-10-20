import NearCompression.SHA512ScheduleWindow

/-! Joint schedule and compression-round AIR. Each round consumes the current
schedule-window head. Constants k, initial message/state, padding, and final
feed-forward remain unbound here. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

def sha512CombinedRoundRow (row : Nat → Fp) : Nat → Fp := fun col => row (2544+col)
def sha512CombinedWindow (row : Nat → Fp) : List Nat := sha512ScheduleWindow row
def sha512CombinedVars (row : Nat → Fp) : Vars := sha512RoundVars (sha512CombinedRoundRow row)
def sha512CombinedK (row : Nat → Fp) : Nat := sha512RoundK (sha512CombinedRoundRow row)
def sha512CombinedOutput (row : Nat → Fp) : Vars := sha512RoundOutput (sha512CombinedRoundRow row)

def sha512CombinedWordConstraints : List Expr :=
  (List.range 64).map (fun bit => .add (.col (1440+bit) false) (.neg (.col (4400+bit) false)))
def sha512CombinedConstraints : List Expr :=
  sha512ScheduleWindowSequenceTable.constraints ++
    sha512RoundSequenceTable.constraints.map (sha512RelocateExpr 2544) ++ sha512CombinedWordConstraints

def sha512CombinedTable : Table := ⟨5152,sha512CombinedConstraints,[],22⟩

/-- Preserve selectors and cyclic next-row semantics while projecting columns. -/
def sha512CombinedProjection (tr : Trace Fp) (source offset : Nat) : Trace Fp :=
  ⟨fun _ => tr.log source,fun _ r col => tr.cell source r (offset+col)⟩

theorem sha512_combined_relocate_eval (tr : Trace Fp) (pub : List Fp)
    (source offset r : Nat) (e : Expr) :
    (sha512RelocateExpr offset e).eval tr source r pub =
      e.eval (sha512CombinedProjection tr source offset) 0 r pub := by
  induction e <;> simp_all [sha512RelocateExpr,Expr.eval,Expr.evalWith,rowEnv,
    sha512CombinedProjection,Trace.height] <;> rfl

/-- Generic isolated-table projection, including all next-row constraints. -/
theorem sha512_combined_project_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) (base : Table) (offset : Nat)
    (maxLog : base.maxLog=22) (empty : base.interactions=[])
    (member : ∀ e ∈ base.constraints, sha512RelocateExpr offset e ∈ sha512CombinedConstraints) :
    Holds ⟨[base],0,0⟩ pub (sha512CombinedProjection tr t offset) := by
  constructor
  · intro j hj
    have hj0 : j=0 := by simpa using hj
    subst j
    have hb := holds.logBound t ht
    rw [table] at hb
    simpa [sha512CombinedProjection,maxLog,sha512CombinedTable] using hb
  · intro j hj r hr e he
    have hj0 : j=0 := by simpa using hj
    subst j
    rw [←sha512_combined_relocate_eval]
    have hc := holds.constr t ht r hr (sha512RelocateExpr offset e)
    rw [table] at hc
    exact hc (member e he)
  · intro j hj r hr i hi
    have hj0 : j=0 := by simpa using hj
    subst j
    simpa [empty] using hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,empty]

theorem sha512_relocate_zero (e : Expr) : sha512RelocateExpr 0 e=e := by
  induction e <;> simp_all [sha512RelocateExpr]

theorem sha512_combined_schedule_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) :
    Holds ⟨[sha512ScheduleWindowSequenceTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
  apply sha512_combined_project_holds air tr pub t ht table holds _ 0 rfl rfl
  intro e he
  rw [sha512_relocate_zero]
  exact List.mem_append_left _ (List.mem_append_left _ he)

theorem sha512_combined_round_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) :
    Holds ⟨[sha512RoundSequenceTable],0,0⟩ pub (sha512CombinedProjection tr t 2544) := by
  apply sha512_combined_project_holds air tr pub t ht table holds _ 2544 rfl rfl
  intro e he
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨e,he,rfl⟩))

theorem sha512_combined_word_bits (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512BitsWord (tr.cell t r) 1440 = sha512BitsWord (tr.cell t r) 4400 := by
  apply ofBits_congr
  intro bit hb
  have hc := holds.constr t ht r hr (.add (.col (1440+bit) false) (.neg (.col (4400+bit) false)))
  rw [table] at hc
  have hv := hc (List.mem_append_right _ (List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩))
  change tr.cell t r (1440+bit) + -tr.cell t r (4400+bit) = 0 at hv
  have eq : tr.cell t r (1440+bit) = tr.cell t r (4400+bit) := by grind
  rw [eq]

theorem sha512_combined_message_binding (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512RoundW (sha512CombinedRoundRow (tr.cell t r)) = (sha512CombinedWindow (tr.cell t r)).headD 0 := by
  have roundH := sha512_combined_round_holds air tr pub t ht table holds
  have rowH := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl roundH r hr
  have eq := sha512_round_add_bits _ rowH 3 4 (by decide) (by decide)
  have link := sha512_combined_word_bits air tr pub t ht table holds r hr
  change sha512RoundW (sha512CombinedRoundRow (tr.cell t r)) = sha512BitsWord (tr.cell t r) 1440
  simp only [sha512RoundAddBase,Nat.reduceMul,Nat.reduceAdd,sha512CombinedProjection,
    sha512BitsWord,sha512CombinedRoundRow,←Nat.add_assoc,Nat.reduceAdd] at eq link ⊢
  exact eq.trans link.symm

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem sha512_combined_table_wf : sha512CombinedTable.wf ⟨[sha512CombinedTable],0,0⟩ 3=true := by decide

set_option maxRecDepth 65536 in
theorem sha512_combined_table_size :
    sha512CombinedTable.width=5152 ∧ sha512CombinedTable.constraints.length=6848 := by decide

/-- The current round consumes the current authenticated window head. -/
theorem sha512_combined_output (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512CombinedOutput (tr.cell t r) = round (sha512CombinedVars (tr.cell t r))
      (sha512CombinedK (tr.cell t r)) ((sha512CombinedWindow (tr.cell t r)).headD 0) := by
  have roundH := sha512_combined_round_holds air tr pub t ht table holds
  have rowH := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl roundH r hr
  have result := (sha512_round_full_output _ rowH).symm
  change sha512CombinedOutput (tr.cell t r) = round (sha512CombinedVars (tr.cell t r))
    (sha512CombinedK (tr.cell t r)) (sha512RoundW (sha512CombinedRoundRow (tr.cell t r))) at result
  rw [sha512_combined_message_binding air tr pub t ht table holds r hr] at result
  exact result

/-- Simultaneous actual schedule and round evolution; k remains a free per-row input. -/
theorem sha512_combined_recurrence (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512CombinedTable)
    (holds : Holds air pub tr) (r : Nat) (next : r+1<tr.height t) :
    sha512CombinedVars (tr.cell t (r+1)) = round (sha512CombinedVars (tr.cell t r))
      (sha512CombinedK (tr.cell t r)) ((sha512CombinedWindow (tr.cell t r)).headD 0) ∧
    sha512CombinedWindow (tr.cell t (r+1)) = nextWindow (sha512CombinedWindow (tr.cell t r)) := by
  have roundH := sha512_combined_round_holds air tr pub t ht table holds
  have scheduleH := sha512_combined_schedule_holds air tr pub t ht table holds
  have rlink := sha512_sequence_state_link _ _ pub 0 (by decide) rfl roundH r next
  have wlink := sha512_schedule_window_recurrence _ _ pub 0 (by decide) rfl scheduleH r next
  constructor
  · change sha512CombinedVars (tr.cell t (r+1)) = sha512CombinedOutput (tr.cell t r) at rlink
    rw [rlink]
    exact sha512_combined_output air tr pub t ht table holds r (by omega)
  · simpa only [sha512CombinedWindow,sha512CombinedProjection,Nat.zero_add] using wlink

/-- Both families of temporal links vanish at the final row. The current-row
message-consumption wire remains enforced there. -/
theorem sha512_combined_final (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (last : r+1=tr.height t) :
    (∀ e ∈ instructionSequenceConstraints sha512ScheduleWindowPairs, e.eval tr t r pub=0) ∧
    (∀ e ∈ instructionSequenceConstraints sha512RoundSequencePairs,
      (sha512RelocateExpr 2544 e).eval tr t r pub=0) := by
  constructor
  · intro e he
    exact sha512_window_final tr pub t r last e he
  · intro e he
    rw [sha512_combined_relocate_eval]
    exact sha512_sequence_final _ pub 0 r last e he

end NearCompression
