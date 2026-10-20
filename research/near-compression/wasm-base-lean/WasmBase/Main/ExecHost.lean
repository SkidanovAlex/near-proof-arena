import WasmBase.Main.Exec
import WasmBase.Main.HostLinks
import WasmBase.Main.RowHostSpec
/-!
# WasmBase.Main.ExecHost — the bus decomposition for `wasmBaseHostAir` (piece 2)

`wasmBaseHostAir nloc ngl = wasmBaseAir nloc ngl ++ [HOST, HOSTO, HOSTT]`, so every bus of a host
trace is the base trace's messages **plus** the messages of tables 22/23/24.  This file proves that
decomposition for the buses the execution theorem reads:

* `host_msgs_air`: every bus `b` splits as `msgs wasmBaseAir ++ (HOST ++ HOSTO ++ HOSTT)`;
* `host_occs_air`: the same for the occurrence list;
* `msgs_state_host` / `msgs_ch_host`: the STATE and CH decompositions in the shape
  `Exec.msgs_state` / `Exec.msgs_ch` have for the base AIR.  The HOST row's STATE interactions are
  the standard `pc`/`pc + 1` pair (`host_part_state_T` / `host_part_state_F`), and its CH messages
  are the row's `rowMsgs … busStk` (`host_part_ch_recv` / `host_part_ch_send` decode them to
  `rowCons`/`rowProd`);
* `host_part_nil_env`: the response oracle (23) and the cached host table (24) carry no STATE or CH
  interaction, so they contribute nothing to those two buses;
* `host_arg_stack` / `host_word_stack`: the two halves of piece 1 (live arguments, response word)
  restated at the trace/`RelW` boundary.

## One caveat that affects the remaining induction

The HOST row's CH **receives** are counted with `pf j`, not `act · pf j` (`host_inters_stk`; the
constraint list `Host.constraints` has no `act`–`pf` link).  So an **inactive** HOST row
(`act = 0`) with `pf 0 = 1` still emits two count-1 CH *receives* (and one CH send gated by
`nres`, which is also unconstrained by `act`).  Consequently:

* `ChipFacts.inactive` for the base chips (the statement "an inactive row has no count-1
  interaction") **does not hold** for table 22 as the HOST table is currently constrained; the
  decomposition `msgs_ch_host` is therefore unconditional (`part Host.table …` on both sides), and
  the `ChanOK` hypothesis of the induction cannot simply be instantiated with
  `cons = actList … ++ HOST rows` — the inactive HOST rows' CH messages would not be cancelled.
* Either (a) the HOST AIR gains `act · (1 − pf j)` padding constraints (the intended gating; then
  `inactive`-style reasoning works and the induction is the base one plus table 22), or (b) the
  correctness statement restricts the trace to host traces in which every inactive HOST row has
  `pf 0 = pf 1 = 0` (a trace-level side condition, easy to state, less faithful to the AIR).

## The remaining statement (the induction)

The induction `exec_of_rows` re-run for the host AIR, threading `S_seg`/`segb`.  Every base row
keeps the segment (`RowSpec`'s `RelW` at `S_seg segb`); each HOST row restarts it
(`(S_seg, segb) ↦ (S + fee, g_after)`, `StepHost.host_seg`).  The honest statement is:

```
theorem wasm_base_exec_host (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    (CF : ChipFacts X nloc ngl pub tr) (CH : HostChipFacts X nloc ngl pub tr)
    (HOK : HostOK tr resp) (HR : HostResp resp)
    (hfeeN : …) (hg64 : X.g0 < 2 ^ 64) (init : …) :
    ∃ sN segs, runHost … = .fin sN ∧ sN.frames = [] ∧
      -- the final segment is `(S_final, g_final)` from the last HOST row (or `(0, g0)` if none)
      (segs = [] → X.R * S_final + sN.gas.g = X.g0) ∧
      (∀ (S_seg segb) ∈ segs, X.R * (S_final - S_seg) + sN.gas.g = segb)
```

where `HostChipFacts` = `ChipFacts` with the `rows` field extended by `host_rowspec` at table 22
(and `inactive`/`counts` extended with the gating caveat above).  What is already available:

* `host_rowspec` (the HOST row's `RowSpec` at the trace level) and `RowHostSpec.host_arg_stack` /
  `host_word_stack` (piece 1 at the `RelW` boundary);
* `StepHost.step_host_ok` / `step_host_ok_seg` / `host_seg` (the spec step and its successor
  segment) and `Main.Host.host_row_seg` (the row's successor segment from `HostOK`);
* `host_msgs_air`, `msgs_state_host`, `msgs_ch_host`, `host_occs_air` (the bus decomposition).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The table split -/

/-- Every bus of the host AIR is the base AIR's plus the HOST, HOSTO and HOSTT parts. -/
theorem host_msgs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseHostAir nloc ngl) tr pub b s =
      msgs (wasmBaseAir nloc ngl) tr pub b s ++
      (part Host.table tr pub 22 b s ++ (part HostO.table tr pub 23 b s ++
        (part HostTab.table tr pub 24 b s ++ part HostB.table tr pub 25 b s))) := by
  rw [msgs_flatMap, msgs_flatMap]
  have e : (wasmBaseHostAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [Host.table, HostO.table, HostTab.table, HostB.table] := rfl
  rw [e, List.zipIdx_append]
  simp only [List.flatMap_append, List.length_map, air_len, Nat.zero_add, part, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.zipIdx_cons, Nat.reduceAdd]
  rw [show ([].zipIdx 26 : List (Table × Nat)) = [] from rfl]
  simp only [List.flatMap_nil, List.append_nil]

/-- The occurrence list of the host AIR is the base AIR's plus the HOST table's. -/
theorem host_occs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) :
    occs (wasmBaseHostAir nloc ngl) tr pub =
      occs (wasmBaseAir nloc ngl) tr pub ++
      ((List.range (tr.height 22)).flatMap fun r => rowOccs Host.table tr pub 22 r) ++
      (((List.range (tr.height 23)).flatMap fun r => rowOccs HostO.table tr pub 23 r) ++
        (((List.range (tr.height 24)).flatMap fun r => rowOccs HostTab.table tr pub 24 r) ++
          ((List.range (tr.height 25)).flatMap fun r => rowOccs HostB.table tr pub 25 r))) := by
  unfold occs
  have e : (wasmBaseHostAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [Host.table, HostO.table, HostTab.table, HostB.table] := rfl
  rw [e, List.zipIdx_append]
  simp only [List.flatMap_append, List.length_map, air_len, Nat.zero_add, List.zipIdx_cons,
    List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowOccs, Nat.reduceAdd]
  have h0 : ([].zipIdx 26 : List (Table × Nat)) = [] := rfl
  simp only [show ([].zipIdx 26 : List (Table × Nat)) = [] from rfl, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-! ## The HOST row's STATE messages -/

theorem rowMsgs_host_state (tr : Trace) (pub : List F) (r : Nat) :
    rowMsgs Host.table tr pub 22 r busState true =
      (if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) ∧
    rowMsgs Host.table tr pub 22 r busState false =
      (if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  have h1 : Host.inters.filter (fun i => i.bus = busState ∧ i.send = true) =
      [Host.inters.getD 1 default] := by
    rw [host_inters_state.2]; rfl
  have h0 : Host.inters.filter (fun i => i.bus = busState ∧ i.send = false) =
      [Host.inters.getD 0 default] := by
    rw [host_inters_state.1]; rfl
  constructor
  · rw [rowMsgs_single Host.table tr pub 22 r busState true _ h1]; unfold rowAct rowOut; rfl
  · rw [rowMsgs_single Host.table tr pub 22 r busState false _ h0]; unfold rowAct rowIn; rfl

/-- The HOST table's STATE sends: the active rows' outputs, in order. -/
theorem host_part_state_T (tr : Trace) (pub : List F) :
    part Host.table tr pub 22 busState true =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) := by
  unfold part
  congr 1
  funext r
  rw [(rowMsgs_host_state tr pub r).1]

/-- The HOST table's STATE receives: the active rows' inputs, in order. -/
theorem host_part_state_F (tr : Trace) (pub : List F) :
    part Host.table tr pub 22 busState false =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  unfold part
  congr 1
  funext r
  rw [(rowMsgs_host_state tr pub r).2]

/-! ## The oracle and the cached host table carry no STATE or CH interaction -/

theorem host_part_nil_env {nloc ngl : Nat} (tr : Trace) (pub : List F) (b : Nat) (s : Bool)
    (hb : b = busState ∨ b = busStk) :
    part HostO.table tr pub 23 b s = [] ∧ part HostTab.table tr pub 24 b s = [] ∧
      part HostB.table tr pub 25 b s = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold part; rw [List.flatMap_eq_nil_iff]; intro r _)
  · rw [rowMsgs_eq]
    rcases hb with rfl | rfl <;> cases s <;>
      simp [HostO.table, busState, busStk, busR16, busHostQ, busHostR]
  · rw [rowMsgs_eq]
    rcases hb with rfl | rfl <;> cases s <;>
      simp [HostTab.table, busState, busStk, busR16, busHostT, busHostQ, busHostR, busHostB]
  · rw [rowMsgs_eq]
    rcases hb with rfl | rfl <;> cases s <;>
      simp only [HostB.table, HostB.inters, List.filter_cons, List.filter_nil,
        List.flatMap_cons, List.flatMap_nil] <;>
      (first | rfl | (rw [if_neg (by decide)]; rfl) | (rw [if_pos (by decide)]; intro h; exact absurd h (by decide)))

/-! ## The STATE and CH messages of a host trace -/

/-- The STATE bus of a host trace: base boundary + base instruction rows, then the HOST rows. -/
theorem msgs_state_host {nloc ngl : Nat} (tr : Trace) (pub : List F) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busState true =
      msgs (wasmBaseAir nloc ngl) tr pub busState true ++
        (List.range (tr.height 22)).flatMap (fun r =>
          if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busState false =
      msgs (wasmBaseAir nloc ngl) tr pub busState false ++
        (List.range (tr.height 22)).flatMap (fun r =>
          if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  have h := host_part_nil_env (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · obtain ⟨e1, e2, e3⟩ := h busState true (Or.inl rfl)
    rw [host_msgs_air, e1, e2, e3, host_part_state_T]
    simp
  · obtain ⟨e1, e2, e3⟩ := h busState false (Or.inl rfl)
    rw [host_msgs_air, e1, e2, e3, host_part_state_F]
    simp

/-- The CH bus of a host trace: base boundary + base instruction rows, then the HOST rows' messages
(`rowMsgs … busStk`), on each side. -/
theorem msgs_ch_host {nloc ngl : Nat} (tr : Trace) (pub : List F) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busStk true =
      msgs (wasmBaseAir nloc ngl) tr pub busStk true ++
        part Host.table tr pub 22 busStk true ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busStk false =
      msgs (wasmBaseAir nloc ngl) tr pub busStk false ++
        part Host.table tr pub 22 busStk false := by
  have h := host_part_nil_env (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · obtain ⟨e1, e2, e3⟩ := h busStk true (Or.inr rfl)
    rw [host_msgs_air, e1, e2, e3]
    simp
  · obtain ⟨e1, e2, e3⟩ := h busStk false (Or.inr rfl)
    rw [host_msgs_air, e1, e2, e3]
    simp

/-! ## The HOST rows' CH messages, decoded -/

/-- The decoded CH receives of a HOST row are its `rowCons` (definitional). -/
theorem host_row_recv_eq (tr : Trace) (pub : List F) (r : Nat) :
    (rowMsgs Host.table tr pub 22 r busStk false).map decMsg = rowCons Host.table tr pub 22 r := rfl

/-- The decoded CH sends of a HOST row are its `rowProd` (definitional). -/
theorem host_row_send_eq (tr : Trace) (pub : List F) (r : Nat) :
    (rowMsgs Host.table tr pub 22 r busStk true).map decMsg = rowProd Host.table tr pub 22 r := rfl

/-- The HOST table's CH receives, decoded, row by row. -/
theorem host_part_ch_recv (tr : Trace) (pub : List F) :
    (part Host.table tr pub 22 busStk false).map decMsg =
      (List.range (tr.height 22)).flatMap fun r => rowCons Host.table tr pub 22 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-- The HOST table's CH sends, decoded, row by row. -/
theorem host_part_ch_send (tr : Trace) (pub : List F) :
    (part Host.table tr pub 22 busStk true).map decMsg =
      (List.range (tr.height 22)).flatMap fun r => rowProd Host.table tr pub 22 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-- `flatMap` congruence when the functions are pointwise equal on the list. -/
theorem flatMap_congr_on {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## A trace-level side condition making the HOST rows behave like chips

As noted above, the HOST table's CH receives use `pf j` rather than `act · pf j`, so an inactive
row can still carry count-1 CH messages.  `HostTraceOK` is the exact trace-level condition under
which inactive HOST rows carry **no** CH interaction, i.e. under which the decomposition is the
base one plus the active HOST rows.  (Alternatively the AIR gains `act · (1 − pf j)` and
`act · (1 − nres)` padding constraints; then `HostTraceOK` follows from `Holds`.) -/

/-- No inactive HOST row carries a CH message (all `pf j` and `nres` are zero off the active rows). -/
def HostTraceOK (tr : Trace) (pub : List F) : Prop :=
  ∀ r, r < tr.height 22 → ¬ rowAct Host.table tr pub 22 r →
    rowNat tr 22 r (Host.pf 0) = 0 ∧ rowNat tr 22 r (Host.pf 1) = 0 ∧ rowNat tr 22 r Host.nres = 0

/-- Under `HostTraceOK`, `rowCons` vanishes on inactive HOST rows. -/
theorem host_row_cons_inactive {tr : Trace} {pub : List F} {r : Nat}
    (h0 : rowNat tr 22 r (Host.pf 0) = 0) (h1 : rowNat tr 22 r (Host.pf 1) = 0) :
    rowCons Host.table tr pub 22 r = [] := by
  rw [host_row_cons (by omega) (by omega), h0, h1]
  rfl

/-- Under `HostTraceOK`, `rowProd` vanishes on inactive HOST rows. -/
theorem host_row_prod_inactive {tr : Trace} {pub : List F} {r : Nat}
    (hn : rowNat tr 22 r Host.nres = 0) :
    rowProd Host.table tr pub 22 r = [] := by
  rw [host_row_prod, if_neg (by omega)]

/-- **The CH receives of a host trace, restricted to active HOST rows.**  Under `HostTraceOK` the
inactive rows contribute nothing, so the decoded CH receives are the active HOST rows' arguments
(the base rows' contribution is `msgs wasmBaseAir …` of `msgs_ch_host`). -/
theorem host_part_ch_recv_active {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HT : HostTraceOK tr pub) :
    (part Host.table tr pub 22 busStk false).map decMsg =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then
          ((if rowNat tr 22 r (Host.pf 0) = 1 then [argMsg tr r 0] else []) ++
           (if rowNat tr 22 r (Host.pf 1) = 1 then [argMsg tr r 1] else []))
        else []) := by
  rw [host_part_ch_recv]
  refine flatMap_congr_on _ _ _ ?_
  intro r hr
  rw [List.mem_range] at hr
  by_cases ha : rowAct Host.table tr pub 22 r
  · rw [if_pos ha]
    obtain ⟨hb0, hb1⟩ := host_pf_bits H hr ha
    exact host_row_cons hb0 hb1
  · obtain ⟨h0, h1, hn⟩ := HT r hr ha
    rw [if_neg ha, host_row_cons_inactive h0 h1]

/-- **The CH sends of a host trace, restricted to active HOST rows.** -/
theorem host_part_ch_send_active {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HT : HostTraceOK tr pub) :
    (part Host.table tr pub 22 busStk true).map decMsg =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then
          (if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else []) else []) := by
  rw [host_part_ch_send]
  refine flatMap_congr_on _ _ _ ?_
  intro r hr
  rw [List.mem_range] at hr
  by_cases ha : rowAct Host.table tr pub 22 r
  · rw [if_pos ha, host_row_prod]
  · obtain ⟨h0, h1, hn⟩ := HT r hr ha
    rw [if_neg ha, host_row_prod_inactive hn]

/-! ## The HOST rows' arguments as live stack messages (piece 1 composed with the trace)

The two halves of `RESULTS.md` §3.1 compose here: an active HOST row whose STATE input is the one a
`RelW` is related to consumes exactly its `argMsg`s (`RowHostSpec.cons`), and those are the live
stack messages at slots `size − np + j` (`host_arg_view` + `host_arg_slot`). -/

/-- **The consumed arguments are live stack messages.**  For an active HOST row at the STATE input
of a `RelW`-related state, each present argument message is one of the messages in `stackView`. -/
theorem host_arg_stack {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {tr : Trace} {r j : Nat} (hr : r < tr.height 22)
    (hsb : rowNat tr 22 r Host.kSb = E.sb) (h3 : rowNat tr 22 r cH = s.stack.size - E.sb)
    (hnp : rowNat tr 22 r Host.np ≤ s.stack.size) (hj : j < rowNat tr 22 r Host.np) (hj2 : j < 2)
    (hin : live (argMsg tr r j)) :
    argMsg tr r j ∈ stackView s.stack tps :=
  (host_arg_view R (host_arg_slot R hsb h3 hnp hj2) hj hnp hin).1

/-- **The produced result word is the response's.**  The `HOSTR` result message of an active row
with `ar = 1` is the encoding of the response's single result word as an `i64`. -/
theorem host_word_stack {nloc ngl : Nat} {pub : List F} {tr : Trace} {resp : Nat → HostAnswer}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HOK : HostOK tr resp)
    (hsend : ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 22) (hact : rowAct Host.table tr pub 22 r) {ts : Nat}
    (har : rowNat tr 22 r Host.ar = 1) (hnw : (resp ts).results.length = 1) :
    wordMsg tr r = enc 0 (hostSlot tr r 0) (.i64 (UInt64.ofNat ((resp ts).results.headD 0)))
      (rowNat tr 22 r cTs) :=
  host_word_is_resp H HOK hsend hr hact har hnw

end WasmBase
