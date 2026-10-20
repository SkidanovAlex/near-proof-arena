import WasmBase.Main.Host
import WasmBase.Main.HostLinks
/-!
# WasmBase.Main.RowHostSpec — the HOST row's `RowSpec` (piece 1 of `RESULTS.md` §3)

The HOST row (table 22) carries two kinds of CH (`busStk`) interaction:

* up to `Host.nArgs = 9` **argument receives** `stkRecv (sb + h − np + j) tagP[j] P[j] tP[j] pf[j]`
  (`j ∈ Host.argRange`) — the arguments of the host call, popped from the operand stack in argument
  order;
* one **result send** `stkSend (sb + h − np) 1 rb[0..3] ts nres` — the single result word, pushed
  back at the stack base of the call.

This file turns those interactions into the two facts `results/pq-host-gas/RESULTS.md` §3 asks for:

* `host_row_cons` / `host_row_prod`: the row's consumed / produced messages are exactly the
  argument messages `argMsg` and the result message `wordMsg` (the `stkRecv`/`stkSend` shape);
* `host_arg` : a consumed message, in a `RelW`-related state, is the live stack message the Wasm
  side **sent** — slot `size − np + j`, carrying the stack entry at that slot (piece 1(a));
* `host_word`: the produced message is exactly the response's result word (`HostOK.word`), an `i64`
  at slot `size − np` (piece 1(b));
* `HostRowSpec`: the packaged row predicate, proved from `Holds` + `host_rowfacts` + `HostOK`
  (`host_rowspec`);
* `host_step_spec`: the `RowSpec`-shaped spec step of an active HOST row — the segment-restarting
  analogue of `RowSpec` (`RowSpec` keeps the segment; a host call resets it to `(S + fee, g_after)`).

Piece 2 (the bus decomposition of `Exec.lean` repeated for `wasmBaseHostAir`) is *not* in this
file; its exact remaining statements are recorded in `Main/ExecHost.lean`'s header.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-! ## The HOST table's STATE and CH interactions, by direction -/

theorem host_inters_state :
    (Host.inters.filter (fun i => i.bus = busState ∧ i.send = false)) =
      [stateIn (v cPc) (v cTs) (v cS) (v Host.kSb) (v Host.kCid) (v Host.act)] ∧
    (Host.inters.filter (fun i => i.bus = busState ∧ i.send = true)) =
      [stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * v Host.st) (v Host.kSb) (v Host.kCid)
        (v Host.act)] := by
  constructor <;> decide

theorem host_inters_stk :
    (Host.inters.filter (fun i => i.bus = busStk ∧ i.send = false)) =
      (Host.argRange.flatMap fun j =>
        [stkRecv (Host.sbNew + Expr.c j) (v (Host.tagP j)) (limbsOf (Host.P j)) (v (Host.tP j))
          (v (Host.pf j))]) ∧
    (Host.inters.filter (fun i => i.bus = busStk ∧ i.send = true)) =
      [stkSend Host.sbNew 1 (limbsOf Host.rb) (v cTs) (v Host.nres)] := by
  constructor <;> decide

/-! ## The argument and result messages of the row -/

/-- The slot of the HOST row's `j`-th argument: `sb + h − np + j`, read off the row's cells. -/
def hostSlot (tr : Trace) (r j : Nat) : Nat :=
  (tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) +
    ((j : Nat) : F)).toNat

/-- The HOST row's `j`-th argument as a channel message: the stack slot `sb + h − np + j`. -/
def argMsg (tr : Trace) (r j : Nat) : Msg :=
  ⟨0, hostSlot tr r j, rowNat tr 22 r (Host.tagP j), rowNat tr 22 r (Host.P j),
   rowNat tr 22 r (Host.P j + 1), rowNat tr 22 r (Host.P j + 2), rowNat tr 22 r (Host.P j + 3),
   rowNat tr 22 r (Host.tP j)⟩

/-- The HOST row's result word as a channel message: the stack slot `sb + h − np`, tag `1` (the
spec's `pushRet` pushes an `i64`). -/
def wordMsg (tr : Trace) (r : Nat) : Msg :=
  ⟨0, hostSlot tr r 0, 1, rowNat tr 22 r Host.rb, rowNat tr 22 r (Host.rb + 1),
   rowNat tr 22 r (Host.rb + 2), rowNat tr 22 r (Host.rb + 3), rowNat tr 22 r cTs⟩

theorem hostSlot_lt (tr : Trace) (r j : Nat) : hostSlot tr r j < P := by
  simp only [hostSlot]; exact Fp.toNat_lt _

theorem hostSlot_cast (tr : Trace) (r j : Nat) :
    ((hostSlot tr r j : Nat) : F) =
      tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) + ((j : Nat) : F) := by
  rw [hostSlot, Fp.cast_toNat]

/-- The un-decoded argument message of the row (the shape `rowMsgs` produces). -/
def argRaw (tr : Trace) (r j : Nat) : List F :=
  [((0 : Nat) : F), tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) +
      ((j : Nat) : F),
   ((rowNat tr 22 r (Host.tagP j) : Nat) : F), ((rowNat tr 22 r (Host.P j) : Nat) : F),
   ((rowNat tr 22 r (Host.P j + 1) : Nat) : F), ((rowNat tr 22 r (Host.P j + 2) : Nat) : F),
   ((rowNat tr 22 r (Host.P j + 3) : Nat) : F), ((rowNat tr 22 r (Host.tP j) : Nat) : F)]

/-- The un-decoded result message of the row. -/
def wordRaw (tr : Trace) (r : Nat) : List F :=
  [((0 : Nat) : F), tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F),
   ((1 : Nat) : F), ((rowNat tr 22 r Host.rb : Nat) : F), ((rowNat tr 22 r (Host.rb + 1) : Nat) : F),
   ((rowNat tr 22 r (Host.rb + 2) : Nat) : F), ((rowNat tr 22 r (Host.rb + 3) : Nat) : F),
   ((rowNat tr 22 r cTs : Nat) : F)]

theorem decMsg_argRaw (tr : Trace) (r j : Nat) : decMsg (argRaw tr r j) = argMsg tr r j := by
  simp only [decMsg, argRaw, argMsg, hostSlot, List.getD_cons_zero, List.getD_cons_succ,
    Fp.toNat_cast_of_lt (show (0 : Nat) < P by decide),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.tagP j)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.P j)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.P j + 1)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.P j + 2)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.P j + 3)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.tP j))]

theorem decMsg_wordRaw (tr : Trace) (r : Nat) : decMsg (wordRaw tr r) = wordMsg tr r := by
  simp only [decMsg, wordRaw, wordMsg, hostSlot, List.getD_cons_zero, List.getD_cons_succ,
    Fp.toNat_cast_of_lt (show (0 : Nat) < P by decide),
    Fp.toNat_cast_of_lt (show (1 : Nat) < P by decide),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.rb)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.rb + 1)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.rb + 2)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.rb + 3)),
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r cTs)]
  congr 1
  rw [show tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) + ((0 : Nat) : F) =
    tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) from by
      rw [cast_zero]; grind]

/-- The decoded shape of one `stkRecv` when its count is 1: `argRaw`. -/
theorem single_recv {pub : List F} {tr : Trace} {r j : Nat} :
    ([stkRecv (Host.sbNew + Expr.c j) (v (Host.tagP j)) (limbsOf (Host.P j)) (v (Host.tP j))
        (v (Host.pf j))] : List Inter).filterMap
      (fun i => if (i.count.eval (tr.row pub 22 r)).toNat = 1 then
        some (i.msg.map (·.eval (tr.row pub 22 r))) else none)
    = (if rowNat tr 22 r (Host.pf j) = 1 then [argRaw tr r j] else []) := by
  simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, limbsOf, List.range,
    List.range.loop, List.cons_append, List.nil_append, List.map_cons, List.map_nil, v,
    Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_c, cell_cast,
    Trace.row, cH, Host.sbNew, Host.np, Host.pf, argRaw]
  have hpf : Fp.toNat (↑(rowNat tr 22 r (19 + j)) : Fp) = rowNat tr 22 r (19 + j) :=
    Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (19 + j))
  rw [hpf]
  by_cases g : rowNat tr 22 r (19 + j) = 1 <;>
    simp only [g, ite_true, ite_false, Nat.add_zero]

theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The raw `rowMsgs` shape of the row's CH receives: one `argRaw` per present argument. -/
theorem host_rawCons {pub : List F} {tr : Trace} {r : Nat} :
    rowMsgs Host.table tr pub 22 r busStk false =
      Host.argRange.flatMap fun j =>
        (if rowNat tr 22 r (Host.pf j) = 1 then [argRaw tr r j] else []) := by
  simp only [Host.table]
  rw [rowMsgs_eq, host_inters_stk.1, List.filterMap_flatMap]
  exact flatMap_congr' _ _ _ (fun j _ => single_recv)

/-- The raw `rowMsgs` shape of the row's CH send. -/
theorem host_rawProd {pub : List F} {tr : Trace} {r : Nat} :
    rowMsgs Host.table tr pub 22 r busStk true =
      (if rowNat tr 22 r Host.nres = 1 then [wordRaw tr r] else []) := by
  simp only [Host.table]
  rw [rowMsgs_eq, host_inters_stk.2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    List.filterMap_cons, List.filterMap_nil, stkSend, chSend, limbsOf, List.range, List.range.loop,
    List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat',
    cell_cast, Trace.row, cTs, Host.sbNew, Host.rb, Host.nres, Host.np, Expr.eval_c, Nat.reduceAdd, Nat.add_zero,
    wordRaw]
  rw [Fp.toNat_cast_of_lt (rowNat_lt tr 22 r 10)]
  by_cases g0 : rowNat tr 22 r 10 = 1 <;>
    simp only [g0, ite_true, ite_false, List.map_cons, List.map_nil]

/-- Every argument-present flag of an active HOST row is a bit. -/
theorem host_pf_bits {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) :
    ∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) ≤ 1 := by
  intro j hj
  have RF := host_rowfacts H hr hact
  have b := bool_nat (rowNat_lt tr 22 r (Host.pf j)) (RF.pfBit j hj)
  rcases b with h | h <;> omega

/-- One argument slot's messages, decoded. -/
theorem map_decMsg_single {tr : Trace} {r j : Nat} :
    List.map decMsg (if rowNat tr 22 r (Host.pf j) = 1 then [argRaw tr r j] else []) =
      (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else []) := by
  by_cases g : rowNat tr 22 r (Host.pf j) = 1
  · rw [if_pos g, if_pos g, List.map_cons, List.map_nil, decMsg_argRaw]
  · rw [if_neg g, if_neg g]
    rfl

/-- `rowMsgs` mapped through `decMsg` distributes over `flatMap`, pointwise. -/
theorem map_decMsg_flatMap {tr : Trace} {r : Nat} :
    (Host.argRange.flatMap fun j =>
        (if rowNat tr 22 r (Host.pf j) = 1 then [argRaw tr r j] else [])).map decMsg =
      Host.argRange.flatMap fun j =>
        (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else []) := by
  rw [List.map_flatMap]
  exact flatMap_congr' _ _ _ (fun j _ => map_decMsg_single)

/-- The row's consumed messages: the present arguments, in order. -/
theorem host_row_cons {pub : List F} {tr : Trace} {r : Nat} :
    rowCons Host.table tr pub 22 r =
      Host.argRange.flatMap fun j =>
        (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else []) := by
  unfold rowCons
  rw [host_rawCons]
  exact map_decMsg_flatMap

/-- The row's produced messages: the result word iff `nres = 1`. -/
theorem host_row_prod {pub : List F} {tr : Trace} {r : Nat} :
    rowProd Host.table tr pub 22 r =
      (if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else []) := by
  unfold rowProd
  rw [host_rawProd]
  by_cases g0 : rowNat tr 22 r Host.nres = 1 <;>
    simp only [g0, ite_true, ite_false, List.map_cons, List.map_nil, List.map_append, decMsg_wordRaw]

/-! ## The consumed arguments are the live stack messages the Wasm side sent

The HOST row's `j`-th argument sits at stack slot `sb + h − np + j`; with `RelW.height` (`h =
size − sb`) that is `size − np + j`.  Under `live` it is exactly the channel message of the stack
entry at that slot (`RelW.stack_msg`), i.e. one of the messages `stackView` produces. -/

/-- The operand stack of a `RelW`-related state is bounded by the frame base and the static height:
`s.size < 2^28 + 2^16`, in particular shorter than the field modulus. -/
theorem RelW.size_bound {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb) :
    s.stack.size < 2 ^ 28 + 2 ^ 16 := by
  have hb := (X.factsOf R.kLt).hBound pc R.pcLt
  have hh := R.height
  rw [hh] at hb
  simp only [Option.getD_some] at hb
  have h1 := R.sbLt
  have h2 := R.sbLe
  omega

theorem RelW.size_lt {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb) :
    s.stack.size < P := by
  have hP' := P_val
  have := R.size_bound
  omega

/-- The argument slot in a `RelW`-related state: `size − np + j`.  The hypotheses are exactly
`RelW.height` (`h = size − sb`), `RelW.base` (`sb_row = E.sb`) and `RelW.sbLe`. -/
theorem host_arg_slot {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {tr : Trace} {r j : Nat} (hsb : rowNat tr 22 r Host.kSb = E.sb)
    (h3 : rowNat tr 22 r cH = s.stack.size - E.sb) (hle : rowNat tr 22 r Host.np ≤ s.stack.size)
    (hj : j < Host.nArgs) :
    hostSlot tr r j = s.stack.size - rowNat tr 22 r Host.np + j := by
  have hP' := P_val
  have hsz := R.sbLe
  have hzP : s.stack.size < P := R.size_lt
  have hsbP : E.sb < P := by have := R.sbLt; omega
  have hnpP : rowNat tr 22 r Host.np < P := rowNat_lt tr 22 r _
  show (tr.cell 22 r Host.kSb + tr.cell 22 r cH - ((rowNat tr 22 r Host.np : Nat) : F) +
    ((j : Nat) : F)).toNat = _
  have e1 : tr.cell 22 r Host.kSb = ((E.sb : Nat) : F) := by rw [cell_cast, hsb]
  have e2 : tr.cell 22 r cH = ((s.stack.size - E.sb : Nat) : F) := by rw [cell_cast, h3]
  rw [e1, e2]
  have e3 : ((E.sb : Nat) : F) + ((s.stack.size - E.sb : Nat) : F) = ((s.stack.size : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_add, Nat.add_sub_cancel' hsz]
  rw [e3]
  have e4 : ((s.stack.size : Nat) : F) - ((rowNat tr 22 r Host.np : Nat) : F) + ((j : Nat) : F) =
      ((s.stack.size - rowNat tr 22 r Host.np : Nat) : F) + ((j : Nat) : F) := by
    have hsub : ((s.stack.size : Nat) : F) =
        ((s.stack.size - rowNat tr 22 r Host.np : Nat) : F) + ((rowNat tr 22 r Host.np : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel hle]
    rw [hsub]; grind
  rw [e4, ← Lean.Grind.Semiring.natCast_add,
    Fp.toNat_cast_of_lt (show s.stack.size - rowNat tr 22 r Host.np + j < P by
      have h1 := R.size_bound
      have hn : Host.nArgs = 9 := rfl
      rw [hn] at hj
      omega)]

/-- **Piece 1(a).**  A consumed argument message of an active HOST row (the `j`-th with
`j < np`), when live, is one of the live stack messages (`stackView`) of the state the row is
related to, namely the encoding of the stack entry at slot `size − np + j`. -/
theorem host_arg_view {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {tr : Trace} {r j : Nat} (hslot : hostSlot tr r j = s.stack.size - rowNat tr 22 r Host.np + j)
    (hj : j < rowNat tr 22 r Host.np) (hle : rowNat tr 22 r Host.np ≤ s.stack.size)
    (hin : live (argMsg tr r j)) :
    argMsg tr r j ∈ stackView s.stack tps ∧
      argMsg tr r j = enc 0 (s.stack.size - rowNat tr 22 r Host.np + j)
        (s.stack[s.stack.size - rowNat tr 22 r Host.np + j]?.getD default)
        (tps (s.stack.size - rowNat tr 22 r Host.np + j)) := by
  have hlt : (argMsg tr r j).slot < s.stack.size := by
    rw [show (argMsg tr r j).slot = hostSlot tr r j from rfl, hslot]; omega
  have e0 := R.stack_msg hin (show (argMsg tr r j).space = 0 from rfl) hlt
  have e : argMsg tr r j = enc 0 (s.stack.size - rowNat tr 22 r Host.np + j)
      (s.stack[s.stack.size - rowNat tr 22 r Host.np + j]?.getD default)
      (tps (s.stack.size - rowNat tr 22 r Host.np + j)) := by
    rw [← hslot]; exact e0
  have hlt' : s.stack.size - rowNat tr 22 r Host.np + j < s.stack.size := by
    have := hlt
    rw [show (argMsg tr r j).slot = hostSlot tr r j from rfl, hslot] at this
    exact this
  exact ⟨mem_stackView.mpr ⟨_, hlt', e⟩, e⟩

/-! ## The produced result word is the response's

The HOST row sends `stkSend (sb + h − np) 1 rb[0..3] ts nres`; `HostOK.word` binds the response's
result word to the `rb` limbs, the tag is `1` (the spec's `pushRet` pushes an `i64`), and the `rb`
limbs are 16-bit (`host_rb_limb`, from the R16 queries of the HOST row). -/

/-- **Piece 1(b).**  The produced message is the encoding of the response's result word as an `i64`
(the spec's `pushRet` truncates to 64 bits), when the row reports one result (`ar = nres = 1`). -/
theorem host_word_is_resp {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {resp : Nat → HostAnswer} (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HOK : HostOK tr resp)
    (hsend : ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 22) (hact : rowAct Host.table tr pub 22 r) {ts : Nat}
    (har : rowNat tr 22 r Host.ar = 1) (hnw : (resp ts).results.length = 1) :
    wordMsg tr r = enc 0 (hostSlot tr r 0) (.i64 (UInt64.ofNat ((resp ts).results.headD 0)))
      (rowNat tr 22 r cTs) := by
  obtain ⟨w, hwres⟩ : ∃ w, (resp ts).results = [w] := by
    cases h : (resp ts).results with
    | nil => rw [h] at hnw; simp at hnw
    | cons a l =>
      rw [h] at hnw
      simp only [List.length_cons, Nat.succ.injEq] at hnw
      have hl : l = [] := List.eq_nil_of_length_eq_zero hnw
      exact ⟨a, by rw [hl]⟩
  have hw := HOK.word r hr ts
  rw [har] at hw
  rw [if_neg (by decide)] at hw
  rw [hwres] at hw
  simp only [List.cons.injEq, and_true] at hw
  have hlimb : ∀ i, i < 4 → rowNat tr 22 r (Host.rb + i) < 65536 := host_rb_limb H hsend hr hact
  have h0 : rowNat tr 22 r Host.rb < 65536 := hlimb 0 (by decide)
  have h1 : rowNat tr 22 r (Host.rb + 1) < 65536 := hlimb 1 (by decide)
  have h2 : rowNat tr 22 r (Host.rb + 2) < 65536 := hlimb 2 (by decide)
  have h3 : rowNat tr 22 r (Host.rb + 3) < 65536 := hlimb 3 (by decide)
  have hw64 : w < 2 ^ 64 := by rw [hw]; omega
  have e0 : rowNat tr 22 r Host.rb = w % 65536 := by rw [hw]; omega
  have e1 : rowNat tr 22 r (Host.rb + 1) = w / 65536 % 65536 := by rw [hw]; omega
  have e2 : rowNat tr 22 r (Host.rb + 2) = w / 2 ^ 32 % 65536 := by rw [hw]; omega
  have e3 : rowNat tr 22 r (Host.rb + 3) = w / 2 ^ 48 % 65536 := by rw [hw]; omega
  rw [hwres, List.headD_cons]
  show (⟨0, hostSlot tr r 0, 1, rowNat tr 22 r Host.rb, rowNat tr 22 r (Host.rb + 1),
    rowNat tr 22 r (Host.rb + 2), rowNat tr 22 r (Host.rb + 3), rowNat tr 22 r cTs⟩ : Msg) =
    enc 0 (hostSlot tr r 0) (.i64 (UInt64.ofNat w)) (rowNat tr 22 r cTs)
  simp only [enc, vTag, vNum, UInt64.toNat_ofNat', Msg.mk.injEq]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, trivial⟩
  all_goals omega

/-! ## `HostRowSpec`: the row predicate

`HostRowSpec` is the HOST row's `RowSpec` at the trace level: it walks the row's `stkRecv`/`stkSend`
occurrences and records (i) that the consumed messages are exactly the arguments the row requests,
and (ii) that the produced message is exactly the result word the row's `HOSTR` response carries.
The two "live" halves — that the argument messages are the stack messages the Wasm side sent
(`host_arg_view`) and that the result message is the encoding of the response's word
(`host_word_is_resp`) — are separate lemmas, because they quantify over the `RelW`-related state
rather than the trace. -/

/-- The HOST row's trace-level `RowSpec`. -/
structure HostRowSpec (pub : List F) (tr : Trace) (resp : Nat → HostAnswer) (r : Nat) : Prop where
  /-- the row is active -/
  act : rowAct Host.table tr pub 22 r
  /-- the argument-present flags are bits, prefix-closed, and `np` is their sum -/
  npBits : (∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) ≤ 1) ∧
    (∀ j, j + 1 < Host.nArgs → rowNat tr 22 r (Host.pf (j + 1)) ≤ rowNat tr 22 r (Host.pf j)) ∧
    rowNat tr 22 r Host.np = cellSum (rowNat tr 22 r) Host.pf Host.argRange
  /-- `nres = (1 − st)·ar` -/
  nresEq : rowNat tr 22 r Host.nres = (1 - rowNat tr 22 r Host.st) * rowNat tr 22 r Host.ar
  /-- the consumed messages are exactly the present arguments, in argument order -/
  cons : rowCons Host.table tr pub 22 r =
    Host.argRange.flatMap fun j =>
      (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else [])
  /-- the produced message is the result word (exactly one iff `nres = 1`) -/
  prod : rowProd Host.table tr pub 22 r =
    (if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else [])
  /-- the response's status is the row's `st`, and `ar` its result count -/
  respStatus : rowNat tr 22 r Host.st = (resp (rowNat tr 22 r 1)).status
  respAr : rowNat tr 22 r Host.ar = (resp (rowNat tr 22 r 1)).results.length
  /-- the row's `g_after` limbs are the response's budget -/
  respGas : rowNat tr 22 r Host.ga + 65536 * rowNat tr 22 r (Host.ga + 1) +
      65536 ^ 2 * rowNat tr 22 r (Host.ga + 2) + 65536 ^ 3 * rowNat tr 22 r (Host.ga + 3) =
      (resp (rowNat tr 22 r 1)).gAfter
  /-- the result word in the row is the response's -/
  respWord : (resp (rowNat tr 22 r 1)).results =
    (if rowNat tr 22 r Host.ar = 0 then [] else
      [rowNat tr 22 r Host.rb + 65536 * rowNat tr 22 r (Host.rb + 1) +
        65536 ^ 2 * rowNat tr 22 r (Host.rb + 2) + 65536 ^ 3 * rowNat tr 22 r (Host.rb + 3)])

/-- `nres = (1 − st)·ar` from the field equation, for bit `st` and `ar`. -/
theorem nres_from {nres st ar : Nat} (hn : nres < P) (hst : st = 0 ∨ st = 1) (har : ar = 0 ∨ ar = 1)
    (h : (nres : F) - (ar : F) + (st : F) * (ar : F) = 0) :
    nres = (1 - st) * ar := by
  rcases hst with rfl | rfl <;> rcases har with rfl | rfl
  · have e : (nres : F) = ((0 : Nat) : F) := by grind
    have h' := (cast_inj_iff hn (by decide : (0 : Nat) < P)).mp e
    rw [h']
  · have e : (nres : F) = ((1 : Nat) : F) := by grind
    have h' := (cast_inj_iff hn (by decide : (1 : Nat) < P)).mp e
    rw [h']
  · have e : (nres : F) = ((0 : Nat) : F) := by grind
    have h' := (cast_inj_iff hn (by decide : (0 : Nat) < P)).mp e
    rw [h']
  · have e : (nres : F) = ((0 : Nat) : F) := by grind
    have h' := (cast_inj_iff hn (by decide : (0 : Nat) < P)).mp e
    rw [h']

/-- A member of `Host.argRange` is below `Host.nArgs`. -/
theorem argRange_lt {j : Nat} (hj : j ∈ Host.argRange) : j < Host.nArgs := by
  simpa only [Host.argRange, List.mem_range] using hj

/-- `Host.argRange` has nine entries, so a sum of bits over it is below the modulus. -/
theorem argRange_length : Host.argRange.length = Host.nArgs := by
  simp [Host.argRange]

theorem cellSum_argRange_lt {c : Nat → Nat} (hbit : ∀ j ∈ Host.argRange, c (Host.pf j) ≤ 1) :
    cellSum c Host.pf Host.argRange < P := by
  have h := cellSum_le c Host.pf 1 Host.argRange hbit
  have hP' := P_val
  have hn : Host.nArgs = 9 := rfl
  rw [argRange_length, hn] at h
  omega

/-- A prefix-closed bit vector's `j`-th flag is at most its predecessor's, as naturals. -/
theorem host_order_nat {c : Nat → Nat} (rw : Row) (hP : ∀ i, c i < P)
    (hbit : ∀ j, j < Host.nArgs → c (Host.pf j) ≤ 1)
    (h : ∀ j, j + 1 < Host.nArgs → (v (Host.pf (j + 1)) -
      v (Host.pf j) * v (Host.pf (j + 1))).eval (natRow c rw) = 0)
    {j : Nat} (hj : j + 1 < Host.nArgs) :
    c (Host.pf (j + 1)) ≤ c (Host.pf j) := by
  have h' : (v (Host.pf (j + 1)) * (1 - v (Host.pf j))).eval (natRow c rw) = 0 := by
    have h1 := h j hj
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow_cur] at h1 ⊢
    grind
  exact le_of_mulsub hP (hbit (j + 1) (by omega)) (hbit j (by omega)) h'

/-- **The HOST row's `HostRowSpec` from the trace.**  Assembled from `host_rowfacts` (the field
facts of the constraints), `HostOK` (the binding of the response) and the row's message shapes
(`host_row_cons`, `host_row_prod`). -/
theorem host_rowspec {nloc ngl : Nat} {pub : List F} {tr : Trace} {resp : Nat → HostAnswer}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HOK : HostOK tr resp) {r : Nat}
    (hr : r < tr.height 22) (hact : rowAct Host.table tr pub 22 r) :
    HostRowSpec pub tr resp r := by
  have hP' := P_val
  have RF := host_rowfacts H hr hact
  have hpfBit : ∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) ≤ 1 := by
    intro j hj
    rcases bool_nat (rowNat_lt tr 22 r (Host.pf j)) (RF.pfBit j hj) with h | h <;> omega
  have hordNat : ∀ j, j + 1 < Host.nArgs → rowNat tr 22 r (Host.pf (j + 1)) ≤ rowNat tr 22 r (Host.pf j) :=
    fun j hj => host_order_nat (tr.row pub 22 r) (rowNat_lt tr 22 r) hpfBit RF.order hj
  have hnp : rowNat tr 22 r Host.np = cellSum (rowNat tr 22 r) Host.pf Host.argRange :=
    natEq RF.npEq (rowNat_lt tr 22 r Host.np)
      (cellSum_argRange_lt (fun j hj => hpfBit j (argRange_lt hj)))
  have hst := bool_nat (rowNat_lt tr 22 r Host.st) RF.stBit
  have har := bool_nat (rowNat_lt tr 22 r Host.ar) RF.arBit
  have hnr : rowNat tr 22 r Host.nres = (1 - rowNat tr 22 r Host.st) * rowNat tr 22 r Host.ar := by
    have h := RF.nresEq
    change (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
      (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0 at h
    exact nres_from (rowNat_lt tr 22 r Host.nres) hst har h
  refine ⟨hact, ⟨hpfBit, hordNat, hnp⟩, hnr, host_row_cons, host_row_prod,
    ?_, HOK.ar r hr _, HOK.gas r hr _, HOK.word r hr _⟩
  exact HOK.status r hr _

end WasmBase
