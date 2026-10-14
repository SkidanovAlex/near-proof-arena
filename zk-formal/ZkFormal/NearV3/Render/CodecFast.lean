import ZkFormal.NearV3.Render.CodecIntList

/-!
# `codec_fast`: the integer pass of the codec rows, with the row cells evaluated once

`codec_int` (`CodecDefs`) re-unfolds the row tables (`hdrA`, `recA`, …) and re-evaluates `lookup` in
every one of the 239 constraints of every row case (one `simp` per constraint, each rebuilding a
~200-lemma simp set), decides membership in `modE` by a full `simp` per constraint, and unfolds `zev`
by its definitional equations, which the kernel re-checks by unfolding the structural recursion of
`zev`.  `codec_fast` proves the same goals (same statements; only the tactic of `CodecHeader`,
`CodecRecInt`, `CodecEndInt` changes):

* `int_of_cInt` (`CodecIntList`): the goal becomes `AllI Z cIntT`, one conjunct `IdxP i (zev Z e = 0)`
  per integer constraint (the `modE` ones are discharged there once and for all);
* `cdc_rows`: the row tables of `hcur`/`hnxt` are unfolded once, and every cell value is read off
  once, as hypotheses `hc_i : Z.cur i = vᵢ`, `hn_i : Z.nxt i = vᵢ'` (`i < 91`), each proved by
  `lookup_of_lastFind0` with a kernel-evaluated `rfl` that compares column literals only (the cell
  values are carried, never reduced);
* `cdc_allsimp`: one `simp` over all the conjuncts, with the propositional (non-`rfl`) equations
  `zq_*` for `zev` (so the kernel checks rewrites instead of unfolding `zev`) and the cells; the
  constraints that vanish identically disappear;
* `cdc_dispatch`: each residual goal `IdxP i Q` is closed by `codec_int`'s cascade (`cdc_cascade`),
  trying first the alternatives recorded for index `i` on the honest rows (`cdcPref`).

docs/logs/v3-elab-budget-2026-10.md has the measurements.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

/-! ## `zev` by propositional equations -/

section
variable (Z : ZEnv)
theorem zq_c (x : Nat) : zev Z (ZkFormal.Chacha.Table.E.c x) = (Z.cur x : Int) :=
  (rfl : zev Z (ZkFormal.Chacha.Table.E.c x) = _).trans rfl
theorem zq_n (x : Nat) : zev Z (ZkFormal.Chacha.Table.E.n x) = (Z.nxt x : Int) :=
  (rfl : zev Z (ZkFormal.Chacha.Table.E.n x) = _).trans rfl
theorem zq_k (v : Nat) : zev Z (ZkFormal.Chacha.Table.E.k v) = (v : Int) :=
  (rfl : zev Z (ZkFormal.Chacha.Table.E.k v) = _).trans rfl
theorem zq_const (v : Nat) : zev Z (.const v) = (v : Int) := (rfl : zev Z (.const v) = _).trans rfl
theorem zq_colF (x : Nat) : zev Z (.col x false) = (Z.cur x : Int) :=
  (rfl : zev Z (.col x false) = _).trans rfl
theorem zq_colT (x : Nat) : zev Z (.col x true) = (Z.nxt x : Int) :=
  (rfl : zev Z (.col x true) = _).trans rfl
theorem zq_add (a b : Expr) : zev Z (.add a b) = zev Z a + zev Z b :=
  (rfl : zev Z (.add a b) = _).trans rfl
theorem zq_mul (a b : Expr) : zev Z (.mul a b) = zev Z a * zev Z b :=
  (rfl : zev Z (.mul a b) = _).trans rfl
theorem zq_neg (a : Expr) : zev Z (.neg a) = - zev Z a := (rfl : zev Z (.neg a) = _).trans rfl
theorem zq_smul (v : Nat) (e : Expr) : zev Z (ZkFormal.Chacha.Table.E.smul v e) = (v : Int) * zev Z e :=
  (rfl : zev Z (ZkFormal.Chacha.Table.E.smul v e) = _).trans rfl
theorem zq_isFirst : zev Z .isFirst = Z.first := (rfl : zev Z .isFirst = _).trans rfl
theorem zq_isLast : zev Z .isLast = Z.last := (rfl : zev Z .isLast = _).trans rfl
theorem zq_isTransition : zev Z .isTransition = 1 - Z.last := (rfl : zev Z .isTransition = _).trans rfl
end

/-! ## Reading a cell of an explicit row -/

/-- The last pair with key `c` (the one `lookup` returns), by `Nat.beq` on the keys only. -/
def lastFind (c : Nat) : List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | p :: ps => match lastFind c ps with
    | some q => some q
    | none => bif Nat.beq p.1 c then some p else none

theorem lookup_cons_eq (p : Nat × Nat) (ps : List (Nat × Nat)) (c d : Nat) :
    lookup (p :: ps) c d = lookup ps c (if p.1 = c then p.2 else d) := rfl

theorem lookup_lastFind (L : List (Nat × Nat)) (c d : Nat) :
    lookup L c d = ((lastFind c L).map Prod.snd).getD d := by
  induction L generalizing d with
  | nil => rfl
  | cons p ps ih =>
    rw [lookup_cons_eq, ih]
    simp only [lastFind]
    cases lastFind c ps with
    | some q => rfl
    | none =>
      cases hb : Nat.beq p.1 c
      · have h := Nat.ne_of_beq_eq_false hb
        simp [h]
      · have h := Nat.eq_of_beq_eq_true hb
        simp [h]

theorem lookup_of_lastFind {L : List (Nat × Nat)} {c v : Nat} (d : Nat)
    (h : lastFind c L = some (c, v)) : lookup L c d = v := by
  rw [lookup_lastFind, h]; rfl

/-- A cell of an explicit row, absent keys included (the default pair `(c, 0)` comes first, so it
is found only when `c` is not a key of `L`). -/
theorem lookup_of_lastFind0 {L : List (Nat × Nat)} {c v : Nat}
    (h : lastFind c ((c, 0) :: L) = some (c, v)) : lookup L c 0 = v := by
  have e : lookup ((c, 0) :: L) c 0 = lookup L c 0 := by rw [lookup_cons_eq]; simp
  rw [← e]; exact lookup_of_lastFind 0 h

/-! ## The tactic -/

set_option hygiene false in
/-- Unfold the rows of `hcur`/`hnxt` and read every cell once (`hc_i`, `hn_i`). -/
macro "cdc_rows" : tactic => do
  let mut ts : Array (Lean.TSyntax `tactic) := #[]
  ts := ts.push (← `(tactic| simp only [hdrA, recA, hashA, ashA, instA, regA, pbits,
    qbits, params, hdrBytes, bytesLE, bit, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.map_append,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, ite_true, ite_false, Nat.reduceEqDiff,
    Nat.reduceLeDiff, Nat.reduceLT, and_true, true_and, and_false, false_and, reduceIte,
    Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.add_zero,
    Nat.zero_add, Nat.div_one,
    act, kH, kR, kZ, kA, kF, tau, pos, pres, vid, nn, NN, base, fair, bpre, bpost,
    pbit, kidx, klo, khi, fS, fR, fA, g, ig7, e7, ig2, e2, lowf, wt, ap, big, ib, nzb, apost, ikl,
    ekl, ihp, ehp, sj, isj, esj, bsha, fb, al, a1, cb, afin, gfin, gb, itz, zt, cx, cy, cbit, cg,
    rend, a2, g2, vbg, fwg, pm0, pm1, dgg, bF, srcC, apR, hasC, bigR, rs, a0g, u0g, useC,
    prbit, Nat.add_assoc, reg_0, reg_1, reg_2, reg_3, reg_4, reg_5, reg_6, reg_7, reg_8, reg_9, reg_10,
    reg_11, reg_12, reg_13, reg_14, reg_15, reg_16, reg_17, reg_18, reg_19, reg_20, reg_21, reg_22,
    reg_23, reg_24, reg_25, reg_26, reg_27, reg_28, reg_29, reg_30, reg_31] at hcur hnxt))
  for i in [0:91] do
    for (h, p) in [(Lean.mkIdent `hcur, "hc_"), (Lean.mkIdent `hnxt, "hn_")] do
      let nm := Lean.mkIdent (Lean.Name.mkSimple s!"{p}{i}")
      let lit := Lean.Syntax.mkNumLit (toString i)
      ts := ts.push (← `(tactic| have $nm:ident := ($h:ident $lit).trans (lookup_of_lastFind0 rfl)))
  `(tactic| ($ts*))

/-- Rewrite every tagged integer constraint (`AllI Z cIntT`) with the cells `hc_i`, `hn_i`, in one
pass; the constraints that vanish identically disappear (`idx_true`), the others stay tagged. -/
macro "cdc_allsimp" : tactic => do
  let mut args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for i in [0:91] do
    for p in ["hc_", "hn_"] do
      args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(Lean.mkIdent (Lean.Name.mkSimple s!"{p}{i}")):ident))
  `(tactic| simp (maxSteps := 4000000) only [AllI, cIntT, idx_true, zq_const, zq_colF, zq_colT, zq_add, zq_mul,
    zev_sub, zq_smul, zq_neg, zq_isFirst, zq_isLast, zq_isTransition,
    ite_true, ite_false, Bool.false_eq_true, Nat.reduceEqDiff, Int.mul_zero, Int.zero_mul,
    Int.sub_self, Int.add_zero, Int.zero_add, false_and, and_false, true_and, and_true,
    Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, not_false_eq_true, not_true_eq_false, ne_eq,
    reduceIte, false_or, or_false, true_or, or_true, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.add_zero, Nat.zero_add, Nat.div_one,
    Int.natCast_one, Int.natCast_zero, Int.one_mul, Int.mul_one, Nat.add_assoc, $args,*])

/-- Drop the cells (and the row hypotheses) before the closing cascade, so that `omega` and `simp [*]`
see the same context as in `codec_int`, minus the row hypotheses. -/
macro "cdc_clear" : tactic => do
  let mut ids : Array Lean.Ident := #[Lean.mkIdent `hcur, Lean.mkIdent `hnxt]
  for i in [0:91] do
    for p in ["hc_", "hn_"] do
      ids := ids.push (Lean.mkIdent (Lean.Name.mkSimple s!"{p}{i}"))
  `(tactic| clear $ids*)

/-- The closing alternatives of `codec_int`, numbered in `codec_int`'s order. -/
syntax "cdc_alt " num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| cdc_alt 1) => `(tactic| omega)
  | `(tactic| cdc_alt 2) => `(tactic| (simp only [bool_ite, Int.one_mul, Int.mul_zero]; done))
  | `(tactic| cdc_alt 3) => `(tactic| (simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]; split <;> simp))
  | `(tactic| cdc_alt 4) => `(tactic| (simp [*]; done))
  | `(tactic| cdc_alt 5) => `(tactic| (simp [*] <;> omega))
  | `(tactic| cdc_alt 6) => `(tactic| (apply int_bool <;> omega))
  | `(tactic| cdc_alt 7) => `(tactic| (cases I.pres <;> simp [b2n] <;> omega))
  | `(tactic| cdc_alt 8) => `(tactic| (apply int_bool <;> cases I.pres <;> simp [b2n] <;> omega))
  | `(tactic| cdc_alt 9) => `(tactic| ((repeat' split) <;> omega))
  | `(tactic| cdc_alt 10) => `(tactic| ((repeat' split) <;> simp <;> omega))
  | `(tactic| cdc_alt 11) => `(tactic| (apply int_bool <;> (repeat' split) <;> omega))
  | `(tactic| cdc_alt 12) => `(tactic| (cases hh : R.hasC <;> simp [b2n, hh, *] <;> omega))
  | `(tactic| cdc_alt 13) => `(tactic| (cases hh : I.pres <;> simp [b2n, hh, *] <;> omega))
  | `(tactic| cdc_alt 14) => `(tactic| (apply int_bool <;> (repeat' split) <;> simp))
  | `(tactic| cdc_alt 15) => `(tactic| (apply int_bool <;> cases R.hasC <;> simp [b2n] <;> omega))
  | `(tactic| cdc_alt 16) => `(tactic| (apply int_bool <;> cases R.useC <;> simp [b2n] <;> omega))
  | `(tactic| cdc_alt 17) => `(tactic| (apply int_bool <;> cases R.al <;> simp [b2n] <;> omega))
  | `(tactic| cdc_alt 18) => `(tactic| (cases R.al <;> simp [b2n, *] <;> (repeat' split) <;> omega))
  | `(tactic| cdc_alt 19) => `(tactic| ((try simp only [*]) <;> cases I.pres <;> simp [b2n] <;> omega))

/-- `codec_int`'s closing cascade. -/
macro "cdc_cascade" : tactic => `(tactic| first
    | cdc_alt 1
    | cdc_alt 2
    | cdc_alt 3
    | cdc_alt 4
    | cdc_alt 5
    | cdc_alt 6
    | cdc_alt 7
    | cdc_alt 8
    | cdc_alt 9
    | cdc_alt 10
    | cdc_alt 11
    | cdc_alt 12
    | cdc_alt 13
    | cdc_alt 14
    | cdc_alt 15
    | cdc_alt 16
    | cdc_alt 17
    | cdc_alt 18
    | cdc_alt 19)

/-- For the constraint at index `i` of `constraints`: the alternatives of the cascade that close it on
the honest codec rows (recorded on every row case of `CodecHeader`, `CodecRecInt`, `CodecEndInt`), most
frequent first.  They are tried first (each must close the goal); the whole cascade follows, so the
table only orders the search. -/
def cdcPref : List (Nat × List Nat) :=
  [(6, [7]), (12, [2]), (14, [2]), (15, [6, 4]), (16, [4, 6]), (17, [4]), (19, [7]), (20, [4]), (21, [2]), (23, [6, 4]), (24, [6, 4]), (25, [6, 4]), (26, [6, 4]), (27, [6, 4]), (28, [6, 4]), (29, [6, 4]), (30, [6, 4]), (31, [6, 4]), (32, [6, 4]), (33, [6, 4]), (34, [6, 4]), (35, [6, 4]), (36, [6, 4]), (37, [6, 4]), (38, [6, 4]), (40, [9]), (41, [17]), (42, [4, 6]), (43, [2]), (44, [12]), (45, [4, 6]), (49, [1]), (51, [1]), (59, [9, 5]), (65, [1, 4]), (68, [1]), (77, [1]), (78, [4]), (79, [1]), (80, [1, 4, 7, 9]), (81, [13, 7, 4]), (87, [1]), (88, [1]), (89, [1]), (90, [1]), (92, [4, 7]), (126, [1]), (129, [1]), (130, [1]), (135, [4]), (141, [4]), (142, [4]), (143, [5]), (145, [5]), (147, [9]), (148, [1]), (154, [4]), (155, [4]), (156, [18]), (158, [1]), (159, [1]), (161, [9]), (164, [4]), (171, [12]), (172, [12]), (178, [1]), (183, [9]), (184, [4]), (185, [1]), (186, [1]), (187, [1]), (189, [4]), (190, [4, 5]), (191, [4]), (196, [1]), (197, [4]), (198, [4]), (200, [1]), (201, [1]), (206, [4]), (207, [4])]

set_option hygiene false in
/-- Close one residual goal `IdxP i Q`: by its index, the recorded alternatives (`cdcPref`, each must
close the goal), then the whole cascade. -/
macro "cdc_dispatch" : tactic => do
  let mut close ← `(tactic| (refine IdxP.mk ?_; cdc_cascade))
  for (i, ks) in cdcPref.reverse do
    let mut c ← `(tactic| cdc_cascade)
    for k in ks.reverse do
      let lit := Lean.Syntax.mkNumLit (toString k)
      let rest := #[c]
      c ← `(tactic| first | (cdc_alt $lit; done) | ($rest*))
    let il := Lean.Syntax.mkNumLit (toString i)
    let cs := #[c]
    let rest := #[close]
    close ← `(tactic| first | (refine @IdxP.mk $il _ ?_; $cs*) | ($rest*))
  pure close

set_option hygiene false in
/-- The integer pass (`codec_int`'s goal: `∀ e ∈ constraints, e ∉ modE → zev Z e = 0`, with `hcur`,
`hnxt` the row assignments): to the tagged list (`int_of_cInt`), cells read once (`cdc_rows`), all
constraints rewritten in one `simp` (`cdc_allsimp`), and the residual goals closed by `codec_int`'s
cascade, recorded alternatives first (`cdc_dispatch`). -/
macro "codec_fast" : tactic => `(tactic| (
  apply int_of_cInt
  cdc_rows
  cdc_allsimp
  all_goals cdc_clear
  all_goals repeat' apply And.intro
  all_goals cdc_dispatch))

end ZkFormal.NearV3.Render.Cdc
