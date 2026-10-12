import ZkFormal.NearV3.Sched.Gen.Codec
import ZkFormal.NearV3.Candidates.SchedSetAll
import ZkFormal.NearV3.Candidates.SchedField
import ZkFormal.NearV3.Candidates.ProcKeyInverse
import ZkFormal.NearV3.Sched.Complete.Cmp

/-!
# Honest rows of the frozen codec table `Sched.Codec.table` (table 11): assignments

Row assignments (column ↦ value lists, read through `SchedSetAll.lookup`) of the four row kinds of
one scheduler instance: header (`hdrA`), record (`recA`, with the allowance-field accumulators as
explicit parameters), sanity-hash (`hashA`) and `sha256(all_shards)` (`ashA`) rows; the values follow
the frozen generator `Gen.codecRows`.  `modE`: the eight constraints that hold only modulo `P`
(the six `isZ` inverse tests, `nzb = bpre·ib`, the `wt` shift); every other constraint vanishes
over the integers on the honest rows.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

/-- The register columns, as literals. -/
@[simp] theorem reg_0 : reg 0 = 24 := rfl
@[simp] theorem reg_1 : reg 1 = 25 := rfl
@[simp] theorem reg_2 : reg 2 = 26 := rfl
@[simp] theorem reg_3 : reg 3 = 30 := rfl
@[simp] theorem reg_4 : reg 4 = 31 := rfl
@[simp] theorem reg_5 : reg 5 = 33 := rfl
@[simp] theorem reg_6 : reg 6 = 36 := rfl
@[simp] theorem reg_7 : reg 7 = 37 := rfl
@[simp] theorem reg_8 : reg 8 = 39 := rfl
@[simp] theorem reg_9 : reg 9 = 41 := rfl
@[simp] theorem reg_10 : reg 10 = 42 := rfl
@[simp] theorem reg_11 : reg 11 = 59 := rfl
@[simp] theorem reg_12 : reg 12 = 61 := rfl
@[simp] theorem reg_13 : reg 13 = 62 := rfl
@[simp] theorem reg_14 : reg 14 = 63 := rfl
@[simp] theorem reg_15 : reg 15 = 71 := rfl
@[simp] theorem reg_16 : reg 16 = 72 := rfl
@[simp] theorem reg_17 : reg 17 = 66 := rfl
@[simp] theorem reg_18 : reg 18 = 67 := rfl
@[simp] theorem reg_19 : reg 19 = 50 := rfl
@[simp] theorem reg_20 : reg 20 = 51 := rfl
@[simp] theorem reg_21 : reg 21 = 52 := rfl
@[simp] theorem reg_22 : reg 22 = 35 := rfl
@[simp] theorem reg_23 : reg 23 = 40 := rfl
@[simp] theorem reg_24 : reg 24 = 58 := rfl
@[simp] theorem reg_25 : reg 25 = 60 := rfl
@[simp] theorem reg_26 : reg 26 = 78 := rfl
@[simp] theorem reg_27 : reg 27 = 87 := rfl
@[simp] theorem reg_28 : reg 28 = 88 := rfl
@[simp] theorem reg_29 : reg 29 = 89 := rfl
@[simp] theorem reg_30 : reg 30 = 90 := rfl
@[simp] theorem reg_31 : reg 31 = 53 := rfl

/-- `finv`, folded: the honest inverse cells.  Irreducible, so that numeral simprocs never try to
evaluate a field inverse of a symbolic value. -/
@[irreducible] def inv (x : Nat) : Nat := finv x

theorem inv_eq (x : Nat) : inv x = finv x := by unfold inv; rfl

/-- Instance constants of one codec block. -/
structure Inst where
  tv : Nat
  n : Nat
  N : Nat
  pres : Bool
  vid : Nat
  base : Nat
  fair : Nat

/-- `[τ = 0]`: the forwarding rows of instance 0. -/
def zt0 (I : Inst) : Nat := if I.tv = 0 then 1 else 0

theorem zt0_le (I : Inst) : zt0 I ≤ 1 := by unfold zt0; split <;> omega

theorem tv_zt0 (I : Inst) : (I.tv : Int) * (zt0 I : Int) = 0 := by
  unfold zt0; split <;> simp_all

def instA (I : Inst) : List (Nat × Nat) :=
  [(act, 1), (tau, I.tv), (pres, b2n I.pres), (vid, I.vid), (nn, I.n), (NN, I.N),
   (base, I.base), (fair, I.fair), (itz, inv I.tv), (zt, zt0 I)]

def pbits (x : Nat) : List (Nat × Nat) := (List.range 8).map fun i => (pbit i, bit x i)
def qbits (x : Nat) : List (Nat × Nat) := (List.range 8).map fun i => (prbit i, bit x i)

/-- Header bytes `[0, N₀, N₁, 0, 0]` and the register contents (header, base, fair bytes). -/
def hdrBytes (I : Inst) : List Nat := [0, I.N % 256, I.N / 256 % 256, 0, 0]
def params (I : Inst) : List Nat := hdrBytes I ++ bytesLE I.base 3 ++ bytesLE I.fair 3

def regA (vals : Nat → Nat) : List (Nat × Nat) := (List.range 32).map fun i => (reg i, vals i)

/-- Header row `p < 5`. -/
def hdrA (I : Inst) (p : Nat) : List (Nat × Nat) :=
  let bp := (hdrBytes I).getD p 0
  instA I ++ [(kH, 1), (kF, if p = 0 then 1 else 0), (pos, p), (bpost, bp),
    (bpre, if I.pres then bp else 0), (vbg, b2n I.pres), (ihp, inv (fsub p 4)),
    (ehp, if p = 4 then 1 else 0)] ++ regA (fun i => (params I).getD (p + i) 0) ++ pbits bp ++
    qbits (if I.pres then bp else 0)

theorem zev_col (Z : ZEnv) (c : Nat) (nx : Bool) :
    zev Z (.col c nx) = if nx then (Z.nxt c : Int) else (Z.cur c : Int) := rfl

theorem bool_ite (p : Prop) [Decidable p] :
    ((if p then 1 else 0 : Nat) : Int) * (((if p then 1 else 0 : Nat) : Int) - 1) = 0 := by
  split <;> rfl

theorem int_bool {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (x - 1) = 0 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> rfl

/-- The eight constraints that hold only modulo `P` on honest rows. -/
def modE : List Expr :=
  (isZ (c kR) (sub (c g) (k 7)) ig7 e7).take 1 ++
  (isZ (c fA) (sub (c g) (k 2)) ig2 e2).take 1 ++
  (isZ (c kR) (sub (c kidx) (sub (c NN) (k 1))) ikl ekl).take 1 ++
  (isZ (c kH) (sub (c pos) (k 4)) ihp ehp).take 1 ++
  (isZ (.add (c kZ) (c kA)) (sub (c sj) (.add (k 31) (smul 32 (c kA)))) isj esj).take 1 ++
  (isZ (c act) (c tau) itz zt).take 1 ++
  [ .mul (c fA) (sub (c nzb) (.mul (c bpre) (c ib))),
    .mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt))) ]

/-- Per-link data of one record (link `kk`). -/
structure Rec where
  kk : Nat
  srcS : Nat
  hasC : Bool
  useC : Bool
  al : Bool
  a0s : Nat
  gb : Nat
  afin : Nat
  gfin : Nat
  ft : Nat
  /-- the inverse cell `(kk − (N − 1))⁻¹` (honest value `finv (fsub kk (N − 1))`) -/
  iklv : Nat

def apRv (R : Rec) : Nat := R.a0s % 16777216
def bigRv (R : Rec) : Nat := if 16777216 ≤ R.a0s then 1 else 0
def cbv (I : Inst) (R : Rec) : Nat := if MA ≤ apRv R + I.fair then 1 else 0
def a1v (I : Inst) (R : Rec) : Nat :=
  if bigRv R = 1 then MA else if cbv I R = 1 then MA else apRv R + I.fair

theorem a1v_def (I : Inst) (R : Rec) :
    a1v I R = if bigRv R = 1 then MA else if cbv I R = 1 then MA else apRv R + I.fair := rfl

theorem cbv_le (I : Inst) (R : Rec) : cbv I R ≤ 1 := by unfold cbv; split <;> omega
theorem bigRv_le (R : Rec) : bigRv R ≤ 1 := by unfold bigRv; split <;> omega

/-- Record row `(f, gg)` of link `R.kk`: post byte `bpo`, pre byte `bpr`, allowance-field
accumulators `apv, apostv, bigv` (before this row). -/
def recA (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv : Nat) : List (Nat × Nat) :=
  instA I ++ [(kR, 1), (pos, 5 + 24 * R.kk + 8 * f + gg), (bpost, bpo), (bpre, bpr),
    (vbg, b2n I.pres), (kidx, R.kk), (klo, R.kk % 256), (khi, R.kk / 256),
    (fS, if f = 0 then 1 else 0), (fR, if f = 1 then 1 else 0), (fA, if f = 2 then 1 else 0),
    (g, gg), (ig7, inv (fsub gg 7)), (e7, if gg = 7 then 1 else 0),
    (ikl, R.iklv), (ekl, if R.kk + 1 = I.N then 1 else 0)] ++
  pbits bpo ++ qbits bpr ++
  [(rs, if f = 0 ∧ gg = 0 then 1 else 0), (al, b2n R.al), (gb, R.gb), (srcC, R.srcS),
    (hasC, b2n R.hasC), (useC, b2n R.useC)] ++
  (if f = 2 ∧ 2 ≤ gg then [(apR, apRv R), (bigR, bigRv R)] else []) ++
  (if f = 2 then [(lowf, if gg < 3 then 1 else 0), (wt, 256 ^ gg % 2013265921), (ap, apv), (big, bigv),
    (apost, apostv), (nzb, if bpr = 0 then 0 else 1), (ib, inv bpr), (ig2, inv (fsub gg 2)),
    (e2, if gg = 2 then 1 else 0)] else []) ++
  (if f = 2 ∧ gg = 2 then [(a0g, b2n R.hasC), (cx, apRv R + I.fair), (cy, MA), (cbit, cbv I R),
    (cg, 1)] else []) ++
  (if f = 2 ∧ 2 ≤ gg then [(cb, cbv I R)] else []) ++
  (if f = 2 ∧ gg = 7 then [(rend, 1), (bF, if bigv = 1 ∨ bpr ≠ 0 then 1 else 0), (a1, a1v I R),
    (a2, a1v I R - b2n R.al * I.base), (g2, b2n R.al * I.base), (afin, R.afin), (gfin, R.gfin),
    (u0g, b2n R.useC), (fwg, zt0 I), (cx, zt0 I * (R.gfin + R.gb)), (cy, zt0 I * R.ft),
    (cbit, zt0 I), (cg, zt0 I), (pm0, zt0 I * (R.kk % 256)), (pm1, zt0 I * (R.kk / 256)),
    (fb 0, zt0 I * (R.ft % 256)), (fb 1, zt0 I * (R.ft / 256 % 256)),
    (fb 2, zt0 I * (R.ft / 65536 % 256))] else [])

/-- Sanity-hash row `j < 32`: digest `dig`, prior hash `hpre`. -/
def hashA (I : Inst) (dig hpre : List Nat) (j : Nat) : List (Nat × Nat) :=
  let bpr := if I.pres then hpre.getD j 0 else 0
  instA I ++ [(kZ, 1), (dgg, if j = 0 then 1 else 0), (pos, 5 + 24 * I.N + j), (sj, j),
    (bpost, dig.getD j 0), (bpre, bpr), (bsha, bpr), (vbg, b2n I.pres), (isj, inv (fsub j 31)),
    (esj, if j = 31 then 1 else 0)] ++ regA (fun i => dig.getD (j + i) 0) ++ pbits (dig.getD j 0) ++
    qbits bpr

/-- `sha256(all_shards)` row `j < 32`. -/
def ashA (I : Inst) (ash : List Nat) (j : Nat) : List (Nat × Nat) :=
  instA I ++ [(kA, 1), (pos, 5 + 24 * I.N + 32 + j), (sj, 32 + j), (bsha, ash.getD j 0),
    (pm0, j), (pm1, ash.getD j 0), (isj, inv (fsub (32 + j) 63)), (esj, if j = 31 then 1 else 0)]

/- The integer pass: every non-modular constraint vanishes over the integers, for a row whose cells
are `hcur` and whose successor's cells are `hnxt` (both by `lookup`). -/
set_option hygiene false in
macro "codec_int" : tactic => `(tactic| (
  simp only [constraints, cKind, cRec, cTrl, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map, List.forall_mem_nil, boolCols, recBoolCols, isZ, instCols,
    List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil]
  repeat' apply And.intro
  all_goals first
    | (intro h; refine absurd ?_ h; simp [modE, isZ]; done)
    | (intro _
       try simp only [zev_c, zev_n, zev_k, zev_add, zev_mul, zev_sub, zev_smul, zev_neg, mul3, notE,
         encG, pbitsE, oE, aLE, ftE, gT, Table.boolC, ZkFormal.Chacha.Rng.Table.num, zev_sum, zev,
         hcur, hnxt]
       try simp only [zev, zev_col, zev_sum, zev_add, zev_mul, zev_smul, zev_neg, zev_sub, zev_k, ZkFormal.Chacha.Rng.Table.num, List.sum_cons, List.sum_nil, hcur, hnxt, List.foldl_cons, List.foldl_nil, List.range_zero, List.map_cons,
         List.map_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ,
         ite_true, ite_false, Bool.false_eq_true, Nat.reduceEqDiff, Int.mul_zero, Int.zero_mul,
         Int.sub_self, Int.add_zero, Int.zero_add, false_and, and_false, true_and, and_true,
         Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, not_false_eq_true, not_true_eq_false, ne_eq,
         reduceIte, false_or, or_false, true_or, or_true, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd,
         Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.add_zero, Nat.zero_add, Nat.div_one,
         Int.natCast_one, Int.natCast_zero, Int.one_mul, Int.mul_one, hdrA, recA, hashA, ashA, instA, regA, pbits,
         qbits, params, hdrBytes, bytesLE, lookup, bit, List.range_succ, List.foldl_append,
         List.map_append, act, kH, kR, kZ, kA, kF, tau, pos, pres, vid, nn, NN, base, fair, bpre, bpost,
         pbit, kidx, klo, khi, fS, fR, fA, g, ig7, e7, ig2, e2, lowf, wt, ap, big, ib, nzb, apost, ikl,
         ekl, ihp, ehp, sj, isj, esj, bsha, fb, al, a1, cb, afin, gfin, gb, itz, zt, cx, cy, cbit, cg,
         rend, a2, g2, vbg, fwg, pm0, pm1, dgg, bF, srcC, apR, hasC, bigR, rs, a0g, u0g, useC,
         prbit, Nat.add_assoc, reg_0, reg_1, reg_2, reg_3, reg_4, reg_5, reg_6, reg_7, reg_8, reg_9, reg_10, reg_11, reg_12, reg_13, reg_14, reg_15, reg_16, reg_17, reg_18, reg_19, reg_20, reg_21, reg_22, reg_23, reg_24, reg_25, reg_26, reg_27, reg_28, reg_29, reg_30, reg_31]
       all_goals first
         | omega
         | (simp only [bool_ite, Int.one_mul, Int.mul_zero]; done)
         | (simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]; split <;> simp)
         | (simp [*]; done)
         | (simp [*] <;> omega)
         | (apply int_bool <;> omega)
         | (cases I.pres <;> simp [b2n] <;> omega)
         | (apply int_bool <;> cases I.pres <;> simp [b2n] <;> omega)
         | ((repeat' split) <;> omega)
         | ((repeat' split) <;> simp <;> omega)
         | (apply int_bool <;> (repeat' split) <;> omega)
         | (cases hh : R.hasC <;> simp [b2n, hh, *] <;> omega)
         | (cases hh : I.pres <;> simp [b2n, hh, *] <;> omega)
         | (apply int_bool <;> (repeat' split) <;> simp)
         | (apply int_bool <;> cases R.hasC <;> simp [b2n] <;> omega)
         | (apply int_bool <;> cases R.useC <;> simp [b2n] <;> omega)
         | (apply int_bool <;> cases R.al <;> simp [b2n] <;> omega)
         | (cases R.al <;> simp [b2n, *] <;> (repeat' split) <;> omega)
         | ((try simp only [*]) <;> cases I.pres <;> simp [b2n] <;> omega))))

end ZkFormal.NearV3.Render.Cdc
