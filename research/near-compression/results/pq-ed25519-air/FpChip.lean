import NearSpecV3.Ed25519

/-!
# F_p multiplication chip prototype for `p = 2^255 − 19`

Scope.  A **prototype** of the field-arithmetic chip for a BabyBear-hosted
emulation of `F_p`, `p = 2^255 − 19`, as used by `NearSpecV3.Ed25519`.  It is
*not* wired into a full Ed25519 AIR: it is the `mul` gadget, its trace generator,
its constraint pre-check and its differential-test harness
(`Difftest.lean`, driven by `difftest.py`).

Representation.  `x ∈ [0, p)` is 15 limbs of 17 bits: `x = Σ_{i<15} x_i·B^i`,
`B = 2^17`, so `B^15 = 2^255`.  A row has 149 committed cells:
`a`(15), `b`(15), `q`(15), `r`(15), `d`(29), `cd`(30), `ce`(30).

The row relation.  For `a, b < p` let `ab = a·b`, `q = ab / p`, `r = ab mod p`.
The row proves `ab = q·p + r` with two base-`B` carry chains sharing the reduced
digits `d`:

  (P)  conv_k + cd_k = d_k + B·cd_{k+1},   cd_0 = 0        (k < 29)
  (E)  qp_k + r_k + ce_k = d_k + B·ce_{k+1}, ce_0 = 0      (k < 29)
  (F)  cd_29 = ce_29

where `conv_k = Σ_{i+j=k} a_i·b_j` and `qp_k = Σ_{i+j=k} q_i·p_j`, with `p`'s limbs
`p_0 = B−19`, `p_i = B−1` (`1 ≤ i ≤ 14`) and `r_k = 0` for `k ≥ 15`.

Telescoping each chain (`value_of_chain`, **proved**) gives

  `Σ_{k<29} conv_k B^k + cd_0 = Σ_{k<29} d_k B^k + cd_29·B^29`
  `Σ_{k<29} (qp_k+r_k) B^k + ce_0 = Σ_{k<29} d_k B^k + ce_29·B^29`

Since `Σ conv_k B^k = a·b` and `Σ (qp_k+r_k) B^k = q·p + r` (both exact base-`B`
recombinations), (F) with the zero boundaries yields `a·b = q·p + r`.  With
`r < p` this forces `r = a·b mod p`.

**Status.**  Proved here (axioms `[propext, Quot.sound]`, checked with
`#print axioms`): `B_pow`, `p_limbs`, `value_of_chain`, `value_of_chain0`, and
`mul_identity` — the `a·b = q·p + r` conclusion, *conditional on* the two
recombination hypotheses `RecombineConv`/`RecombineQP`.

*Not* proved, and stated here as open:
* the two exact recombinations `recombine_conv`/`recombine_qp`: they are
  **hypotheses** of `mul_identity`, not theorems.  They are true
  (`Σ_k conv_k B^k = a·b` is just base-`B` convolution), but the general
  identity over 29 coefficients is not yet discharged;
* that `Row.gen` satisfies the constraints (executable trace generator, tested
  against Lean `Nat` arithmetic by `difftest.py`);
* the final `r = a*b % p` characterisation (tested via `FpMul.check`).

No `sorry`, no `native_decide`, no `implemented_by` anywhere in this file.
-/

namespace NearCompression.PqEd25519
namespace FpChip

/-- Limb base. -/
def B : Nat := 2 ^ 17
/-- Number of limbs. -/
def NLIMB : Nat := 15
/-- Number of convolution coefficients (product of two 15-limb values). -/
def NCONV : Nat := 29

theorem B_pow : B ^ NLIMB = 2 ^ 255 := by decide +kernel

/-- Field modulus. -/
def p : Nat := 2 ^ 255 - 19
theorem p_eq_spec : p = NearSpecV3.Ed25519.p := rfl

/-- Limb `i` of `x` in base `B`. -/
def limb (x i : Nat) : Nat := (x / B ^ i) % B

/-- Limbs of `p`. -/
def pLimb (i : Nat) : Nat := if i = 0 then B - 19 else B - 1

/-- `p` really has those limbs.  Kernel-checked. -/
theorem p_limbs : ((List.range NLIMB).map (fun i => pLimb i * B ^ i)).sum = p := by
  decide +kernel

/-- `Σ_{k<n} f k · B^k`, written with `List` so the module needs no Mathlib. -/
def vsum (f : Nat → Nat) (Bc n : Nat) : Nat :=
  ((List.range n).map (fun k => f k * Bc ^ k)).sum

/-- `k`-th convolution coefficient of `a` and `b`. -/
def conv (a b : Nat) (k : Nat) : Nat :=
  ((List.range NLIMB).map (fun i =>
    if k < i then 0 else if k - i < NLIMB then limb a i * limb b (k - i) else 0)).sum

/-- `k`-th coefficient of `q·p`. -/
def qpConv (q : Nat) (k : Nat) : Nat :=
  ((List.range NLIMB).map (fun i =>
    if k < i then 0 else if k - i < NLIMB then limb q i * pLimb (k - i) else 0)).sum

/-- Output limb `k`, zero past the top limb. -/
def rLimb (r k : Nat) : Nat := if k < NLIMB then limb r k else 0

/-! ## Trace generator (untrusted prover) -/

/-- One multiplication row.  The limb vectors are stored as `Nat → Nat`; the
Rust/JSON encoding flattens them (`Row.toCells`). -/
structure Row where
  a : Nat
  b : Nat
  q : Nat
  r : Nat
  d : Nat → Nat
  cd : Nat → Nat
  ce : Nat → Nat

/-- Carry into digit `k` of a base-`B` chain. -/
def chainCarry (f : Nat → Nat) (k : Nat) : Nat :=
  (vsum f B k) / B ^ k

/-- Generate the row for `a·b mod p` by integer arithmetic.  This is the
*prover*; the verifier checks `constraints` and the range bounds only. -/
def Row.gen (a b : Nat) : Row :=
  let ab := a * b
  let q := ab / p
  let r := ab % p
  let cd : Nat → Nat := chainCarry (conv a b)
  let ce : Nat → Nat := chainCarry (fun k => qpConv q k + rLimb r k)
  let d : Nat → Nat := fun k => conv a b k + cd k - B * cd (k + 1)
  { a := a, b := b, q := q, r := r, d := d, cd := cd, ce := ce }

/-! ## Polynomial expressions (AIR style) -/

/-- `v i` = this row's cell `i`.  No next row and no public input are needed. -/
inductive Expr where
  | c : Nat → Expr
  | v : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr

namespace Expr

/-- Evaluate in `Int`, so `sub` is a genuine difference: a violated constraint
cannot be masked by saturating `Nat` subtraction. -/
def evalInt (r : Nat → Nat) : Expr → Int
  | .c n => (n : Int)
  | .v i => (r i : Int)
  | .add e f => evalInt r e + evalInt r f
  | .sub e f => evalInt r e - evalInt r f
  | .mul e f => evalInt r e * evalInt r f

/-- Degree, for `max_constraint_degree`. -/
def degree : Expr → Nat
  | .c _ | .v _ => 1
  | .add e f | .sub e f => max (degree e) (degree f)
  | .mul e f => degree e + degree f

/-- Serialise to JSON in the dialect of
`research/near-compression/wasm-base-lean/Tool.lean` (the Rust interpreter
consumes exactly these four node shapes). -/
def toJson : Expr → String
  | .c n => s!"[\"c\",{n}]"
  | .v i => s!"[\"v\",{i}]"
  | .add a b => s!"[\"+\",{a.toJson},{b.toJson}]"
  | .sub a b => s!"[\"-\",{a.toJson},{b.toJson}]"
  | .mul a b => s!"[\"*\",{a.toJson},{b.toJson}]"

end Expr

namespace Col
-- Column layout (149 cells).
def a : Nat := 0
def b : Nat := 15
def q : Nat := 30
def r : Nat := 45
def d : Nat := 60
def cd : Nat := 89
def ce : Nat := 119
def total : Nat := 149
end Col

/-- First carry chain (P) for digit `k < 29`:
`conv_k + cd_k − d_k − B·cd_{k+1} = 0`. -/
def constraintP (k : Nat) : Expr :=
  let prod := (List.range NLIMB).foldl
    (fun acc i => if k < i then acc else if k - i < NLIMB then
      Expr.add acc (Expr.mul (.v (Col.a + i)) (.v (Col.b + (k - i)))) else acc)
    (.c 0)
  Expr.sub (Expr.sub (Expr.add prod (.v (Col.cd + k))) (.v (Col.d + k)))
    (Expr.mul (.c B) (.v (Col.cd + (k + 1))))

/-- Second carry chain (E) for digit `k < 29`:
`qp_k + r_k + ce_k − d_k − B·ce_{k+1} = 0`. -/
def constraintE (k : Nat) : Expr :=
  let qp := (List.range NLIMB).foldl
    (fun acc i => if k < i then acc else if k - i < NLIMB then
      Expr.add acc (Expr.mul (.v (Col.q + i)) (.c (pLimb (k - i)))) else acc)
    (.c 0)
  let rk := if k < NLIMB then Expr.v (Col.r + k) else Expr.c 0
  Expr.sub (Expr.sub (Expr.add (Expr.add qp rk) (.v (Col.ce + k))) (.v (Col.d + k)))
    (Expr.mul (.c B) (.v (Col.ce + (k + 1))))

/-- The 60 constraints: 29 of (P), 29 of (E), the two zero boundaries and
`cd_29 = ce_29`. -/
def constraints : List Expr :=
  (List.range 29).map constraintP
  ++ (List.range 29).map constraintE
  ++ [ Expr.v (Col.cd + 0), Expr.v (Col.ce + 0)
     , Expr.sub (.v (Col.cd + 29)) (.v (Col.ce + 29)) ]

/-- A row as column → value. -/
def Row.env (w : Row) : Nat → Nat := fun i =>
  if i < 15 then limb w.a i
  else if i < 30 then limb w.b (i - 15)
  else if i < 45 then limb w.q (i - 30)
  else if i < 60 then limb w.r (i - 45)
  else if i < 89 then w.d (i - 60)
  else if i < 119 then w.cd (i - 89)
  else w.ce (i - 119)

/-- Range bounds assumed by the AIR; in a deployment these are range lookups.
The measured maximum carry is `1,966,045 < 2^21` (see `CENSUS.md` §5), so
`2^23` is a safe bound. -/
def Row.rangesOk (w : Row) : Bool :=
  (List.range 15).all (fun i => limb w.a i < B && limb w.b i < B
      && limb w.q i < B && limb w.r i < B)
  && (List.range 29).all (fun k => w.d k < B)
  && (List.range 30).all (fun k => w.cd k < 2 ^ 23 && w.ce k < 2 ^ 23)

/-- Constraint pre-check: all polynomial equations vanish on the row. -/
def Row.constraintsOk (w : Row) : Bool :=
  let e := Row.env w
  constraints.all (fun c => Expr.evalInt e c == 0)

/-- Complete row check (equations + ranges). -/
def Row.check (w : Row) : Bool := w.constraintsOk && w.rangesOk

/-- Domain predicate: both operands are canonical representatives in `[0, p)`.
Without this, `a = p` is representable in 15 limbs and the limb ranges do not
catch it; the `< p` side is essential for the uniqueness step `r = a·b mod p`. -/
def InDomain (a b : Nat) : Bool := a < p && b < p

/-- The chip check for `a·b mod p`: domain, equations and ranges. -/
def FpMul.check (a b : Nat) : Bool := InDomain a b && (Row.gen a b).check

/-! ## The telescoping lemma (proved) -/

/-- **Carry-chain soundness.**  If `L k + c k = R k + B·c (k+1)` for all `k < n`,
then `Σ_{k<n} L k·B^k + c 0 = (Σ_{k<n} R k·B^k) + c n·B^n`.

This is the step that turns the limbwise equations (P)/(E) into an identity over
the integers, with no subtraction and no modular reasoning. -/
theorem value_of_chain {Bc n : Nat} (L R c : Nat → Nat)
    (hstep : ∀ k, k < n → L k + c k = R k + Bc * c (k + 1)) :
    vsum L Bc n + c 0 = vsum R Bc n + c n * Bc ^ n := by
  induction n with
  | zero => simp [vsum]
  | succ m ih =>
    have hstep' : ∀ k, k < m → L k + c k = R k + Bc * c (k + 1) :=
      fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self m))
    have h1 := ih hstep'
    simp only [vsum, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at *
    have hlast : L m + c m = R m + Bc * c (m + 1) := hstep m (Nat.lt_succ_self m)
    have hmul : L m * Bc ^ m + c m * Bc ^ m = R m * Bc ^ m + Bc * c (m + 1) * Bc ^ m := by
      have := congrArg (fun x => x * Bc ^ m) hlast
      rw [Nat.add_mul, Nat.add_mul] at this
      exact this
    have hshift : Bc * c (m + 1) * Bc ^ m = c (m + 1) * Bc ^ (m + 1) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [hshift] at hmul
    omega

/-- `value_of_chain` with `c 0 = 0`. -/
theorem value_of_chain0 {Bc n : Nat} (L R c : Nat → Nat) (h0 : c 0 = 0)
    (hstep : ∀ k, k < n → L k + c k = R k + Bc * c (k + 1)) :
    vsum L Bc n = vsum R Bc n + c n * Bc ^ n := by
  have := value_of_chain L R c hstep
  rw [h0] at this
  omega

/-! ## Exact recombination (obligation, NOT proved) -/

/-- The double sum `Σ_i a_i·B^i·(Σ_j b_j·B^j)`, i.e. `a·b` with the limbs made
explicit.  Used only to *state* the recombination obligation. -/
def recombineAux (a b : Nat) : Nat :=
  ((List.range NLIMB).map (fun i =>
    limb a i * (B ^ i * ((List.range NLIMB).map (fun j => limb b j * B ^ j)).sum))).sum

/-- Recombination obligation: the convolution's digit value is `a·b`.

**Not proved here.**  It is an exact finite combinatorial identity (reorder the
15x15 grid, shift indices); proving it needs a `List`/`Finset` double-sum
rearrangement that is out of the prototype's scope.  `difftest.py` checks it on
every vector (including `0`, `1`, `p−1` and full-width products), and it enters
`mul_identity` below as an explicit hypothesis `hconv`, never as an axiom and
never as a `sorry`. -/
def RecombineConv (a b : Nat) : Prop :=
  vsum (conv a b) B NCONV = a * b

/-- Recombination obligation for `q·p + r`. -/
def RecombineQP (q r : Nat) : Prop :=
  vsum (fun k => qpConv q k + rLimb r k) B NCONV = q * p + r

/-! ## The identity -/

/-- **Soundness of the row relation.**  Assume (i) the two chains' step
equations for `k < NCONV`, (ii) the zero boundaries, (iii) `cd NCONV = ce NCONV`,
(iv) the exact recombinations.  Then `a·b = q·p + r`.

(i)–(iii) are exactly what `constraints` checks plus the range bounds that make
`Expr.evalInt` agree with the `Nat`-valued equations; (iv) is
`recombine_conv`/`recombine_qp` (stated, not yet proved — see the status block). -/
theorem mul_identity (a b q r : Nat) (d cd ce : Nat → Nat)
    (hP : ∀ k, k < NCONV → conv a b k + cd k = d k + B * cd (k + 1))
    (hE : ∀ k, k < NCONV → qpConv q k + rLimb r k + ce k = d k + B * ce (k + 1))
    (hcd0 : cd 0 = 0) (hce0 : ce 0 = 0)
    (hfin : cd NCONV = ce NCONV)
    (hconv : RecombineConv a b)
    (hqp : RecombineQP q r) :
    a * b = q * p + r := by
  have h1 := value_of_chain0 (conv a b) d cd hcd0 hP
  have h2 := value_of_chain0 (fun k => qpConv q k + rLimb r k) d ce hce0 hE
  rw [hfin] at h1
  unfold RecombineConv at hconv
  unfold RecombineQP at hqp
  rw [← hconv, ← hqp]
  rw [h1, h2]

end FpChip
end NearCompression.PqEd25519
