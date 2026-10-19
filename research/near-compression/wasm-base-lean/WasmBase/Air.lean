import ZkFormal.Algebra.Fp
/-!
# WasmBase.Air — the AIR model of the direct-Wasm base layer (lane/pq-wasm-base)

This Lean value is the **single source of truth** for the AIR: `wasmbase-tool air` exports it as
JSON, and the Rust crate `native/wasm-base` *interprets* that JSON inside `Air::eval` (so the
SWIRL keygen sees exactly these constraints and interactions).  An independent differential test
(`native/wasm-base/difftest.py`) evaluates the Lean expressions (in Lean) and the Rust verifying
key's symbolic DAG at random points.

## Semantics

The model mirrors the openvm/SWIRL AIR interface:

* a table is a list of column names, polynomial constraints over the current row (`col`), the next
  row (`nxt`, cyclic), public values (`pub`) and the selectors `first`, `last`, `trans`;
* an interaction sends (`send = true`, LogUp count `+count`) or receives (`-count`) the message
  `msg` on bus `bus`.  `count` is an expression evaluated in the field.

`Holds A pub tr` is what the SWIRL PIOP enforces (BF2): every constraint vanishes on every row, and
for every bus `b` and message `m` the **field** sum of signed counts is zero, i.e. the natural sums
of sent and received counts agree **mod p**.  The consequences "multiset equality" and "lookup
membership" are *derived* (`WasmBase.Bus`) from booleanity of the counts and the height bounds,
not assumed.
-/
namespace WasmBase
open ZkFormal.Algebra

abbrev F := Fp

/-- Constraint / message expressions. -/
inductive Expr where
  | c (n : Nat)
  | col (i : Nat)
  | nxt (i : Nat)
  | pub (i : Nat)
  | first
  | last
  | trans
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance instOfNatExpr (n : Nat) : OfNat Expr n := ⟨Expr.c n⟩

structure Inter where
  bus : Nat
  send : Bool
  count : Expr
  msg : List Expr
  deriving Repr, BEq, DecidableEq, Inhabited

structure Table where
  name : String
  cols : List String
  constraints : List Expr
  inters : List Inter
  deriving Repr, Inhabited

def Table.width (T : Table) : Nat := T.cols.length

structure Air where
  tables : List Table
  numPub : Nat
  deriving Repr, Inhabited

/-! ## Evaluation -/

/-- One row of one table: current row, next row (cyclic), publics, selectors. -/
structure Row where
  cur : Nat → F
  nxt : Nat → F
  pub : Nat → F
  isFirst : Bool
  isLast : Bool

def Expr.eval (rw : Row) : Expr → F
  | .c n => (n : F)
  | .col i => rw.cur i
  | .nxt i => rw.nxt i
  | .pub i => rw.pub i
  | .first => if rw.isFirst then 1 else 0
  | .last => if rw.isLast then 1 else 0
  | .trans => if rw.isLast then 0 else 1
  | .add a b => a.eval rw + b.eval rw
  | .sub a b => a.eval rw - b.eval rw
  | .mul a b => a.eval rw * b.eval rw

/-- Formal degree (selectors count 1, as in the backend's symbolic degree). -/
def Expr.degree : Expr → Nat
  | .c _ | .pub _ => 0
  | .col _ | .nxt _ | .first | .last | .trans => 1
  | .add a b | .sub a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- A trace: heights and cells (table, row, column). -/
structure Trace where
  height : Nat → Nat
  cell : Nat → Nat → Nat → F

def Trace.row (tr : Trace) (pub : List F) (t r : Nat) : Row where
  cur := tr.cell t r
  nxt := tr.cell t ((r + 1) % tr.height t)
  pub := fun i => pub.getD i 0
  isFirst := r == 0
  isLast := r + 1 == tr.height t

/-- One interaction occurrence: bus, direction, evaluated message, count as a natural. -/
abbrev Occ := Nat × Bool × List F × Nat

/-- Every interaction occurrence of the trace (all tables, all rows). -/
def occs (A : Air) (tr : Trace) (pub : List F) : List Occ :=
  (A.tables.zipIdx).flatMap fun (T, t) =>
    (List.range (tr.height t)).flatMap fun r =>
      T.inters.map fun i => (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)

/-- Natural sum of the counts with which bus `b` carries message `m` in direction `send`. -/
def busNat (A : Air) (tr : Trace) (pub : List F) (b : Nat) (send : Bool) (m : List F) : Nat :=
  (((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = send ∧ o.2.2.1 = m).map (·.2.2.2)).sum

/-- The verifier's per-bus trace-height constraint (openvm keygen: every interaction has weight 1):
`Σ_t height_t · #(interactions of table t on bus b) < p`. -/
def busLoad (A : Air) (tr : Trace) (b : Nat) : Nat :=
  ((A.tables.zipIdx).map fun (T, t) => tr.height t * (T.inters.filter (·.bus = b)).length).sum

/-- Maximal log-height of any table (pinned base shape: stacked height `2^24`). -/
def maxLogHeight : Nat := 24

/-- **The AIR relation** enforced by the SWIRL PIOP (constraints + mod-p LogUp balance). -/
structure Holds (A : Air) (pub : List F) (tr : Trace) : Prop where
  pubLen : pub.length = A.numPub
  heightPos : ∀ t, t < A.tables.length → 4 ≤ tr.height t
  heightLe : ∀ t, t < A.tables.length → tr.height t ≤ 2 ^ maxLogHeight
  constr : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (tr.row pub t r) = 0
  balance : ∀ b m, busNat A tr pub b true m % P = busNat A tr pub b false m % P
  busBound : ∀ b, busLoad A tr b < P

end WasmBase

namespace WasmBase
namespace Expr
variable (rw : Row)
@[simp] theorem eval_add' (a b : Expr) : (a + b).eval rw = a.eval rw + b.eval rw := rfl
@[simp] theorem eval_sub' (a b : Expr) : (a - b).eval rw = a.eval rw - b.eval rw := rfl
@[simp] theorem eval_mul' (a b : Expr) : (a * b).eval rw = a.eval rw * b.eval rw := rfl
@[simp] theorem eval_ofNat' (n : Nat) : (no_index (@OfNat.ofNat Expr n (instOfNatExpr n))).eval rw = ((n : Nat) : F) := rfl
@[simp] theorem eval_c (n : Nat) : (Expr.c n).eval rw = ((n : Nat) : F) := rfl
@[simp] theorem eval_col (i : Nat) : (Expr.col i).eval rw = rw.cur i := rfl
@[simp] theorem eval_nxt (i : Nat) : (Expr.nxt i).eval rw = rw.nxt i := rfl
@[simp] theorem eval_pub (i : Nat) : (Expr.pub i).eval rw = rw.pub i := rfl
end Expr
end WasmBase
