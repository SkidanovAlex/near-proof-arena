import ZkFormal.NearV3.Tables.NodeUpb
import ZkFormal.NearV3.Tables.Val
import ZkFormal.NearV3.Tables.Ups
import ZkFormal.NearV3.Rcpt.Tables.Size

/-!
# ZkFormal.NearV3.Tables.UnfoldA7 — in-AIR accounting of the A7 measure

RelD0a's A7 (user decision 2026-10-11, revised measure) bounds
`unfoldBytes cb w = Σ_τ unfoldedBytesT pre_τ + unfoldedBytesT post_τ ≤ B0 = 2,000,000`.
In the records of `nearAirV3` (one node record per revealed pre-trie occurrence, one row per
byte; one value record per revealed value occurrence, one row per byte):

* `unfoldedBytesT pre_τ` = the node rows of τ + the value byte rows of τ;
* `unfoldedBytesT post_τ` = the node rows of the records **not replaced** by an `upsV3` part
  (lockstep `set`s keep every length) + the bytes of the `upsV3` parts `Q_j` + the value byte
  rows of the values not replaced + the new `0x0f` value (`L` bytes).

The replaced node records are the terminal record `N_D` and the source record `sN` of every
upper part (`RDB`/`RDE`/`PT`); the replaced value is the old `0x0f` value `vid` when present.

Each table below **extends** its base table (base columns, constraints and interactions are
kept unchanged, new ones appended), so every proved base view still applies:

* `nodeA7`: record flag `rpl` (received `RPL (nid)` on the first row iff set) and the running
  sum `ra` (`+2` per row, `− len` on the first row of a replaced record); the `SUM` row sends
  `SIZE (3, ra)`;
* `valA7`: the same with `rplv` / `RPLV (vid)` / `rb` (`+2` per byte row), `SIZE (4, rb)`;
* `upsA7`: sends `RPL (sN)` on the first row of every upper part, `RPL (N_D)` and, if the
  `0x0f` value was present, `RPLV (vid)` on the segment's first row; the running sum `s` of its
  value and node-part rows is sent as `SIZE (5, s)` on the last row (padding);
* `sizeA7`: rows `t = 0,1,2` also receive `SIZE (t + 3, y)`; the running sum `u` of `y` is
  range-checked on the last active row: `B0 − u` is a 24-bit value.
-/

namespace ZkFormal.NearV3.UnfoldA7

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- `RPL (nid)`: an `upsV3` part replaces node record `nid` in the post trie. -/
def B_RPL : Nat := 70
/-- `RPLV (vid)`: the `0x0f` upsert replaces value record `vid`. -/
def B_RPLV : Nat := 71

/-- The A7 bound (`NearSpecV3.B0`). -/
def B0 : Nat := 2000000

/-! ## `nodeV3` -/

namespace Node
open ZkFormal.NearV3.NodeV3 in
section
def rpl : Nat := 186
def ra : Nat := 187
def width : Nat := 188

def constraints : List Expr :=
  [ bool (c rpl),
    .mul .isFirst (c ra),
    .mul .isTransition
      (sub (n ra) (.add (c ra) (sub (smul 2 (c act)) (mul3 (c nf) (c rpl) (c len))))) ]

def interactions : List Interaction :=
  [ recv B_RPL (.mul (c nf) (c rpl)) [c nid],
    send B_SIZE (c sumr) [k 3, c ra] ]
end
end Node

/-- `nodeV3` with the A7 accounting. -/
def nodeA7 : Table :=
  { ZkFormal.NearV3.NodeV3.tableU with
    width := Node.width
    constraints := ZkFormal.NearV3.NodeV3.tableU.constraints ++ Node.constraints
    interactions := ZkFormal.NearV3.NodeV3.tableU.interactions ++ Node.interactions }

/-! ## `valV3` -/

namespace Val
open ZkFormal.NearV3.ValV3 in
section
def rplv : Nat := 15
def rb : Nat := 16
def width : Nat := 17

def constraints : List Expr :=
  [ bool (c rplv),
    .mul .isFirst (c rb),
    .mul .isTransition
      (sub (n rb) (.add (c rb) (sub (smul 2 (c gb)) (mul3 (c vf) (c rplv) (c len))))) ]

def interactions : List Interaction :=
  [ recv B_RPLV (.mul (c vf) (c rplv)) [c vid],
    send B_SIZE (c sumr) [k 4, c rb] ]
end
end Val

/-- `valV3` with the A7 accounting. -/
def valA7 : Table :=
  { ZkFormal.NearV3.ValV3.table with
    width := Val.width
    constraints := ZkFormal.NearV3.ValV3.table.constraints ++ Val.constraints
    interactions := ZkFormal.NearV3.ValV3.table.interactions ++ Val.interactions }

/-! ## `upsV3` -/

namespace Ups
open ZkFormal.NearV3.UpsV3 in
section
def s : Nat := 200
/-- the terminal record `N_D` (on the segment's first row) -/
def nD : Nat := 201
def width : Nat := 202

def constraints : List Expr :=
  [ .mul .isFirst (c s),
    .mul .isTransition (sub (n s) (.add (c s) (.add (c vb) (c qb)))),
    .mul (c sf) (sub (c nD) (sum [.mul (c dd0) (c N0), .mul (c dd1) (c N1), .mul (c dd2) (c N2)])) ]

def interactions : List Interaction :=
  [ send B_RPL (.mul (c pf) (c up)) [c sN],
    send B_RPL (c sf) [c nD],
    send B_RPLV (.mul (c sf) (c pres)) [c vid],
    send B_SIZE .isLast [k 5, c s] ]
end
end Ups

/-- `upsV3` with the A7 accounting. -/
def upsA7 : Table :=
  { ZkFormal.NearV3.UpsV3.table with
    width := Ups.width
    constraints := ZkFormal.NearV3.UpsV3.table.constraints ++ Ups.constraints
    interactions := ZkFormal.NearV3.UpsV3.table.interactions ++ Ups.interactions }

/-! ## `sizeV3` -/

namespace Size
open ZkFormal.NearV3.SizeV3 in
section
def y : Nat := 31
def u : Nat := 32
def ub (e : Nat) : Nat := 33 + e
def width : Nat := 57

def ubitsE : Expr := bits (fun e => c (ub e)) 0 24

def constraints : List Expr :=
  (List.range 24).map (fun e => bool (c (ub e))) ++
  [ .mul .isFirst (sub (c u) (c y)),
    mul3 .isTransition (n act) (sub (n u) (.add (c u) (n y))),
    .mul (c la) (sub ubitsE (sub (k B0) (c u))) ]

def interactions : List Interaction :=
  [ recv B_SIZE (c act) [.add (c t) (k 3), c y] ]
end
end Size

/-- `sizeV3` (cap `2^4`) with the A7 bound. -/
def sizeA7 : Table :=
  { ZkFormal.NearV3.SizeV3.table with
    maxLog := 4
    width := Size.width
    constraints := ZkFormal.NearV3.SizeV3.table.constraints ++ Size.constraints
    interactions := ZkFormal.NearV3.SizeV3.table.interactions ++ Size.interactions }

end ZkFormal.NearV3.UnfoldA7
