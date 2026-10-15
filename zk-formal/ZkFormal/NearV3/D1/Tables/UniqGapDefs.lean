import ZkFormal.NearV3.Tables.Uniq
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.Tables.UniqGapDefs` — `uniqD1`: `uniqV3` with its sorted gaps on `GB`

Lane `v3-d1-a7b` (plan §5, R-5 → (B), item 3).  Definitions only (verifier-model import rule).
`uniqD1` **extends** `uniqV3` (table 6): columns `0 … 52`, constraints and interactions are
kept unchanged and new ones appended (every proved `uniqV3` view still applies; the new
interaction uses only the new bus `GB`).

`uniqV3` sorts every store entry by `(τ, digest)` (non-strictly; equal digests are byte-equal
entries).  `uniqD1` adds, per segment (entry) `s`:
* `sidx` — the segment's index (`0, 1, 2, …` in table order);
* `lt` — the entry is the last of its instance (the next entry starts a new instance, or there
  is none);
and offers on every row `i` of segment `s` (chained provider, use count `mG`) the lookup
`GB (s, τ, i, prev_i, cur_i, ft, st, lt)`, where `cur_i` is byte `i` of the entry's digest
(`bb`) and `prev_i` the same byte of the previous entry's digest (`d 31`, the 32-row delay
line; meaningless on the first entry, `ft = 1`).  `nmemV3` reads the 32 bytes of one gap and
proves `prev < h < cur` (or `h < cur` at an instance's first entry, `cur < h` at its last).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

namespace UniqGap
open ZkFormal.NearV3.Uniq in
section

def sidx : Nat := 53
def lt : Nat := 54
def mG : Nat := 55
def width : Nat := 56

def constraints : List Expr :=
  [ bool (c lt),
    .mul .isFirst (c sidx),
    -- segment constants
    mul3 (c act) (not (c sl)) (sub (n sidx) (c sidx)),
    mul3 (c act) (not (c sl)) (sub (n lt) (c lt)),
    -- next segment: index + 1; `lt` iff it starts a new instance
    .mul (mul3 (c sl) (n act) .isTransition) (sub (n sidx) (.add (c sidx) (k 1))),
    .mul (mul3 (c sl) (n act) .isTransition) (sub (c lt) (n st)),
    -- no next segment (padding follows, or the table ends): last of its instance
    .mul (mul3 (c sl) (not (n act)) .isTransition) (not (c lt)),
    mul3 .isLast (c sl) (not (c lt)) ]

def gb (u : Expr) : List Expr := [c sidx, c tau, c i, c (d 31), c bb, c ft, c st, c lt, u]

def interactions : List Interaction :=
  [ send B_GB (c act) (gb (k 0)),
    recv B_GB (c act) (gb (c mG)) ]

end
end UniqGap

/-- **`uniqD1`**: `uniqV3` with the gap lookups. -/
def uniqD1 : ZkFormal.Air.Table :=
  { ZkFormal.NearV3.Uniq.table with
    width := UniqGap.width
    constraints := ZkFormal.NearV3.Uniq.table.constraints ++ UniqGap.constraints
    interactions := ZkFormal.NearV3.Uniq.table.interactions ++ UniqGap.interactions }

end ZkFormal.NearV3.D1
