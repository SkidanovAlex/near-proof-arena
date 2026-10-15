import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.Tables.RelayDefs` — `kibV3`, `plfV3`, `ridV3`: public-to-bus relays

Three one-row-per-record tables that turn D1 public records (native data of `prepD1`) into the
messages of unchanged `nearAirV3` tables.  A public record is a list of bytes (plus an
optional generated index), so a message with a field element above `255` that is not the
record index (a walk id, a leaf message id, a receipt-id slot) needs one relay row.  Each
active row receives exactly one public record and sends the derived message(s); a relay
row cannot exist without its public record (the receive would be unbalanced), and every
public record must be consumed.

* `kibV3`: `PKEY (w₀, w₁, w₂, t, sym, last)` ↦ `KEYNIB (w₀ + 2⁸w₁ + 2¹⁶w₂, t, sym, last)`
  (the transaction walks' key nibbles, `walkV3` unchanged).
* `plfV3`: `PLEAF (pos, d[32])` ↦ `MPOS (0, pos, PLF(pos), 68)` and `DIGEST (PLF(pos), 68, d)`
  (outcome leaves `0 … M0 − 1` of `mrkV3`, unchanged; `PLF(pos) = 15 + 16·pos`).
* `ridV3`: `PRID (j, b)` with `j = 32·l + i`, `i < 32`, `l < 2^12` (range-checked by bits,
  lane v3-d1-a7b) ↦ `RIDS (W_LOC + l, i, b)` (local receipt ids for `sortV3`'s distinctness,
  unchanged).

Definitions only (verifier-model import rule).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

namespace KibV3

def act : Nat := 0
def w0 : Nat := 1
def w1 : Nat := 2
def w2 : Nat := 3
def t : Nat := 4
def sym : Nat := 5
def last : Nat := 6
def width : Nat := 7

def wE : Expr := sum [c w0, smul 256 (c w1), smul 65536 (c w2)]

def constraints : List Expr := [bool (c act)]

def interactions : List Interaction :=
  [ recv B_PKEY (c act) [c w0, c w1, c w2, c t, c sym, c last],
    send B_KEYNIB (c act) [wE, c t, c sym, c last] ]

/-- `≤ NT0 · (130 + 198) + NT0 · 130` key nibbles of the transaction and credit walks `< 2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end KibV3

namespace PlfV3

def act : Nat := 0
def pos : Nat := 1
def d (i : Nat) : Nat := 2 + i
def width : Nat := 34

def idE : Expr := mid K_PLF (c pos)

def constraints : List Expr := [bool (c act)]

def interactions : List Interaction :=
  [ recv B_PLEAF (c act) (c pos :: (List.range 32).map fun i => c (d i)),
    send B_MPOS (c act) [k 0, c pos, idE, k 68],
    send B_DIGEST (c act) ([idE, k 68] ++ (List.range 32).map fun i => c (d i)) ]

/-- `M0 ≤ NT0 + NT0 = 8192` leaves. -/
def maxLog : Nat := 13

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end PlfV3

namespace RidV3

def act : Nat := 0
def j : Nat := 1
def l : Nat := 2
def ib (x : Nat) : Nat := 3 + x
def b : Nat := 8
/-- the bits of the slot `l < 2^12` (lane v3-d1-a7b soundness fix: without them `l` is any field
element with `32·l + i = j`, so a row could pick `i ≢ j (mod 32)`) -/
def lb (x : Nat) : Nat := 9 + x
def width : Nat := 21

def iE : Expr := bits (fun x => c (ib x)) 0 5
def lE : Expr := bits (fun x => c (lb x)) 0 12

def constraints : List Expr :=
  [bool (c act)] ++ (List.range 5).map (fun x => bool (c (ib x))) ++
  [ Expr.mul (c act) (sub (c j) (.add (smul 32 (c l)) iE)) ] ++
  (List.range 12).map (fun x => bool (c (lb x))) ++
  [ Expr.mul (c act) (sub (c l) lE) ]

def interactions : List Interaction :=
  [ recv B_PRID (c act) [c j, c b],
    send B_RIDS (c act) [.add (k W_LOC) (c l), iE, c b] ]

/-- `32 · n_loc ≤ 32 · NT0 = 2^17` bytes. -/
def maxLog : Nat := 19

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end RidV3

end ZkFormal.NearV3.D1
