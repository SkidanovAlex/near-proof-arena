import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids

/-!
# `ZkFormal.NearV3.D1.Tables.UvalDefs` — `uvalV3`: the value bytes no reader provides

Lane `v3-d1-a7b` (plan §5, R-5 → (B), item 4).  Definitions only (verifier-model import rule).

`checkD1`'s main pre trie reveals the value of a leaf (or branch) that a key of `txKeys` matches
exactly whenever the value's hash is in the store, read or not.  So the AIR reveals it too: the
window is a value window (`tv = 1`) with a value record `vid` of `valV3` (counted by `valA7`'s
running sum like every revealed value), and an unread walk ends there with the terminal `VAL`.
A value record receives its bytes on `VBYTES (vid, pos, byte)` from the table that reads them
(`acctV3`, `akeyV3`, `akmV3`, the queue values); a value revealed only for an unread key has no
reader, and `uvalV3` sends its bytes instead: one row per byte, the byte range-checked.  The
bytes are bound by the window's `DIGEST` lookup (the value's hash in the parent record), and
every value record receives each of its bytes exactly once (`valV3`), so `uvalV3` can provide
only bytes no other table provides.
-/

namespace ZkFormal.NearV3.D1.UvalV3

open ZkFormal.Air ZkFormal.Near.Dsl

def act : Nat := 0
def vid : Nat := 1
def pos : Nat := 2
def b : Nat := 3
def bb (j : Nat) : Nat := 4 + j
def width : Nat := 12

def constraints : List Expr :=
  (bool (c act) :: (List.range 8).map (fun j => bool (c (bb j)))) ++
  [ .mul (c act) (sub (c b) (bits (fun j => c (bb j)) 0 8)) ]

def interactions : List Interaction :=
  [ send ZkFormal.NearV3.B_VBYTES (c act) [c vid, c pos, c b] ]

/-- Revealed value bytes `≤ B0 / 2 = 10^6 < 2^20` (A7 counts each value byte twice), padded to
the roll-aligned height `2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.UvalV3
