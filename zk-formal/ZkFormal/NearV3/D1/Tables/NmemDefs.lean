import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.Tables.NmemDefs` — `nmemV3`: non-membership in the store

Lane `v3-d1-a7b` (plan §5, R-5 → (B), item 3).  Definitions only (verifier-model import rule).

One 32-row segment per query `NMQ (τ, h)` of a `nodeD1` stub window: `h` is not the digest of
any store entry of instance `τ`.  The 32 bytes of `h` are received on the segment's first row
into the shift register `q 0 … 31` (row `i` holds `h_i` in `q 0`); row `i` reads the gap
lookup `GB (s, τ, i, lo_i, hi_i, ft, st, lt, u)` of `uniqD1`'s entry `s` (chained consumer),
so `lo` / `hi` are the digests of entry `s − 1` and entry `s`.  Exactly one mode:
* `mBt` (between): entries `s − 1`, `s` of the same instance (`ft = st = 0`) and
  `lo < h < hi`;
* `mLo` (below): entry `s` is the first of its instance (`ft = 1` or `st = 1`) and `h < hi`;
* `mHi` (above): entry `s` is the last of its instance (`lt = 1`) and `hi < h`.
Digests are little-endian 256-bit integers (byte `i` has weight `256^i`, as in `uniqV3`).  Two
byte-serial strict comparisons (carry-in `1` at byte 0, no carry out of byte 31):
* `A`: `h = X + dA + 1` with `X = lo` (between) or `hi` (above), gate `mBt + mHi`;
* `B`: `hi = h + dB + 1`, gate `mBt + mLo`.
-/

namespace ZkFormal.NearV3.D1.NmemV3

open ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.NearV3.D1 (B_NMQ B_GB)

def act : Nat := 0
def sf : Nat := 1
def sl : Nat := 2
def i : Nat := 3
def tau : Nat := 4
def ti : Nat := 5
def mBt : Nat := 6
def mLo : Nat := 7
def mHi : Nat := 8
def lo : Nat := 9
def hi : Nat := 10
def fF : Nat := 11
def sF : Nat := 12
def lF : Nat := 13
def uG : Nat := 14
def q (j : Nat) : Nat := 15 + j
def cA : Nat := 47
def oA : Nat := 48
def cB : Nat := 49
def oB : Nat := 50
def dA (j : Nat) : Nat := 51 + j
def dB (j : Nat) : Nat := 59 + j
def width : Nat := 67

def dAE : Expr := bits (fun j => c (dA j)) 0 8
def dBE : Expr := bits (fun j => c (dB j)) 0 8
/-- the lower bound of comparison `A`: `lo` (between) or `hi` (above) -/
def xE : Expr := .add (c lo) (.mul (c mHi) (sub (c hi) (c lo)))
def gAE : Expr := .add (c mBt) (c mHi)
def gBE : Expr := .add (c mBt) (c mLo)

def boolCols : List Nat :=
  [act, sf, sl, mBt, mLo, mHi, cA, oA, cB, oB] ++ (List.range 8).map dA ++ (List.range 8).map dB

/-- Segment-constant columns. -/
def segConst : List Nat := [tau, ti, mBt, mLo, mHi]

def constraints : List Expr :=
  boolCols.map (fun x => bool (c x)) ++
  [ .mul (c sf) (not (c act)), .mul (c sl) (not (c act)),
    .mul .isFirst (sub (c act) (c sf)),
    .mul .isLast (.mul (c act) (not (c sl))),
    .mul (c sf) (c i), .mul (c sl) (sub (c i) (k 31)),
    -- within a segment
    mul3 (c act) (not (c sl)) (not (n act)),
    mul3 (c act) (not (c sl)) (n sf),
    mul3 (c act) (not (c sl)) (sub (n i) (.add (c i) (k 1))) ] ++
  segConst.map (fun x => mul3 (c act) (not (c sl)) (sub (n x) (c x))) ++
  (List.range 31).map (fun j => mul3 (c act) (not (c sl)) (sub (n (q j)) (c (q (j + 1))))) ++
  [ -- next segment or padding
    mul3 (c sl) (n act) (not (n sf)),
    mul3 .isTransition (not (c act)) (n act),
    -- exactly one mode
    .mul (c act) (sub (sum [c mBt, c mLo, c mHi]) (k 1)),
    -- the mode's gap
    .mul (c mBt) (c fF), .mul (c mBt) (c sF),
    mul3 (c mLo) (not (c fF)) (not (c sF)),
    .mul (c mHi) (not (c lF)),
    -- comparison A: h = X + dA + 1 (byte-serial)
    .mul gAE (sub (.add (c (q 0)) (smul 256 (c oA))) (sum [xE, dAE, c cA])),
    .mul (c sf) (sub (c cA) (k 1)),
    mul3 (c act) (not (c sl)) (sub (n cA) (c oA)),
    .mul gAE (.mul (c sl) (c oA)),
    -- comparison B: hi = h + dB + 1 (byte-serial)
    .mul gBE (sub (.add (c hi) (smul 256 (c oB))) (sum [c (q 0), dBE, c cB])),
    .mul (c sf) (sub (c cB) (k 1)),
    mul3 (c act) (not (c sl)) (sub (n cB) (c oB)),
    .mul gBE (.mul (c sl) (c oB)) ]

def gb (u : Expr) : List Expr := [c ti, c tau, c i, c lo, c hi, c fF, c sF, c lF, u]

def interactions : List Interaction :=
  [ recv B_NMQ (c sf) (c tau :: (List.range 32).map fun j => c (q j)),
    recv B_GB (c act) (gb (c uG)),
    send B_GB (c act) (gb (.add (c uG) (k 1))) ]

/-- `≤ 2·NT0 = 8192` stub windows (one per unread walk at most) × 32 rows `= 2^18`, padded to the
roll-aligned height `2^19`. -/
def maxLog : Nat := 19

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.NmemV3
