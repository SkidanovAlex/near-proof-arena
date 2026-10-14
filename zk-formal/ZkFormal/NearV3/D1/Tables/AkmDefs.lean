import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.Tables.AkmDefs` — `akmV3`: access-key values read by transactions

Lane `v3-d1-tables` (V3-D1-DESIGN §2.4 (a)).  Definitions only (verifier-model import rule).

One segment per access-key value record `vid` (a `valV3` record) reached by a transaction's
access-key walk, one row per value byte (`VBYTES (vid, pos, b)`: the segment has exactly the
record's bytes).  The rows run the borsh grammar of `TxD1.decodeAccessKey` (no trailing bytes):

```
AK   := nonce[8] tag
tag 1 (FullAccess): end            tag 0: FCP          tag 2: GKI[18] FCP     tag 3: GKI[18] end
FCP  := opt (0 | 1 allowance[16]) STR(receiver) count[4] STR(method)^count   end
STR  := len[4] utf8[len]           (u32 lengths and counts with high byte 0, i.e. < 2^24)
```

States (one-hot): `sN` nonce, `sT` tag, `sG` gas-key info, `sO` option tag, `sA` allowance,
`sL` u32 length, `sS` string body, `sC` u32 method count.  A fixed field ends (`fe`) at
`ix = len − 1`, a string body at `rem = 1` (`fe = [last = 0]` by an inverse).  The segment's
last row `al` is exactly an accepting end (`endOK`): the FullAccess tag, the last gas-key byte
of tag 3, a zero method count, or the end of the last method name.  The bytes of a string body
are well-formed UTF-8 (`utf8Ok`): classes ASCII / continuation / 2-, 3-, 4-byte lead (`C2–DF`,
`E0–EF`, `F0–F4`), `uc` continuation bytes pending, the second-byte ranges after `E0`, `ED`,
`F0`, `F4` (flags `pE0 … pF4` on the next row), no pending continuation at the string's end.
A value that does not decode has no satisfying segment (`decodeAccessKey = none` rejects).

Outputs: `fa = t1` (FullAccess).  Rows `sN` (`pos = 0 … 7`) provide the key's nonce memory:
`AKMEM (vid, 0, i, b_i, fa)` (initial) and receive `AKMEM (vid, tlast, i, pb_i, fa)` (final);
a non-FullAccess key is never written (`pb = b`).  A FullAccess key (9 bytes) is a written
value: `VSLOT (vid)`, the post value `BYTES (VPOST(vid), pos, ·)` = `pb₀ … pb₇ ‖ 1`
(`encodeFullAccessKey`), and the gas-refund chain `AKC (vid, ·)` (send `0`, receive `U`), as
`akeyV3` for keys not read by any transaction.
-/

namespace ZkFormal.NearV3.D1.AkmV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1

/-! ## Columns -/

def act : Nat := 0
def af : Nat := 1
def al : Nat := 2
def vid : Nat := 3
def pos : Nat := 4
def bb (x : Nat) : Nat := 5 + x
-- states
def sN : Nat := 13
def sT : Nat := 14
def sG : Nat := 15
def sO : Nat := 16
def sA : Nat := 17
def sL : Nat := 18
def sS : Nat := 19
def sC : Nat := 20
def mth : Nat := 21
def ix : Nat := 22
def fe : Nat := 23
def invE : Nat := 24
def rem : Nat := 25
def pw : Nat := 26
def acc : Nat := 27
def zA : Nat := 28
def invA : Nat := 29
def vc : Nat := 30
def zV : Nat := 31
def invV : Nat := 32
def t (x : Nat) : Nat := 33 + x
def tlast : Nat := 37
def pb : Nat := 38
def U : Nat := 39
-- UTF-8
def cA : Nat := 40
def cC : Nat := 41
def c2 : Nat := 42
def c3 : Nat := 43
def c4 : Nat := 44
def inv2 : Nat := 45
def zl0 : Nat := 46
def il0 : Nat := 47
def zl13 : Nat := 48
def il13 : Nat := 49
def z30 : Nat := 50
def i30 : Nat := 51
def z34 : Nat := 52
def i34 : Nat := 53
def pE0 : Nat := 54
def pED : Nat := 55
def pF0 : Nat := 56
def pF4 : Nat := 57
def uc : Nat := 58
def ucn : Nat := 59
-- events
def sd : Nat := 60
def md : Nat := 61
def endOK : Nat := 62
/-- `fe·(1 − al)`: a field ends and the segment goes on -/
def fgo : Nat := 63
/-- a string body starts on the next row: `sL·fgo·(1 − zA)` -/
def eS : Nat := 64
/-- a method name starts on the next row after the count: `sC·fgo·(1 − zA)` -/
def eC : Nat := 65
/-- another method name follows: `md·(1 − zV)` -/
def eM : Nat := 66
/-- FullAccess gates `af·t1`, `sN·t1`, `sT·t1` (degree-1 multiplicities) -/
def aF : Nat := 67
def nF : Nat := 68
def tF : Nat := 69
def width : Nat := 70

/-! ## Expressions -/

def bt (x : Nat) : Expr := c (bb x)
def bE : Expr := bits (fun x => c (bb x)) 0 8
def bN : Expr := bits (fun x => n (bb x)) 0 8
/-- low nibble, low three bits, bits `1 … 4` -/
def loE : Expr := bits (fun x => c (bb x)) 0 4
def lo3E : Expr := bits (fun x => c (bb x)) 0 3
def v2E : Expr := bits (fun x => c (bb (x + 1))) 0 4

def states : List Nat := [sN, sT, sG, sO, sA, sL, sS, sC]
def classes : List Nat := [cA, cC, c2, c3, c4]

/-- `last = 0` at a field's last row: `ix − (len − 1)` for the fixed fields, `rem − 1` for a
string body. -/
def lastE : Expr :=
  sum [ .mul (c sN) (sub (c ix) (k 7)), .mul (c sT) (c ix), .mul (c sG) (sub (c ix) (k 17)),
        .mul (c sO) (c ix), .mul (c sA) (sub (c ix) (k 15)), .mul (c sL) (sub (c ix) (k 3)),
        .mul (c sC) (sub (c ix) (k 3)), .mul (c sS) (sub (c rem) (k 1)) ]

/-- `sL + sC` (a u32 field). -/
def u32S : Expr := .add (c sL) (c sC)
def u32SN : Expr := .add (n sL) (n sC)
/-- Transition guard: the row does not end the segment. -/
def go (e : Expr) : Expr := .mul (not (c al)) e
def tagE : Expr := sum [c (t 1), smul 2 (c (t 2)), smul 3 (c (t 3))]

def boolCols : List Nat :=
  [act, af, al, mth, fe, zA, zV, sd, md, endOK, fgo, eS, eC, eM] ++ (List.range 8).map bb ++ states ++
  (List.range 4).map t ++ classes ++ [zl0, zl13, z30, z34, pE0, pED, pF0, pF4]

/-- Segment constants. -/
def segConst : List Nat := [vid, t 0, t 1, t 2, t 3, tlast, U]

/-! ## Constraints -/

def cShape : List Expr :=
  boolCols.map (fun x => bool (c x)) ++
  [ .mul (c af) (not (c act)), .mul (c al) (not (c act)),
    .mul .isFirst (sub (c act) (c af)),
    .mul .isLast (.mul (c act) (not (c al))),
    mul3 (c act) (not (c al)) (not (n act)),
    mul3 (c act) (not (c al)) (n af),
    mul3 (c al) (n act) (not (n af)),
    mul3 .isTransition (not (c act)) (n act),
    .mul (c af) (c pos), mul3 (c act) (not (c al)) (sub (n pos) (.add (c pos) (k 1))),
    -- one state per active row; a segment starts with the nonce
    sub (sum (states.map c)) (c act),
    .mul (c af) (not (c sN)), .mul (c af) (c ix),
    -- the tag (one-hot, segment constant)
    .mul (c act) (sub (sum ((List.range 4).map fun x => c (t x))) (k 1)),
    .mul (c sT) (sub bE tagE) ] ++
  segConst.map (fun x => mul3 (c act) (not (c al)) (sub (n x) (c x)))

def cFields : List Expr :=
  [ -- field end: fe = [lastE = 0]
    .mul (c act) (.mul lastE (c fe)),
    .mul (c act) (sub (.mul lastE (c invE)) (not (c fe))),
    -- inside a field: same state, next index, a string keeps its kind
    mul3 (c act) (not (c fe)) (sub (n ix) (.add (c ix) (k 1))),
    mul3 (c act) (not (c fe)) (sub (n mth) (c mth)),
    .mul (not (c fe)) (c al),
    mul3 (c sS) (not (c fe)) (sub (n rem) (sub (c rem) (k 1))) ] ++
  states.map (fun s => mul3 (c act) (not (c fe)) (sub (n s) (c s))) ++
  [ sub (c fgo) (.mul (c fe) (not (c al))),
    -- a new field starts at index 0
    .mul (c fgo) (n ix),
    -- u32 fields: little-endian accumulation, high byte 0 (value < 2^24)
    mul3 (c fgo) u32SN (sub (n pw) (k 1)),
    mul3 (c fgo) u32SN (sub (n acc) bN),
    mul3 u32S (not (c fe)) (sub (n pw) (smul 256 (c pw))),
    mul3 u32S (not (c fe)) (sub (n acc) (.add (c acc) (.mul (n pw) bN))),
    mul3 u32S (c fe) bE,
    mul3 u32S (c fe) (.mul (c acc) (c zA)),
    mul3 u32S (c fe) (sub (.mul (c acc) (c invA)) (not (c zA))),
    -- the option tag is 0 or 1
    .mul (c sO) (.mul bE (sub bE (k 1))) ]

def cEvents : List Expr :=
  [ -- a string is done: an empty one at its length's end, or its body's last byte
    sub (c sd) (.add (mul3 (c sL) (c fe) (c zA)) (.mul (c sS) (c fe))),
    sub (c md) (.mul (c sd) (c mth)),
    -- method count: set by `sC`, decremented by each method name, `zV = [vc = 1]`
    mul3 (c act) (not (c al)) (sub (n vc) (sum [c vc, .neg (c md), .mul (c eC) (sub (c acc) (c vc))])),
    .mul (c md) (.mul (sub (c vc) (k 1)) (c zV)),
    .mul (c md) (sub (.mul (sub (c vc) (k 1)) (c invV)) (not (c zV))),
    -- the accepting ends; the segment ends exactly there
    sub (c endOK) (sum [ .mul (c sT) (c (t 1)), mul3 (c sG) (c fe) (c (t 3)),
                         mul3 (c sC) (c fe) (c zA), .mul (c md) (c zV) ]),
    .mul (c act) (sub (c al) (c endOK)),
    -- transition events
    sub (c eS) (mul3 (c sL) (c fgo) (not (c zA))),
    sub (c eC) (mul3 (c sC) (c fgo) (not (c zA))),
    sub (c eM) (.mul (c md) (not (c zV))),
    -- transitions (not at the segment's end)
    mul3 (c sN) (c fgo) (not (n sT)),
    go (mul3 (c sT) (c (t 0)) (not (n sO))),
    go (mul3 (c sT) (.add (c (t 2)) (c (t 3))) (not (n sG))),
    mul3 (c sG) (c fgo) (.mul (c (t 2)) (not (n sO))),
    go (mul3 (c sO) (not bE) (not (n sL))), go (mul3 (c sO) (not bE) (n mth)),
    go (mul3 (c sO) bE (not (n sA))),
    mul3 (c sA) (c fgo) (not (n sL)), mul3 (c sA) (c fgo) (n mth),
    .mul (c eS) (not (n sS)), .mul (c eS) (sub (n rem) (c acc)),
    .mul (c eS) (sub (n mth) (c mth)), .mul (c eS) (n uc),
    go (mul3 (c sd) (not (c mth)) (not (n sC))),
    .mul (c eM) (not (n sL)), .mul (c eM) (not (n mth)),
    .mul (c eC) (not (n sL)), .mul (c eC) (not (n mth)) ] ++
  [pE0, pED, pF0, pF4].map (fun p => .mul (c eS) (n p))

def cUtf8 : List Expr :=
  [ .mul (c sS) (sub (sum (classes.map c)) (k 1)) ] ++
  classes.map (fun x => .mul (not (c sS)) (c x)) ++
  [ -- class patterns
    .mul (c cA) (bt 7),
    .mul (c cC) (not (bt 7)), .mul (c cC) (bt 6),
    .mul (c c2) (not (bt 7)), .mul (c c2) (not (bt 6)), .mul (c c2) (bt 5),
    .mul (c c2) (sub (.mul v2E (c inv2)) (k 1)),
    .mul (c c3) (not (bt 7)), .mul (c c3) (not (bt 6)), .mul (c c3) (not (bt 5)), .mul (c c3) (bt 4),
    .mul (c c4) (not (bt 7)), .mul (c c4) (not (bt 6)), .mul (c c4) (not (bt 5)),
    .mul (c c4) (not (bt 4)), .mul (c c4) (bt 3), mul3 (c c4) (bt 2) (.add (bt 1) (bt 0)),
    -- lead bytes need no pending continuation
    mul3 (c sS) (not (c cC)) (c uc),
    .mul (c sS) (sub (c ucn) (sum [c c2, smul 2 (c c3), smul 3 (c c4), .mul (c cC) (sub (c uc) (k 1))])),
    mul3 (c sS) (not (c fe)) (sub (n uc) (c ucn)),
    mul3 (c sS) (c fe) (c ucn),
    -- E0 / ED / F0 / F4 detection
    .mul (c act) (.mul loE (c zl0)), .mul (c act) (sub (.mul loE (c il0)) (not (c zl0))),
    .mul (c act) (.mul (sub loE (k 13)) (c zl13)),
    .mul (c act) (sub (.mul (sub loE (k 13)) (c il13)) (not (c zl13))),
    .mul (c act) (.mul lo3E (c z30)), .mul (c act) (sub (.mul lo3E (c i30)) (not (c z30))),
    .mul (c act) (.mul (sub lo3E (k 4)) (c z34)),
    .mul (c act) (sub (.mul (sub lo3E (k 4)) (c i34)) (not (c z34))),
    mul3 (c sS) (not (c fe)) (sub (n pE0) (.mul (c c3) (c zl0))),
    mul3 (c sS) (not (c fe)) (sub (n pED) (.mul (c c3) (c zl13))),
    mul3 (c sS) (not (c fe)) (sub (n pF0) (.mul (c c4) (c z30))),
    mul3 (c sS) (not (c fe)) (sub (n pF4) (.mul (c c4) (c z34))),
    -- the second byte after E0 (A0–BF), ED (80–9F), F0 (90–BF), F4 (80–8F)
    mul3 (c sS) (c pE0) (not (bt 5)),
    mul3 (c sS) (c pED) (bt 5),
    .mul (mul3 (c sS) (c pF0) (not (bt 5))) (not (bt 4)),
    mul3 (c sS) (c pF4) (bt 5), mul3 (c sS) (c pF4) (bt 4) ]

def cMem : List Expr :=
  [ -- a key that is not FullAccess is never written
    mul3 (c sN) (not (c (t 1))) (sub (c pb) bE),
    sub (c aF) (.mul (c af) (c (t 1))), sub (c nF) (.mul (c sN) (c (t 1))),
    sub (c tF) (.mul (c sT) (c (t 1))) ]

def constraints : List Expr := cShape ++ cFields ++ cEvents ++ cUtf8 ++ cMem

/-! ## Interactions -/

def vpost : Expr := mid K_VPOST (c vid)

def interactions : List Interaction :=
  [ send B_VBYTES (c act) [c vid, c pos, bE],
    send B_AKMEM (c sN) [c vid, k 0, c ix, bE, c (t 1)],
    recv B_AKMEM (c sN) [c vid, c tlast, c ix, c pb, c (t 1)],
    send B_VSLOT (c aF) [c vid],
    send B_BYTES (c nF) [vpost, c pos, c pb],
    send B_BYTES (c tF) [vpost, c pos, bE],
    send B_AKC (c aF) [c vid, k 0],
    recv B_AKC (c aF) [c vid, c U] ]

/-- Access-key value bytes `≤ A7` unfolded bytes `< 2^21`; aligned height `22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.AkmV3
