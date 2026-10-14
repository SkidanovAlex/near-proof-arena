import ZkFormal.NearV3.Rcpt.Tables.RcptRDefs
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.Tables.RcptD1Defs` — `rcptV3D1`: the receipt table after the transactions

Lane `v3-d1-tables` (V3-D1-DESIGN §2.2/§2.3, G11–G14).  Definitions only.

`RcptV3.tableQ` (`nearAirV3` table 16) with the same columns, the same constraint and
interaction *positions*, and these expressions replaced (`replC`, `replI`); everything else
is `tableQ`'s, verbatim:

| | `tableQ` | `tableQD1` | why |
|---|---|---|---|
| running tokens, first row | `tok_i = 0` | `tok_i = TOK0_i` (public `u128`) | the transactions and local receipts burnt `TOK0` first (G12) |
| body offset, first row | `o2 = 8` | `o2 = O0` (public `u32`) | the refunds of the incoming receipts follow `u32 |newTxs| ‖ newTxs ‖ u32 n_out ‖ forwarded ‖ local refunds` (G13) |
| receipt count, last row | `r + rowE = PH_N` | `r + rowE + M0 = PH_N` | `PH_N` counts all outcome leaves (`mrkV3` reads it) |
| `MEM` write time | `r + 1` | `r + 1 + T0` | the `txV3` ops (times `1 … T0`) come first (G14) |
| deposit age (first `DEP` row) | `r − tprev = age`, 13 bits `xb53…65` | `r + T0 − tprev = age`, 14 bits `xb52…65` | `r + T0 ≤ 4481 + 8192 < 2^14` (`xb52` is free on that row) |
| `MPOS` leaf position | `r` | `r + M0` | leaves `0 … M0 − 1` are the transaction and local outcomes (G11) |

The receipt index `r` itself still starts at `0`: it keys the walk ids (`r`, `W_AK + r`), the
SHA ids (`PEO(r)`, `LEAF(r)`, `RID(r)`), `RIDS (r, ·)` and `SREC`, which therefore keep their
D0a ranges (no collision with `W_QV` or with the transaction walks).  With `M0 = T0 = TOK0 = 0`
and `O0 = 8` the table is `tableQ` on the same trace (the D0a statement).
-/

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.RcptV3
  ZkFormal.NearV3.D1

/-- `u32` / `u128` little-endian public header values. -/
def pubLE (off len : Nat) : Expr := sum ((List.range len).map fun x => smul (256 ^ x) (.pub (off + x)))
def m0E : Expr := pubLE E_M0 4
def t0E : Expr := pubLE E_T0 4
def o0E : Expr := pubLE E_O0 4

/-- The replaced constraints `(tableQ's, tableQD1's)`. -/
def substC : List (Expr × Expr) :=
  (List.range 16).map (fun i =>
    (.mul .isFirst (c (tok i)), .mul .isFirst (sub (c (tok i)) (.pub (E_TOK0 + i))))) ++
  [ (.mul .isFirst (sub (c o2) (k 8)), .mul .isFirst (sub (c o2) o0E)),
    (.mul (c lastR) (sub (.add (c r) rowE) nPubE), .mul (c lastR) (sub (sum [c r, rowE, m0E]) nPubE)),
    (mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13)),
     mul3 dp (c fs) (sub (sub (.add (c r) t0E) (c tprev)) (bitsX 52 14))) ]

/-- The replaced interactions. -/
def substI : List (Interaction × Interaction) :=
  [ (send B_MEM (c sDEP) [c kslot, .add (c r) (k 1), c idx, aftE, c lk, c st],
     send B_MEM (c sDEP) [c kslot, sum [c r, k 1, t0E], c idx, aftE, c lk, c st]),
    (send B_MPOS (c rf) [k 0, c r, mid K_LEAF (c r), k 68],
     send B_MPOS (c rf) [k 0, .add (c r) m0E, mid K_LEAF (c r), k 68]) ]

def replC (e : Expr) : Expr := ((substC.find? (·.1 == e)).map (·.2)).getD e
def replI (i : Interaction) : Interaction := ((substI.find? (·.1 == i)).map (·.2)).getD i

/-- **`rcptV3D1`** (`nearAirV3D1` table 16). -/
def tableQD1 : Table :=
  { tableQ with constraints := tableQ.constraints.map replC,
                interactions := tableQ.interactions.map replI }

end ZkFormal.NearV3.D1.RcptD1
