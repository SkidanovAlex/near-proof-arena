import ZkFormal.NearV3.D1.Tables.RelayDefs
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.Tables.KibUDefs` — `kibD1`: `kibV3` routing the unread-key walks

Lane `v3-d1-a7b` (plan §5, R-5 → (B), item 1).  Definitions only (verifier-model import rule).

`kibV3` (table 27) relays every public `PKEY (w₀, w₁, w₂, t, sym, last)` record to
`KEYNIB (w, t, sym, last)`, `w = w₀ + 2⁸w₁ + 2¹⁶w₂`.  `kibD1` decomposes the byte `w₂` into
bits `wb 0 … 7` and relays a record of an **unread-key walk** (`w ≥ W_UNR = 2^23`, i.e. bit 7
of `w₂` set) to `UKEYNIB` (`walkU`) instead; every other record (the candidates' walks,
`w < 2^21`) goes to `KEYNIB` (`walkV3`) as before.
-/

namespace ZkFormal.NearV3.D1.KibD1

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1.KibV3
open ZkFormal.NearV3.D1 (B_PKEY B_UKEYNIB)

def wb (j : Nat) : Nat := 7 + j
def width : Nat := 15

/-- the routing bit (`w ≥ 2^23`) -/
def uE : Expr := c (wb 7)

def constraints : List Expr :=
  (bool (c act) :: (List.range 8).map (fun j => bool (c (wb j)))) ++
  [ .mul (c act) (sub (c w2) (bits (fun j => c (wb j)) 0 8)) ]

def interactions : List Interaction :=
  [ recv B_PKEY (c act) [c w0, c w1, c w2, c t, c sym, c last],
    send B_KEYNIB (.mul (c act) (not uE)) [wE, c t, c sym, c last],
    send B_UKEYNIB (.mul (c act) uE) [wE, c t, c sym, c last] ]

/-- `≤ NT0 · (132 + 200) + NT0 · 132` candidate and credit nibbles, plus
`≤ NT0 · (132 + 264)` unread-key nibbles, `< 2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.KibD1
