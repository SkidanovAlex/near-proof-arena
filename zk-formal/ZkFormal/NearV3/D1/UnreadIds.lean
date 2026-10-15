import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.UnreadIds` — buses and ids of the unread-key walks (plan §5, R-5 → (B))

Lane `v3-d1-a7b` (user decision 2026-10-15: the signed spec is unchanged; `nearAirV3D1` walks
every `txKeys` entry so that its A7 count is `checkD1`'s A7ᴰ¹ measure).  Definitions only
(verifier-model import rule).  The buses are new numbers (`72 … 75`, unused by `nearAirV3` and
by the phase-1 D1 tables, below `nearBuses = 77`).

| # | bus | message | producers → consumers |
|---|---|---|---|
| 72 | `UKEYNIB` | `(w, t, sym, last)` | `kibD1` (public `PKEY` records with `w ≥ W_UNR`) → `walkU` |
| 73 | `SEDGE` | `(N, I, z, u)` | `nodeD1` stub / value-not-in-store windows (chained provider) ↔ `walkU` terminal `mT` |
| 74 | `NMQ` | `(τ, h[32])` | `nodeD1` stub windows → `nmemV3` (non-membership of `h` among the store digests of `τ`) |
| 75 | `GB` | `(s, τ, i, prev_i, cur_i, ft, st, lt, u)` | `uniqD1` (chained provider, byte `i` of entry `s` and of its predecessor) ↔ `nmemV3` |

Walk ids of the unread-key walks: `W_UNR + 2·j` (signer account) and `W_UNR + 2·j + 1`
(access key) for transaction `j` of the witness (all of them: duplicates, flag 0, invalid and
cost-overflow transactions included), `W_UNR = 2^23`: byte 2 of the id has bit 7 set, which
`kibD1` routes to `UKEYNIB`; every other public walk id (`W_TX + 2·op (+1) < 2^21`) has it
clear.

`SYM_WILD = 19` is the symbol slot of an extension's stub (any key symbol may follow).
-/

namespace ZkFormal.NearV3.D1

/-! ## Buses -/

def B_UKEYNIB : Nat := 72
def B_SEDGE : Nat := 73
def B_NMQ : Nat := 74
def B_GB : Nat := 75

/-! ## Ids -/

/-- Base of the unread-key walk ids (`W_UNR + 2·j`, `W_UNR + 2·j + 1`). -/
def W_UNR : Nat := 8388608

/-- The stub symbol of an extension whose child is not in the store (matches any symbol). -/
def SYM_WILD : Nat := 19

end ZkFormal.NearV3.D1
