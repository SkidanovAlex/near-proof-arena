import ZkFormal.NearV3.Tables.Walk
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.Tables.WalkUDefs` — `walkU`: the unread-key walks

Lane `v3-d1-a7b` (plan §5, R-5 → (B), items 1–2).  Definitions only (verifier-model import rule).

A copy of `walkV3` (`Tables/Walk.lean`, same column layout `0 … 55`) for the walks of the
transaction keys `txKeys w.txs` that `checkD1`'s main pre trie is built over (**every**
transaction's signer account and access key, read or not).  The candidates' walks stay in
`walkV3`.  Deltas:
* the key symbols arrive on `UKEYNIB` (from `kibD1`, public walk ids `≥ W_UNR`) instead of
  `KEYNIB`;
* every walk is on the main instance (`τ = 0` on the `START` row);
* a fifth mode `mT` — **stub**: at the lookup position `(N, I)` a `SEDGE (N, I, z, u)` of
  `nodeD1` (chained: receive `u`, send `u + 1`), `z = sym` (`mW = 0`: a branch child slot, or
  `END` at a value slot) or `z = SYM_WILD` (`mW = 1`: an extension's child).  The relation's
  `buildFor` stops there too: the child (value) hash is not in the store (`NMQ`).  A stub is
  terminal: the remaining symbols are drained (`mD`), as after an absent terminal;
* no `FINAL`: nothing consumes an unread walk's result (the walk only has to exist, which the
  `UKEYNIB` balance forces), so `fk`, `kk` are left unconstrained.

A walk of `walkU` therefore ends at a value (`VAL`), an absence (`mK`, `mB`), or a stub (`mT`):
the key's path in the record tree either is determined (as the relation's `find`), or stops at
an unrevealed child or value whose hash is not in the store.
-/

namespace ZkFormal.NearV3.D1.WalkU

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.WalkV3
open ZkFormal.NearV3.D1 (B_UKEYNIB B_SEDGE SYM_WILD)

/-- stub mode -/
def mT : Nat := 56
/-- stub of an extension child (wildcard symbol) -/
def mW : Nat := 57
def width : Nat := 58

/-- absent and stub terminals -/
def absU : Expr := sum [c mK, c mB, c mT]
def modesU : List Nat := [mS, mK, mB, mD, mT]

def boolColsU : List Nat := boolCols ++ [mT, mW]

/-- the stub's symbol slot -/
def zE : Expr := .add (c sym) (.mul (c mW) (sub (k SYM_WILD) (c sym)))

/-- The constraints after the booleanity ones. -/
def tailC : List Expr :=
  [ sub (c gK) (sub (c act) (c ws)),
    sub (sum (modesU.map c)) (c act),
    .mul (c ws) (not (c act)), .mul (c we) (not (c act)),
    .mul (c ws) (c we),
    -- a walk starts with the START step from (head of τ = 0) at symbol index 0
    .mul (c ws) (not (c mS)),
    .mul (c ws) (c tau),
    .mul (c ws) (sub (c nI) (c tau)), .mul (c ws) (sub (c sym) (k SYM_START)),
    .mul (c ws) (c t),
    -- the first row starts a walk, or the table is empty (no transaction: no unread walk)
    .mul .isFirst (sub (c act) (c ws)),
    .mul .isLast (.mul (c act) (not (c we))),
    -- inside a walk
    mul3 (c act) (not (c we)) (not (n act)),
    mul3 (c act) (not (c we)) (n ws),
    mul3 (c act) (not (c we)) (sub (n w) (c w)),
    mul3 (c act) (not (c we)) (sub (n tau) (c tau)),
    mul3 (c act) (not (c we)) (sub (n t) (.add (c t) (c gK))),
    -- a step leads to the next lookup position; after a step comes a step or a terminal
    mul3 (c mS) (not (c we)) (sub (n nN) (c nN2)),
    mul3 (c mS) (not (c we)) (sub (n nI) (c nI2)),
    mul3 (c mS) (not (c we)) (n mD),
    -- after an absent / stub terminal or a drain row: drain
    .mul (.add absU (c mD)) (.mul (not (c we)) (not (n mD))),
    -- the key's last symbol is END
    .mul (c we) (sub (c sym) (k SYM_END)),
    -- step: the edge carries the symbol; kinds DOWN/KEY (non-final) or VAL (final)
    .mul (c mS) (sub (c nib) (c sym)),
    mul3 (c mS) (not (c we)) (.mul (c ek) (sub (c ek) (k 1))),
    mul3 (c mS) (c we) (sub (c ek) (k ZkFormal.NearV3.EK_VAL)),
    -- absent by key: a KEY or LEND edge with a different symbol
    .mul (c mK) (.mul (sub (c ek) (k ZkFormal.NearV3.EK_KEY)) (sub (c ek) (k ZkFormal.NearV3.EK_LEND))),
    .mul (c mK) (sub (.mul (sub (c sym) (c nib)) (c inv)) (k 1)),
    -- absent at a branch (position 0): END ⇒ no value; nibble ⇒ bit sym of bm is 0
    .mul (c mB) (c nI),
    mul3 (c mB) (c we) (c hv),
    sub selSum (.mul (c mB) (not (c we))),
    mul3 (c mB) (not (c we)) (sub selIdx (c sym)),
    selBit,
    -- the wildcard flag is a stub flag
    .mul (c mW) (not (c mT)),
    -- after a walk: another walk or padding
    mul3 (c we) (n act) (not (n ws)),
    mul3 .isTransition (not (c act)) (n act) ]

def constraints : List Expr := boolColsU.map (fun x => bool (c x)) ++ tailC

def sedge (uu : Expr) : List Expr := [c nN, c nI, zE, uu]

def interactions : List Interaction :=
  [ recv B_UKEYNIB (c gK) [c w, c t, c sym, c we],
    recv ZkFormal.Near.B_EDGE (.add (c mS) (c mK)) (edge (c u)),
    send ZkFormal.Near.B_EDGE (.add (c mS) (c mK)) (edge (.add (c u) (k 1))),
    recv ZkFormal.NearV3.B_BMAP (c mB) (bmap (c ub)),
    send ZkFormal.NearV3.B_BMAP (c mB) (bmap (.add (c ub) (k 1))),
    recv B_SEDGE (c mT) (sedge (c u)),
    send B_SEDGE (c mT) (sedge (.add (c u) (k 1))) ]

/-- `≤ 2·NT0 = 8192` walks of `≤ 200` rows (access keys `[2] ‖ id ‖ [2] ‖ pk`, ED25519 keys
only in D1), `< 2^21` rows, padded to the roll-aligned height `2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.WalkU
