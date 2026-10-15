import ZkFormal.NearV3.Tables.UnfoldA7
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.Tables.NodeStubDefs` — `nodeD1`: `nodeA7` with stub windows

Lane `v3-d1-a7b` (plan §5, R-5 → (B), items 2–3).  Definitions only (verifier-model import
rule).  `nodeD1` **extends** `nodeA7` (table 2): its columns `0 … 187`, constraints and
interactions are kept unchanged and new ones are appended, so every proved `nodeA7` / `nodeV3`
view still applies (`Assembly.tableLocal_ext`), and the new interactions use only the new buses
`SEDGE` and `NMQ`.

A **stub window** (`su = 1`, on the first row of a digest window only) is
* a child window of a branch or an extension whose child is **not revealed** (`rv = 0`), or
* the value window of a leaf or a branch whose value is **not revealed** (`tv = 0`).

It claims that the window's 32 bytes `h` (the child's hash / the value's hash, `reg 0 … 31` on
the window's first row) are not the digest of any store entry of the record's instance `τ`:
it sends `NMQ (τ, h)` (answered by `nmemV3` from `uniqD1`'s sorted digests), and it provides
the walk terminal `SEDGE (nid, I, z, ·)` (chained, use count `mSt`) at the lookup position
where the relation's `buildFor` reaches the window:
* branch child `j`: `(nid, 0)` with symbol `z = j` (the walk's nibble);
* extension child: `(nid, s)` (`s` = key nibbles, the extension's dead last-nibble target)
  with `z = SYM_WILD` (any following symbol);
* value of a leaf: `(nid, s)`; of a branch: `(nid, 0)`; with `z = SYM_END`.

`walkU`'s terminal `mT` consumes `SEDGE`; then `buildFor` over the extracted store stops at the
same place (`.hash h`, or `.ref` for the value) as the record tree.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

namespace NodeStub
open ZkFormal.NearV3.NodeV3 in
section

/-- stub window flag (first row of a window) -/
def su : Nat := 188
/-- the stub's lookup position and symbol -/
def sI : Nat := 189
def sZ : Nat := 190
/-- `SEDGE` use count (chained provider) -/
def mSt : Nat := 191
def width : Nat := 192

/-- Lookup position of the stub: `s` for an extension's child and a leaf's value, `0` else. -/
def sIE : Expr := .add (.mul (c sVH) (.mul (c tl) sE)) (.mul (c sCH) (.mul (c te) sE))

/-- Symbol of the stub: `END` (value), `SYM_WILD` (extension child), the slot (branch child). -/
def sZE : Expr :=
  sum [smul ZkFormal.Near.SYM_END (c sVH), .mul (c sCH) (smul SYM_WILD (c te)),
       .mul (c sCH) (.mul isBr jIdxE)]

def constraints : List Expr :=
  [ bool (c su),
    .mul (c su) (not (c fs)),
    .mul (c su) (not winE),
    mul3 (c su) (c sCH) (c rv),
    mul3 (c su) (c sVH) (c tv),
    .mul (c su) (sub (c sI) sIE),
    .mul (c su) (sub (c sZ) sZE) ]

def sedge (u : Expr) : List Expr := [c nid, c sI, c sZ, u]

def interactions : List Interaction :=
  [ send B_SEDGE (c su) (sedge (k 0)),
    recv B_SEDGE (c su) (sedge (c mSt)),
    send B_NMQ (c su) (c tau :: (List.range 32).map fun i => c (reg i)) ]

end
end NodeStub

/-- **`nodeD1`**: `nodeA7` with the stub windows. -/
def nodeD1 : ZkFormal.Air.Table :=
  { ZkFormal.NearV3.UnfoldA7.nodeA7 with
    width := NodeStub.width
    constraints := ZkFormal.NearV3.UnfoldA7.nodeA7.constraints ++ NodeStub.constraints
    interactions := ZkFormal.NearV3.UnfoldA7.nodeA7.interactions ++ NodeStub.interactions }

end ZkFormal.NearV3.D1
