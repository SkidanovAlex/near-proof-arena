import WasmBase.Chips
/-!
# WasmBase.HostChip — the HOST chip and the host-function table (direct-Wasm PQ base layer)

First slice of README §14.2: a `call` of an imported function is a straight-line instruction whose
signature is taken from a **fixed host table**, bound through a cached trace exactly like FUNC.
Every domain condition is explicit and decidable.

A HOST row (`np ≤ 2`, `ar ≤ 1`):

* consumes `np` values from the operand stack (channel space 0, in argument order);
* sends one request `[ts, hid, S, a0lo, a0hi, a1lo, a1hi, np]` on `HOSTQ`;
* receives one response `[ts, st, rlo, rhi, glo, ghi, ar, 0]` on `HOSTR`, where `st = 0` means
  success and `st = 1` means the host aborted (`g := g_after` still applies);
* produces `(1 − st)·ar` result words at the stack base `sb + h − np`;
* moves to `pc + 1` (`st = 0`) or stays at `pc` with `halted = 2` (`st = 1`);
* advances `S` by `fee + hostK`, `hostK` being the host ext cost in regular-op units; `g_after` is
  the budget after the spec's `g := remaining`.

`HOSTQ` / `HOSTR` are answered inside the trace by a witness **oracle** table `HOSTO` (one row per
call), whose rows are exactly the abstract host responses.  The soundness statement is therefore
relative to that oracle: the proof says "if the state side supplies these responses, the spec `run`
takes this host-call step".  Joining with the state proof (README §14.2) replaces `HOSTO` by the
state tables on the same buses.  Keeping the oracle in-trace also makes the native bus pre-check
exact rather than partial.

The HOST table is not appended to `wasmBaseAir`: that would shift every table index of the proved
F1/memory/globals/calls slice.  Host programs use `wasmBaseHostAir`, which appends HOST (22),
HOSTO (23) and the cached HOSTT table (24).
-/
namespace WasmBase
namespace Chips
open Expr

/-- Cross-proof host request / response, and the cached host table. -/
def busHostQ : Nat := 7
def busHostR : Nat := 8
def busHostT : Nat := 9

/-- Fixed host table `(id, name, #params, #results)`; `np ≤ 2`, `ar ≤ 1` (the message shape). -/
def hostFns : List (Nat × String × Nat × Nat) :=
  [(0, "block_index", 0, 1), (1, "block_timestamp", 0, 1), (2, "epoch_height", 0, 1),
   (3, "storage_usage", 0, 1), (4, "prepaid_gas", 0, 1), (5, "used_gas", 0, 1),
   (6, "register_len", 1, 1), (7, "panic", 0, 0)]

/-- Host id of an imported function name (`none`: not in the fixed table ⇒ outside the domain). -/
def hostIdOf (name : String) : Option Nat :=
  (hostFns.find? (fun x => x.2.1 = name)).map (·.1)

/-- Signature `(np, ar)` of a host id. -/
def hostSig (id : Nat) : Option (Nat × Nat) :=
  (hostFns.find? (fun x => x.1 = id)).map fun x => (x.2.2.1, x.2.2.2)

/-- The cached host-table row `[id, np, ar, 0, 0, 0, 0, 0]`. -/
def hostRow (id np ar : Nat) : List Nat := [id, np, ar, 0, 0, 0, 0, 0]

/-- FETCH opcode of an import call (not a Wasm opcode of the F1 family). -/
def opHost : Nat := 0x1FF

namespace Host
def act : Nat := 5
def hid : Nat := 6
def np : Nat := 7
def ar : Nat := 8
/-- response status: 0 = success, 1 = abort -/
def st : Nat := 9
def nres : Nat := 10
def ga : Nat := 11     -- g_after limbs 11..14
def rb : Nat := 15     -- result limbs 15..18
def pf (j : Nat) : Nat := 19 + j
def tagP (j : Nat) : Nat := 21 + 7 * j
def P (j : Nat) : Nat := 22 + 7 * j    -- 4 limbs
def tP (j : Nat) : Nat := 26 + 7 * j
def hP (j : Nat) : Nat := 27 + 7 * j
def kSb : Nat := 35
def kCid : Nat := 36

def cols : List String := headerCols ++
  ["act", "hid", "np", "ar", "st", "nres", "ga0", "ga1", "ga2", "ga3",
   "r0", "r1", "r2", "r3", "pf0", "pf1",
   "tagP0", "P0_0", "P0_1", "P0_2", "P0_3", "tP0", "hP0",
   "tagP1", "P1_0", "P1_1", "P1_2", "P1_3", "tP1", "hP1"] ++ frameCols

def sbNew : Expr := v kSb + v cH - v np
def aLo (j : Nat) : Expr := v (P j) + 65536 * v (P j + 1)
def aHi (j : Nat) : Expr := v (P j + 2) + 65536 * v (P j + 3)
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def ok : Expr := 1 - v st

/-! Constraints.  `S` advances by the instruction `fee` only: host ext costs are burnt by the state
side (`sync`) and returned as `g_after`, not counted in instruction-gas units.  Each constraint is
named so its membership is `by simp`. -/
def cAct : Expr := bool (v act)
def cSt : Expr := bool (v st)
def cP0 : Expr := bool (v (pf 0))
def cP1 : Expr := bool (v (pf 1))
/-- `pf1 = pf0·pf1` (with `pf0` a bit: `pf1·(1−pf0) = 0`). -/
def cP1P0 : Expr := v (pf 1) - v (pf 0) * v (pf 1)
def cNp : Expr := v np - v (pf 0) - v (pf 1)
def cAr : Expr := bool (v ar)
/-- `nres = (1−st)·ar`. -/
def cNres : Expr := v nres - v ar + v st * v ar
def cGLo : Expr := gLo - (v ga + 65536 * v (ga + 1))
def cGHi : Expr := gHi - (v (ga + 2) + 65536 * v (ga + 3))
def cRLo : Expr := rLo - (v rb + 65536 * v (rb + 1))
def cRHi : Expr := rHi - (v (rb + 2) + 65536 * v (rb + 3))
/-- The argument padding: an absent argument has zero tag and zero limbs; a present one has tag 1. -/
def cPad0 : Expr := v (tagP 0) - v (pf 0) * v (tagP 0)
def cPad1 : Expr := v (tagP 1) - v (pf 1) * v (tagP 1)
def cTag0 : Expr := v (pf 0) * v (tagP 0) - v (pf 0)
def cTag1 : Expr := v (pf 1) * v (tagP 1) - v (pf 1)

def cPadL (j : Nat) : List Expr :=
  (List.range 4).map fun i => v (P j + i) - v (pf j) * v (P j + i)

def constraints : List Expr :=
  [cAct, cSt, cP0, cP1, cP1P0, cNp, cAr, cNres, cGLo, cGHi, cRLo, cRHi, cPad0, cPad1, cTag0, cTag1] ++
  cPadL 0 ++ cPadL 1

def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * v st) (v kSb) (v kCid) (v act),
   fetch (v cPc) (Expr.c opHost) (v cH) (v cFee) [v hid, v np, v ar, 0] (v act),
   ⟨busHostT, true, v act, [v hid, v np, v ar, 0, 0, 0, 0, 0]⟩,
   ⟨busHostQ, true, v act, [v cTs, v hid, v cS, aLo 0, aHi 0, aLo 1, aHi 1, v np]⟩,
   ⟨busHostR, false, v act, [v cTs, v st, rLo, rHi, gLo, gHi, v ar, 0]⟩] ++
  (List.range 4).map (fun i => r16 (v (ga + i)) (v act)) ++
  (List.range 4).map (fun i => r16 (v (rb + i)) (v act)) ++
  [r16 (v (P 0)) (v act), r16 (v (P 0 + 1)) (v act), r16 (v (P 0 + 2)) (v act),
   r16 (v (P 0 + 3)) (v act), r16 (v (P 1)) (v act), r16 (v (P 1 + 1)) (v act),
   r16 (v (P 1 + 2)) (v act), r16 (v (P 1 + 3)) (v act)] ++
  ((List.range 2).flatMap fun j =>
    [stkRecv (sbNew + Expr.c j) (v (tagP j)) (limbsOf (P j)) (v (tP j)) (v (pf j))] ++
    timeChk (v cTs) (v (tP j)) (v (hP j)) (v (pf j))) ++
  [stkSend sbNew 1 (limbsOf rb) (v cTs) (v nres)]

def table : Table := ⟨"HOST", cols, constraints, inters⟩
end Host

namespace HostTab
def mult : Nat := 8
def cachedWidth : Nat := 8
def table : Table := ⟨"HOSTT", ["id", "np", "ar", "z0", "z1", "z2", "z3", "z4", "mult"], [],
  [⟨busHostT, false, v mult, (List.range 8).map v⟩]⟩
end HostTab

/-! The witness oracle of the host responses (one row per host call): it absorbs the HOSTQ request
and emits the HOSTR response; on the joined proof the state side plays this role. -/
namespace HostO
def q (i : Nat) : Nat := i        -- request columns 0..7
def st : Nat := 8
def rb : Nat := 9                 -- response word limbs 9..12
def ga : Nat := 13                -- g_after limbs 13..16
def ar : Nat := 17
def mult : Nat := 18
def cols : List String := ["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7", "st",
  "r0", "r1", "r2", "r3", "g0", "g1", "g2", "g3", "ar", "mult"]
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def table : Table := ⟨"HOSTO", cols, [], [
  ⟨busHostQ, false, v mult, (List.range 8).map (fun i => v (q i))⟩,
  ⟨busHostR, true, v mult, [v (q 0), v st, rLo, rHi, gLo, gHi, v ar, 0]⟩]⟩
end HostO

end Chips

/-- The direct-Wasm base AIR **with host calls**: the proved F1/memory/globals/calls tables plus
HOST (22), the response oracle HOSTO (23) and the cached HOSTT table (24). -/
def wasmBaseHostAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++ [Chips.Host.table, Chips.HostO.table, Chips.HostTab.table]
    numPub := (wasmBaseAir nloc ngl).numPub }

end WasmBase
