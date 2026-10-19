import NearSpecV3.Wasm.Exec
import WasmBase.Chips
/-!
# WasmBase.Check — verifier-side eligibility checker and code records

The verifier runs this on the prepared program (`NearSpecV3.Wasm.prepare`) to obtain the public code
records of `wasmBaseAir`.  It returns `none` outside the domain.  All domain conditions are explicit
and decidable:

* **D1 family:** the function has no params, at most 64 declared locals (i32/i64), at most one
  result (i32/i64), and every instruction is in family F1: `i32/i64.const`, `drop`, `select`,
  `local.get/set/tee` (index in range), the numeric opcodes of `isFamilyNum`, `block`, `loop` (no
  result), `end`, `br`, `br_if`, `return`.
* **D2 gas:** every gas entry is `none` or `some (k, fee)` with `fee.l = 0` and
  `fee.c = units · regular_op_cost`, `units < 2^16`.
* **D3 no-discard branches:** at every `br l` / taken `br_if l` to a non-function label the static
  height equals `label.height + label.arity`, and at every exit of the function (`end` of the body,
  `return`, `br`/`br_if` to the function label) it equals the result arity.  So no branch drops
  operand-stack values (the stack channel needs no "kill" rows).
* **D4 dead code:** after an unconditional transfer the next instruction is `end`.
* **D5 sizes:** code length `< 2^20`, static heights `< 2^16`.

The checker computes a static label stack `L pc` and height `H pc` per pc (`analyze`) and then
re-verifies every local transition (`verifyAt`); the base-faithful proof uses only `verifyAt`.
-/
namespace WasmBase
open NearSpecV3.Wasm

deriving instance DecidableEq for NearSpecV3.Wasm.Label

/-- Numeric opcodes of family F1. -/
def isFamilyNum (op : Nat) : Bool :=
  (0x45 ≤ op && op ≤ 0x5A) ||
  (0x6A ≤ op && op ≤ 0x78) || (0x7C ≤ op && op ≤ 0x8A)

/-- Operands popped by a numeric family opcode. -/
def numPops (op : Nat) : Nat := if op = 0x45 ∨ op = 0x50 then 1 else 2

/-- Width tag of a numeric family opcode's operands (1 = i64). -/
def numIs64 (op : Nat) : Bool :=
  (0x50 ≤ op && op ≤ 0x5A) || (0x7C ≤ op && op ≤ 0x8A)

/-- Static control kind of an instruction at a pc, given the static label stack. -/
inductive Kind where
  | straight (pops pushes : Nat)
  | next          -- block / loop / nested end: pc + 1, labels change, stack unchanged
  | jump (tgt : Nat)
  | jumpIf (tgt : Nat)
  | halt
  | haltIf
  deriving Repr, DecidableEq, Inhabited

structure CheckOut where
  /-- defined-function index -/
  fn : Nat
  labels : Array (List Label)
  heights : Array Nat
  arity : Nat
  /-- 1 if the result is i64 -/
  resTag : Nat
  records : Array (List Nat)
  maxFee : Nat
  /-- declared local types (1 = i64) -/
  localTags : List Nat
  deriving Inhabited

def rootLabel (pf : PFunc) : Label :=
  { target := pf.code.size, arity := pf.type.results.size, height := 0, isLoop := false }

/-- Fee units of a gas entry (D2). -/
def feeUnits (cfg : NearCfg) : Option (Option (IK × Fee)) → Option Nat
  | some none => some 0
  | some (some (_, fee)) =>
    if fee.l = 0 ∧ cfg.regularOpCost ≠ 0 ∧ fee.c % cfg.regularOpCost = 0 ∧
        fee.c / cfg.regularOpCost < 2 ^ 16 then some (fee.c / cfg.regularOpCost) else none
  | none => none

/-- Kind of the instruction at `pc` under label stack `ls` and height `h`. -/
def kindOf (ls : List Label) : Instr → Option Kind
  | .i32Const _ | .i64Const _ => some (.straight 0 1)
  | .drop => some (.straight 1 0)
  | .select _ => some (.straight 3 1)
  | .localGet _ => some (.straight 0 1)
  | .localSet _ => some (.straight 1 0)
  | .localTee _ => some (.straight 1 1)
  | .num op => if isFamilyNum op then some (.straight (numPops op) 1) else none
  | .block _ | .loop none => some .next
  | .end_ => match ls with
    | [_] => some .halt
    | _ :: _ :: _ => some .next
    | [] => none
  | .br l => if l + 1 ≥ ls.length then some .halt
    else (ls[l]?).map fun lab => .jump lab.target
  | .brIf l => if l + 1 ≥ ls.length then some .haltIf
    else (ls[l]?).map fun lab => .jumpIf lab.target
  | .ret => some .halt
  | _ => none

/-- Forward pass: static labels and heights (`none` = outside D1/D4). `dead` = after an
unconditional transfer. -/
def analyze (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
  let n := pf.code.size
  let mut ls : List Label := [rootLabel pf]
  let mut h : Nat := 0
  let mut dead := false
  let mut L : Array (List Label) := #[]
  let mut H : Array Nat := #[]
  for pc in [0:n] do
    let some ins := pf.code[pc]? | return none
    if dead then
      -- a dead `end` gets the height its successor expects (`label.height + label.arity`)
      match ins, ls with
      | .end_, lab :: rest@(_ :: _) =>
        L := L.push ls; H := H.push (lab.height + lab.arity)
        ls := rest; h := lab.height + lab.arity; dead := false
      | .end_, [lab] =>
        L := L.push ls; H := H.push (lab.height + lab.arity); dead := false
      | _, _ => return none
    else
      L := L.push ls
      H := H.push h
      match ins with
      | .block bt =>
        match pf.endOf[pc]? with
        | some e =>
          ls := { target := e + 1, arity := (btResults bt).size, height := h, isLoop := false } :: ls
        | none => return none
      | .loop none =>
        ls := { target := pc + 1, arity := 0, height := h, isLoop := true } :: ls
      | .end_ =>
        match ls with
        | _ :: rest@(_ :: _) => ls := rest
        | _ => dead := true
      | .br _ | .ret => dead := true
      | .brIf _ => h := h - 1
      | i =>
        match kindOf ls i with
        | some (.straight pops pushes) =>
          if h < pops then return none
          h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations of one pc (the only facts the proofs use). -/
def verifyAt (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
  match pf.code[pc]?, L[pc]?, H[pc]? with
  | some ins, some ls, some h =>
    let fnAr := pf.type.results.size
    let atQ (q : Nat) (ls' : List Label) (h' : Nat) : Bool :=
      decide (q < pf.code.size) && decide (L[q]? = some ls') && decide (H[q]? = some h')
    match ins with
    | .block bt =>
      match pf.endOf[pc]? with
      | some e => atQ (pc + 1)
          ({ target := e + 1, arity := (btResults bt).size, height := h, isLoop := false } :: ls) h
      | none => false
    | .loop none => atQ (pc + 1) ({ target := pc + 1, arity := 0, height := h, isLoop := true } :: ls) h
    | .end_ => match ls with
      | [_] => decide (h = fnAr)
      | _ :: rest@(_ :: _) => atQ (pc + 1) rest h
      | [] => false
    | .ret => decide (h = fnAr)
    | .br l =>
      if l + 1 ≥ ls.length then decide (h = fnAr)
      else match ls[l]? with
        | some lab => decide (h = lab.height + lab.arity) &&
            atQ lab.target (if lab.isLoop then ls.drop l else ls.drop (l + 1)) h
        | none => false
    | .brIf l =>
      decide (1 ≤ h) && atQ (pc + 1) ls (h - 1) &&
      (if l + 1 ≥ ls.length then decide (h - 1 = fnAr)
       else match ls[l]? with
        | some lab => decide (h - 1 = lab.height + lab.arity) &&
            atQ lab.target (if lab.isLoop then ls.drop l else ls.drop (l + 1)) (h - 1)
        | none => false)
    | i => match kindOf ls i with
      | some (.straight pops pushes) => decide (pops ≤ h) && atQ (pc + 1) ls (h - pops + pushes)
      | _ => false
  | _, _, _ => false

/-- 16-bit limbs of a value. -/
def limbs4 (x : Nat) : List Nat := [x % 65536, x / 65536 % 65536, x / 2 ^ 32 % 65536, x / 2 ^ 48 % 65536]

/-- Code record `[pc, op, h, fee, x0, x1, x2, x3]` (bus FETCH). -/
def recordOf (ls : List Label) (h fee pc : Nat) (ins : Instr) : Option (List Nat) :=
  let mk (op : Nat) (xs : List Nat) := some ([pc, op, h, fee] ++ xs)
  match ins with
  | .i32Const v => mk 0x41 (limbs4 v.toNat)
  | .i64Const v => mk 0x42 (limbs4 v.toNat)
  | .drop => mk 0x1A [0, 0, 0, 0]
  | .select _ => mk 0x1B [0, 0, 0, 0]
  | .localGet x => mk 0x20 [x, 0, 0, 0]
  | .localSet x => mk 0x21 [x, 0, 0, 0]
  | .localTee x => mk 0x22 [x, 0, 0, 0]
  | .num op => if isFamilyNum op then mk op [0, 0, 0, 0] else none
  | i => match kindOf ls i with
    | some .next => mk Chips.Ctrl.opNext [0, 0, 0, 0]
    | some (.jump t) => mk Chips.Ctrl.opJump [t, 0, 0, 0]
    | some (.jumpIf t) => mk Chips.Ctrl.opJif [t, 0, 0, 0]
    | some .halt => mk Chips.Ctrl.opHalt [0, 0, 0, 0]
    | some .haltIf => mk Chips.Ctrl.opHif [0, 0, 0, 0]
    | _ => none

/-- D1/D5 basic shape (decidable). -/
def basicOk (pf : PFunc) : Bool :=
  decide (pf.type.params.size = 0) && decide (pf.locals.size ≤ 64) && decide (pf.type.results.size ≤ 1) &&
  pf.type.results.all (fun t => t == .i32 || t == .i64) &&
  pf.locals.all (fun t => t == .i32 || t == .i64) &&
  pf.code.all (fun i => match i with
    | .localGet x | .localSet x | .localTee x => decide (x < pf.locals.size)
    | _ => true) &&
  decide (pf.code.size < 2 ^ 20) && decide (pf.gas.size = pf.code.size)

/-- Static structure: sizes, entry, every local transition, height bound. -/
def structOk (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAt pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

def recordAt (cfg : NearCfg) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) :
    Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee => recordOf (L[pc]?.getD []) (H[pc]?.getD 0) fee pc ins
  | _, _ => none

/-- Entry point: the eligibility check of defined function `fn` (domain D1–D5). -/
def check (cfg : NearCfg) (p : Prepared) (fn : Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk pf then
      match analyze pf with
      | none => none
      | some (L, H) =>
        if structOk pf L H then
          match (List.range pf.code.size).mapM (recordAt cfg pf L H) with
          | none => none
          | some recs =>
            some { fn, labels := L, heights := H, arity := pf.type.results.size,
                   localTags := pf.locals.toList.map fun t => if t == .i64 then 1 else 0,
                   resTag := if pf.type.results[0]? == some .i64 then 1 else 0,
                   records := recs.toArray,
                   maxFee := (recs.map fun r => r.getD 3 0).foldl max 0 }
        else none
    else none

end WasmBase
