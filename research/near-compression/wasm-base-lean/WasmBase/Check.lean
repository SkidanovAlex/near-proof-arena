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
  result), `end`, `br`, `br_if`, `return`, and the integer loads/stores (`isLoadOp`, `isStoreOp`)
  with a static offset `< 2^32`, and `global.get/set` (index `< 2^16`; the index is in range and the
  global numeric by validation, and the proof only uses the live global message).  No `memory.grow` / `memory.size` / bulk memory: the memory size is
  the configuration's initial size for the whole run.
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

/-- Integer loads `i32/i64.load*` (`0x28, 0x29, 0x2C‥0x35`; no float loads). -/
def isLoadOp (op : Nat) : Bool := op == 0x28 || op == 0x29 || (0x2C ≤ op && op ≤ 0x35)

/-- Integer stores `i32/i64.store*` (`0x36, 0x37, 0x3A‥0x3E`; no float stores). -/
def isStoreOp (op : Nat) : Bool := op == 0x36 || op == 0x37 || (0x3A ≤ op && op ≤ 0x3E)

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
  /-- local types, params first (1 = i64) -/
  localTags : List Nat
  /-- number of params and of locals (params included) -/
  np : Nat
  nl : Nat
  /-- the spec's stack-budget charge of a call (`stackCharge`) -/
  charge : Nat
  /-- prologue gas units (`prologueGas / regular_op_cost`) -/
  prologue : Nat
  deriving Inhabited

/-- Opcode of a call record (bus FETCH). -/
def opCall : Nat := 0x10

/-- `(params, results)` of a defined-function call target (`none`: an import or out of range). -/
def sigOf (p : Prepared) (fi : Nat) : Option (Nat × Nat) :=
  if p.m.imports.size ≤ fi then (p.funcs[fi - p.m.imports.size]?).map fun pf =>
    (pf.type.params.size, pf.type.results.size) else none

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
  | .globalGet x => if x < 2 ^ 16 then some (.straight 0 1) else none
  | .globalSet x => if x < 2 ^ 16 then some (.straight 1 0) else none
  | .num op => if isFamilyNum op then some (.straight (numPops op) 1) else none
  | .load op _ off => if isLoadOp op ∧ off < 2 ^ 32 then some (.straight 1 1) else none
  | .store op _ off => if isStoreOp op ∧ off < 2 ^ 32 then some (.straight 2 0) else none
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
def analyze (p : Prepared) (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
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
      | .call fi =>
        match sigOf p fi with
        | some (np, ar) =>
          if h < np then return none
          h := h - np + ar
        | none => return none
      | i =>
        match kindOf ls i with
        | some (.straight pops pushes) =>
          if h < pops then return none
          h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations of one pc (the only facts the proofs use). -/
def verifyAt (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
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
    | .call fi => match sigOf p fi with
      | some (np, ar) => decide (np ≤ h) && atQ (pc + 1) ls (h - np + ar)
      | none => false
    | i => match kindOf ls i with
      | some (.straight pops pushes) => decide (pops ≤ h) && atQ (pc + 1) ls (h - pops + pushes)
      | _ => false
  | _, _, _ => false

/-- 16-bit limbs of a value. -/
def limbs4 (x : Nat) : List Nat := [x % 65536, x / 65536 % 65536, x / 2 ^ 32 % 65536, x / 2 ^ 48 % 65536]

/-- Code record `[pc, op, h, fee, x0, x1, x2, x3]` (bus FETCH) at global pc `pc`; jump targets are
global (`off` = the function's code offset; the labels are local). -/
def recordOf (off : Nat) (cinfo : Nat → Option Nat) (ls : List Label) (h fee pc : Nat) (ins : Instr) :
    Option (List Nat) :=
  let mk (op : Nat) (xs : List Nat) := some ([pc, op, h, fee] ++ xs)
  match ins with
  | .i32Const v => mk 0x41 (limbs4 v.toNat)
  | .i64Const v => mk 0x42 (limbs4 v.toNat)
  | .drop => mk 0x1A [0, 0, 0, 0]
  | .select _ => mk 0x1B [0, 0, 0, 0]
  | .localGet x => mk 0x20 [x, 0, 0, 0]
  | .localSet x => mk 0x21 [x, 0, 0, 0]
  | .localTee x => mk 0x22 [x, 0, 0, 0]
  | .globalGet x => if x < 2 ^ 16 then mk 0x23 [x, 0, 0, 0] else none
  | .globalSet x => if x < 2 ^ 16 then mk 0x24 [x, 0, 0, 0] else none
  | .num op => if isFamilyNum op then mk op [0, 0, 0, 0] else none
  | .load op _ off => if isLoadOp op ∧ off < 2 ^ 32 then mk op [off % 65536, off / 65536, 0, 0] else none
  | .store op _ off => if isStoreOp op ∧ off < 2 ^ 32 then mk op [off % 65536, off / 65536, 0, 0] else none
  | .call fi => match cinfo fi with
    | some entry => mk opCall [entry, 0, 0, 0]
    | none => none
  | i => match kindOf ls i with
    | some .next => mk Chips.Ctrl.opNext [0, 0, 0, 0]
    | some (.jump t) => mk Chips.Ctrl.opJump [t + off, 0, 0, 0]
    | some (.jumpIf t) => mk Chips.Ctrl.opJif [t + off, 0, 0, 0]
    | some .halt => mk Chips.Ctrl.opHalt [0, 0, 0, 0]
    | some .haltIf => mk Chips.Ctrl.opHif [0, 0, 0, 0]
    | _ => none

/-- D1/D5 basic shape (decidable): at most 8 params and 64 locals (params included), numeric types,
local indices in range, the stack charge and prologue gas of a call representable. -/
def basicOk (cfg : NearCfg) (pf : PFunc) : Bool :=
  decide (pf.type.params.size ≤ 8) && decide (pf.type.params.size + pf.locals.size ≤ 64) &&
  decide (pf.type.results.size ≤ 1) &&
  pf.type.results.all (fun t => t == .i32 || t == .i64) &&
  pf.locals.all (fun t => t == .i32 || t == .i64) &&
  pf.code.all (fun i => match i with
    | .localGet x | .localSet x | .localTee x => decide (x < pf.type.params.size + pf.locals.size)
    | _ => true) &&
  decide (pf.code.size < 2 ^ 20) && decide (pf.gas.size = pf.code.size) &&
  pf.type.params.all (fun t => t == .i32 || t == .i64) &&
  decide (pf.stackCharge < 2 ^ 26) && decide (cfg.regularOpCost ≠ 0) &&
  decide (pf.prologueGas % cfg.regularOpCost = 0) && decide (pf.prologueGas / cfg.regularOpCost < 2 ^ 16)

/-- Static structure: sizes, entry, every local transition, height bound. -/
def structOk (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAt p pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

def recordAt (cfg : NearCfg) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (off : Nat)
    (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee => recordOf off cinfo (L[pc]?.getD []) (H[pc]?.getD 0) fee (off + pc) ins
  | _, _ => none

/-- Type tag of a value type (1 = i64). -/
def vtTag (t : VT) : Nat := if t == .i64 then 1 else 0

/-- The eligibility check of defined function `fn` (domain D1–D5), its code placed at global pc
`off`. -/
def check (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyze p pf with
      | none => none
      | some (L, H) =>
        if structOk p pf L H then
          match (List.range pf.code.size).mapM (recordAt cfg pf L H off cinfo) with
          | none => none
          | some recs =>
            some { fn, labels := L, heights := H, arity := pf.type.results.size,
                   localTags := (pf.type.params.toList ++ pf.locals.toList).map vtTag,
                   np := pf.type.params.size, nl := pf.type.params.size + pf.locals.size,
                   charge := pf.stackCharge, prologue := pf.prologueGas / cfg.regularOpCost,
                   resTag := if pf.type.results[0]? == some .i64 then 1 else 0,
                   records := recs.toArray,
                   maxFee := (recs.map fun r => r.getD 3 0).foldl max 0 }
        else none
    else none

/-! ## Module level: the checked functions, global pcs, global code records

The code of the checked functions is concatenated: function `k` (defined-function index
`fns[k]`) occupies global pcs `[offs[k], offs[k] + size_k)`.  Records are keyed by global pc and
branch targets in them are global; the checker's labels stay local (as the spec's).  Every fact the
proof uses about the layout is re-verified by a decidable check (`layoutOk`), not proven about the
construction. -/

/-- Defined-function call targets of a function's code. -/
def calleesOf (p : Prepared) (pf : PFunc) : List Nat :=
  pf.code.toList.filterMap fun i => match i with
    | .call fi => if p.m.imports.size ≤ fi then some (fi - p.m.imports.size) else none
    | _ => none

/-- The entry function and every function reachable from it by `call` (breadth first). -/
def closureFns (p : Prepared) (entry : Nat) : List Nat := Id.run do
  let mut fns : List Nat := [entry]
  let mut todo : List Nat := [entry]
  for _ in [0:p.funcs.size + 1] do
    match todo with
    | [] => break
    | fn :: rest =>
      todo := rest
      for c in (p.funcs[fn]?.map (calleesOf p)).getD [] do
        if !(fns.contains c) then
          fns := fns ++ [c]
          todo := todo ++ [c]
  return fns

/-- Prefix sums: the code offsets of the functions. -/
def prefixOffs : List Nat → Nat → List Nat
  | [], _ => []
  | n :: ns, o => o :: prefixOffs ns (o + n)

/-- The function containing global pc `j` and the local pc. -/
def locate (offs sizes : List Nat) (j : Nat) : Nat × Nat :=
  let k := ((List.range offs.length).find? fun k => offs.getD k 0 ≤ j && j < offs.getD k 0 + sizes.getD k 0).getD 0
  (k, j - offs.getD k 0)

structure ModOut where
  /-- checked defined-function indices; `fns[0]` is the entry function -/
  fns : List Nat
  cks : List CheckOut
  offs : List Nat
  sizes : List Nat
  codeSize : Nat
  /-- global code records -/
  records : Array (List Nat)
  maxFee : Nat
  /-- the function table (bus FUNC): per checked function `[entry, np + 128 nl, charge, prologue, m0, m1, m2, m3]`
  (`m` = the locals' type mask, bit `j` = local `j` is i64, as four 16-bit limbs) -/
  funcs : List (List Nat)
  deriving Inhabited

/-- The decidable layout facts the proof uses. -/
def layoutOk (fns : List Nat) (offs sizes : List Nat) (total : Nat) : Bool :=
  decide (offs.length = fns.length) && decide (sizes.length = fns.length) &&
  (List.range total).all (fun j =>
    let kl := locate offs sizes j
    decide (kl.1 < fns.length) && decide (kl.2 < sizes.getD kl.1 0) && decide (offs.getD kl.1 0 + kl.2 = j)) &&
  (List.range fns.length).all (fun k =>
    decide (offs.getD k 0 + sizes.getD k 0 ≤ total) &&
    (List.range (sizes.getD k 0)).all fun l => decide (locate offs sizes (offs.getD k 0 + l) = (k, l)))

/-- Type mask of a list of local tags: bit `j` set iff local `j` is i64. -/
def maskOf (tags : List Nat) : Nat := ((List.range 64).map fun i => 2 ^ i * tags.getD i 0).foldl (· + ·) 0

/-- The function-table row of a checked function placed at `off`. -/
def funcRow (off : Nat) (ck : CheckOut) : List Nat :=
  [off, ck.np + 128 * ck.nl, ck.charge, ck.prologue] ++ limbs4 (maskOf ck.localTags)

/-- Call-target info for the records: the global entry pc of a checked function. -/
def callInfo (p : Prepared) (fns : List Nat) (offs : List Nat) (fi : Nat) : Option Nat :=
  if p.m.imports.size ≤ fi then (fns.idxOf? (fi - p.m.imports.size)).map fun k => offs.getD k 0 else none

/-- Module-level eligibility check from entry function `entry`. -/
def checkModule (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOut :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => check cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 then
      some { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
             maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
             funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) }
    else none

end WasmBase
