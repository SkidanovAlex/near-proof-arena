import WasmBase.Air
/-!
# WasmBase.Chips — the AIR set `wasm-base-v2` (instruction family F1)

Thirteen AIRs (≤ 32), max degree 8, no preprocessed or cached traces.  Buses:

| bus | name | message | role |
|---|---|---|---|
| 0 | STATE | `[pc, ts, S, halted]` | execution-state chain: each instruction row receives once, sends once |
| 1 | FETCH | `[pc, op, h, fee, x0, x1, x2, x3]` | code records; queried by instruction rows, answered by the cached CODE table |
| 2 | CH | `[space, slot, tag, v0, v1, v2, v3, tp]` | value channel: operand stack (space 0) and locals (space 1); producer → consumer (P-PERF-5) |
| 3 | R16 | `[v]` | 16-bit range lookups into RANGE16 |
| 4 | BYTE | `[kind, x, y, z]` | byte-pair range (kind 0) / and (1) / or (2) / xor (3) into BYTE |

Values are 4 limbs of 16 bits (i32: limbs 2, 3 are 0); `tag` = 1 for i64.  `S` is the number of
gas units (`regular_op_cost`) charged so far; `h` is the static operand-stack height at `pc` (from
the code record); `ts` is the row clock.  A consumer of a stack value receives `(slot, tag, v, tp)`
and range-checks `ts - tp - 1 = lo + 2^16 hi` with `lo, 4·hi < 2^16`.
-/
namespace WasmBase
namespace Chips
open Expr

def v (i : Nat) : Expr := .col i
def nv (i : Nat) : Expr := .nxt i
def pv (i : Nat) : Expr := .pub i

def busState : Nat := 0
def busFetch : Nat := 1
def busStk : Nat := 2
def busR16 : Nat := 3
def busByte : Nat := 4

def B16 : Expr := 65536
def bool (x : Expr) : Expr := x * (x - 1)

def stateIn (pc ts s : Expr) (cnt : Expr) : Inter := ⟨busState, false, cnt, [pc, ts, s, 0]⟩
def stateOut (pc ts s halted : Expr) (cnt : Expr) : Inter := ⟨busState, true, cnt, [pc, ts, s, halted]⟩
def fetch (pc op h fee : Expr) (xs : List Expr) (cnt : Expr) : Inter :=
  ⟨busFetch, true, cnt, [pc, op, h, fee] ++ xs⟩
/-- Space 0 = operand stack, space 1 = locals. -/
def chRecv (space slot tag : Expr) (val : List Expr) (tp cnt : Expr) : Inter :=
  ⟨busStk, false, cnt, [space, slot, tag] ++ val ++ [tp]⟩
def chSend (space slot tag : Expr) (val : List Expr) (ts cnt : Expr) : Inter :=
  ⟨busStk, true, cnt, [space, slot, tag] ++ val ++ [ts]⟩
def stkRecv (slot tag : Expr) (val : List Expr) (tp cnt : Expr) : Inter := chRecv 0 slot tag val tp cnt
def stkSend (slot tag : Expr) (val : List Expr) (ts cnt : Expr) : Inter := chSend 0 slot tag val ts cnt
def r16 (e cnt : Expr) : Inter := ⟨busR16, true, cnt, [e]⟩
def byteQ (kind x y z cnt : Expr) : Inter := ⟨busByte, true, cnt, [kind, x, y, z]⟩
/-- `tp < ts`: `ts - tp - 1 = lo + 2^16·hi`, `lo < 2^16`, `4·hi < 2^16`. -/
def timeChk (ts tp hi cnt : Expr) : List Inter :=
  [r16 (ts - tp - 1 - B16 * hi) cnt, r16 (4 * hi) cnt]

/-- Header columns shared by every instruction chip. -/
def cPc : Nat := 0
def cTs : Nat := 1
def cS : Nat := 2
def cH : Nat := 3
def cFee : Nat := 4
def headerCols : List String := ["pc", "ts", "S", "h", "fee"]

/-- Standard state transition `pc → pc+1` plus fetch. -/
def stdState (op : Expr) (xs : List Expr) (act : Expr) : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) act,
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) 0 act,
   fetch (v cPc) op (v cH) (v cFee) xs act]

def zeros4 : List Expr := [0, 0, 0, 0]
def limbsOf (base : Nat) : List Expr := (List.range 4).map fun i => v (base + i)
/-- 16-bit limb `i` from byte columns `base..base+7`. -/
def limbB (base i : Nat) : Expr := v (base + 2 * i) + 256 * v (base + 2 * i + 1)
def limbsB (base : Nat) : List Expr := (List.range 4).map (limbB base)

/-! ## ADD: i32/i64 add, sub -/
namespace Add
def fAdd : Nat := 5
def fSub : Nat := 6
def is64 : Nat := 7
def a : Nat := 8     -- a[4] 8..11
def ta : Nat := 12
def ha : Nat := 13
def b : Nat := 14    -- b[4] 14..17
def tb : Nat := 18
def hb : Nat := 19
def r : Nat := 20    -- r[4] 20..23
def cy : Nat := 24   -- carries 24..27
def cols : List String := headerCols ++ ["f_add", "f_sub", "is64", "a0", "a1", "a2", "a3", "ta", "ha",
  "b0", "b1", "b2", "b3", "tb", "hb", "r0", "r1", "r2", "r3", "c0", "c1", "c2", "c3"]
def act : Expr := v fAdd + v fSub
def op : Expr := 0x6A + 18 * v is64 + v fSub
/-- add: `a + b = r (+ carry)`, sub: `r + b = a (+ borrow)`; `X + b + c_in = Z + 2^16 c_out`. -/
def X (i : Nat) : Expr := v fAdd * v (a + i) + v fSub * v (r + i)
def Z (i : Nat) : Expr := v fAdd * v (r + i) + v fSub * v (a + i)
def constraints : List Expr :=
  [bool (v fAdd), bool (v fSub), bool (v is64), v fAdd * v fSub,
   (1 - v is64) * v (a + 2), (1 - v is64) * v (a + 3),
   (1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3),
   (1 - v is64) * v (r + 2), (1 - v is64) * v (r + 3),
   bool (v cy), bool (v (cy + 1)), bool (v (cy + 2)), bool (v (cy + 3)),
   (1 - v is64) * v (cy + 2), (1 - v is64) * v (cy + 3),
   X 0 + v (b + 0) - Z 0 - B16 * v cy,
   X 1 + v (b + 1) + v cy - Z 1 - B16 * v (cy + 1),
   v is64 * (X 2 + v (b + 2) + v (cy + 1) - Z 2 - B16 * v (cy + 2)),
   v is64 * (X 3 + v (b + 3) + v (cy + 2) - Z 3 - B16 * v (cy + 3))]
def inters : List Inter :=
  stdState op zeros4 act ++
  [stkRecv (v cH - 2) (v is64) (limbsOf a) (v ta) act,
   stkRecv (v cH - 1) (v is64) (limbsOf b) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v cH - 2) (v is64) (limbsOf r) (v cTs) act] ++
  (List.range 4).map (fun i => r16 (v (r + i)) act)
def table : Table := ⟨"ADD", cols, constraints, inters⟩
end Add

/-! ## BIT: i32/i64 and, or, xor (byte lookups) -/
namespace Bit
def fAnd : Nat := 5
def fOr : Nat := 6
def fXor : Nat := 7
def is64 : Nat := 8
def ab : Nat := 9    -- 9..16
def ta : Nat := 17
def ha : Nat := 18
def bb : Nat := 19   -- 19..26
def tb : Nat := 27
def hb : Nat := 28
def rb : Nat := 29   -- 29..36
def byteNames (p : String) : List String := (List.range 8).map fun i => p ++ toString i
def cols : List String := headerCols ++ ["f_and", "f_or", "f_xor", "is64"] ++ byteNames "ab" ++
  ["ta", "ha"] ++ byteNames "bb" ++ ["tb", "hb"] ++ byteNames "rb"
def act : Expr := v fAnd + v fOr + v fXor
def op : Expr := 0x71 + 18 * v is64 + v fOr + 2 * v fXor
def kind : Expr := v fAnd + 2 * v fOr + 3 * v fXor
def constraints : List Expr :=
  [bool (v fAnd), bool (v fOr), bool (v fXor), bool (v is64),
   v fAnd * v fOr, v fAnd * v fXor, v fOr * v fXor] ++
  ((List.range 4).flatMap fun k =>
    [(1 - v is64) * v (ab + 4 + k), (1 - v is64) * v (bb + 4 + k), (1 - v is64) * v (rb + 4 + k)])
def inters : List Inter :=
  stdState op zeros4 act ++
  [stkRecv (v cH - 2) (v is64) (limbsB ab) (v ta) act,
   stkRecv (v cH - 1) (v is64) (limbsB bb) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v cH - 2) (v is64) (limbsB rb) (v cTs) act] ++
  (List.range 8).map (fun k => byteQ kind (v (ab + k)) (v (bb + k)) (v (rb + k)) act)
def table : Table := ⟨"BIT", cols, constraints, inters⟩
end Bit

/-! ## MUL: i32/i64 mul (byte limbs, carries range-checked) -/
namespace Mul
def act : Nat := 5
def is64 : Nat := 6
def ab : Nat := 7    -- 7..14
def ta : Nat := 15
def ha : Nat := 16
def bb : Nat := 17   -- 17..24
def tb : Nat := 25
def hb : Nat := 26
def rb : Nat := 27   -- 27..34
def cy : Nat := 35   -- 35..42
def cols : List String := headerCols ++ ["act", "is64"] ++ Bit.byteNames "ab" ++ ["ta", "ha"] ++
  Bit.byteNames "bb" ++ ["tb", "hb"] ++ Bit.byteNames "rb" ++ Bit.byteNames "cy"
def op : Expr := 0x6C + 18 * v is64
/-- Column convolution `Σ_{i+j=k} a_i b_j`. -/
def conv (k : Nat) : Expr :=
  ((List.range (k + 1)).map fun i => v (ab + i) * v (bb + (k - i))).foldl (· + ·) 0
def carryIn (k : Nat) : Expr := if k = 0 then 0 else v (cy + k - 1)
def limbEq (k : Nat) : Expr := conv k + carryIn k - v (rb + k) - 256 * v (cy + k)
def constraints : List Expr :=
  [bool (v act), bool (v is64)] ++
  ((List.range 4).flatMap fun k =>
    [(1 - v is64) * v (ab + 4 + k), (1 - v is64) * v (bb + 4 + k), (1 - v is64) * v (rb + 4 + k),
     (1 - v is64) * v (cy + 4 + k)]) ++
  (List.range 4).map limbEq ++
  (List.range 4).map (fun k => v is64 * limbEq (k + 4))
def inters : List Inter :=
  stdState op zeros4 (v act) ++
  [stkRecv (v cH - 2) (v is64) (limbsB ab) (v ta) (v act),
   stkRecv (v cH - 1) (v is64) (limbsB bb) (v tb) (v act)] ++
  timeChk (v cTs) (v ta) (v ha) (v act) ++ timeChk (v cTs) (v tb) (v hb) (v act) ++
  [stkSend (v cH - 2) (v is64) (limbsB rb) (v cTs) (v act)] ++
  (List.range 4).map (fun i => byteQ 0 (v (ab + 2 * i)) (v (ab + 2 * i + 1)) 0 (v act)) ++
  (List.range 4).map (fun i => byteQ 0 (v (bb + 2 * i)) (v (bb + 2 * i + 1)) 0 (v act)) ++
  (List.range 4).map (fun i => byteQ 0 (v (rb + 2 * i)) (v (rb + 2 * i + 1)) 0 (v act)) ++
  (List.range 8).map (fun k => r16 (v (cy + k)) (v act))
def table : Table := ⟨"MUL", cols, constraints, inters⟩
end Mul

/-! ## SHIFT: i32/i64 shl, shr_s, shr_u, rotl, rotr

`k = b mod w` (bits `kb`, `b0 = k + w·q`); `e = k` (shl, rotl) or `w - k` (shr, rotr), `e = 8·t + eb`
with `t` one-hot (`el`) and `pow = 2^eb`.  `A` = `a` extended to `2w` bits (sign-filled for shr_s),
`P = A·2^e mod 2^(2w)` byte by byte with carries; the result is the low half (shl), the high half
(shr_s, shr_u) or their sum (rotl, rotr). -/
namespace Shift
def fShl : Nat := 5
def fShrS : Nat := 6
def fShrU : Nat := 7
def fRotl : Nat := 8
def fRotr : Nat := 9
def is64 : Nat := 10
def ab : Nat := 11   -- 11..18
def ta : Nat := 19
def ha : Nat := 20
def b : Nat := 21    -- 21..24 (16-bit limbs of the count)
def tb : Nat := 25
def hb : Nat := 26
def kb : Nat := 27   -- 27..32
def q : Nat := 33
def eb : Nat := 34   -- 34..36
def el : Nat := 37   -- 37..45
def sgn : Nat := 46
def rest : Nat := 47
def P : Nat := 48    -- 48..63
def cy : Nat := 64   -- 64..79
def cols : List String := headerCols ++ ["f_shl", "f_shrs", "f_shru", "f_rotl", "f_rotr", "is64"] ++
  Bit.byteNames "ab" ++ ["ta", "ha", "b0", "b1", "b2", "b3", "tb", "hb"] ++
  ((List.range 6).map fun i => s!"kb{i}") ++ ["q"] ++ ((List.range 3).map fun i => s!"eb{i}") ++
  ((List.range 9).map fun i => s!"el{i}") ++ ["sgn", "rest"] ++
  ((List.range 16).map fun i => s!"P{i}") ++ ((List.range 16).map fun i => s!"cy{i}")
def left : Expr := v fShl + v fRotl
def right : Expr := v fShrS + v fShrU + v fRotr
def act : Expr := left + right
def op : Expr := 0x74 + 18 * v is64 + v fShrS + 2 * v fShrU + 3 * v fRotl + 4 * v fRotr
def w : Expr := 32 + 32 * v is64
def kval : Expr := ((List.range 6).map fun j => Expr.c (2 ^ j) * v (kb + j)).foldl (· + ·) 0
def eval' : Expr := left * kval + right * (w - kval)
def tval : Expr := ((List.range 9).map fun t => Expr.c t * v (el + t)).foldl (· + ·) 0
def ebval : Expr := v eb + 2 * v (eb + 1) + 4 * v (eb + 2)
def pow : Expr := (1 + v eb) * (1 + 3 * v (eb + 1)) * (1 + 15 * v (eb + 2))
def topByte : Expr := v is64 * v (ab + 7) + (1 - v is64) * v (ab + 3)
def fill : Expr := 255 * v sgn * v fShrS
/-- byte `i` of the `2w`-bit extension of `a`. -/
def A (i : Nat) : Expr :=
  if i < 4 then v (ab + i)
  else if i < 8 then v is64 * v (ab + i) + (1 - v is64) * fill
  else if i < 16 then v is64 * fill
  else 0
/-- `A_{j - t}` selected by the one-hot `el`. -/
def M (j : Nat) : Expr :=
  ((List.range 9).filterMap fun t => if t ≤ j then some (v (el + t) * A (j - t)) else none).foldl (· + ·) 0
def carryIn (j : Nat) : Expr := if j = 0 then 0 else v (cy + j - 1)
def limbEq (j : Nat) : Expr := pow * M j + carryIn j - v (P + j) - 256 * v (cy + j)
def flo : Expr := v fShl + v fRotl + v fRotr
def fhi : Expr := v fShrS + v fShrU + v fRotl + v fRotr
/-- result byte `j` (0..7). -/
def rbyte (j : Nat) : Expr :=
  if j < 4 then flo * v (P + j) + fhi * (v is64 * v (P + j + 8) + (1 - v is64) * v (P + j + 4))
  else v is64 * (flo * v (P + j) + fhi * v (P + j + 8))
def rlimb (i : Nat) : Expr := rbyte (2 * i) + 256 * rbyte (2 * i + 1)
def constraints : List Expr :=
  [bool (v fShl), bool (v fShrS), bool (v fShrU), bool (v fRotl), bool (v fRotr), bool (v is64),
   bool act] ++
  ((List.range 6).map fun j => bool (v (kb + j))) ++
  [(1 - v is64) * v (kb + 5),
   v b - kval - w * v q] ++
  ((List.range 3).map fun j => bool (v (eb + j))) ++
  ((List.range 9).map fun t => bool (v (el + t))) ++
  [((List.range 9).map fun t => v (el + t)).foldl (· + ·) 0 - act,
   eval' - ebval - 8 * tval,
   bool (v sgn),
   topByte - 128 * v sgn - v rest] ++
  ((List.range 4).map fun k => (1 - v is64) * v (ab + 4 + k)) ++
  [(1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3)] ++
  ((List.range 8).flatMap fun k => [(1 - v is64) * v (P + 8 + k), (1 - v is64) * v (cy + 8 + k)]) ++
  (List.range 8).map limbEq ++
  (List.range 8).map (fun j => v is64 * limbEq (j + 8))
def inters : List Inter :=
  stdState op zeros4 act ++
  [stkRecv (v cH - 2) (v is64) (limbsB ab) (v ta) act,
   stkRecv (v cH - 1) (v is64) (limbsOf b) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v cH - 2) (v is64) ((List.range 4).map rlimb) (v cTs) act,
   -- `q < 2^16` itself (v1 range-checked `w·q`, which is unsound: `q` is free, so `w·q` can be any
   -- small residue and the shift count `k` was unconstrained; found by the Lean proof)
   r16 (v q) act,
   byteQ 0 (2 * v rest) 0 0 act] ++
  (List.range 4).map (fun i => byteQ 0 (v (ab + 2 * i)) (v (ab + 2 * i + 1)) 0 act) ++
  (List.range 8).map (fun i => byteQ 0 (v (P + 2 * i)) (v (P + 2 * i + 1)) 0 act) ++
  (List.range 8).map (fun i => byteQ 0 (v (cy + 2 * i)) (v (cy + 2 * i + 1)) 0 act)
def table : Table := ⟨"SHIFT", cols, constraints, inters⟩
end Shift


/-! ## CMP: i32/i64 eqz, eq, ne, lt/gt/le/ge _s/_u -/
namespace Cmp
def fEqz : Nat := 5
def fEq : Nat := 6
def fNe : Nat := 7
def fLtS : Nat := 8
def fLtU : Nat := 9
def fGtS : Nat := 10
def fGtU : Nat := 11
def fLeS : Nat := 12
def fLeU : Nat := 13
def fGeS : Nat := 14
def fGeU : Nat := 15
def is64 : Nat := 16
def a : Nat := 17    -- 17..20
def ta : Nat := 21
def ha : Nat := 22
def b : Nat := 23    -- 23..26
def tb : Nat := 27
def hb : Nat := 28
def sa : Nat := 29
def ra : Nat := 30
def sb : Nat := 31
def rb : Nat := 32
def d : Nat := 33    -- 33..36
def br : Nat := 37   -- 37..40
def inv : Nat := 41
def cols : List String := headerCols ++ ["f_eqz", "f_eq", "f_ne", "f_lts", "f_ltu", "f_gts", "f_gtu",
  "f_les", "f_leu", "f_ges", "f_geu", "is64", "a0", "a1", "a2", "a3", "ta", "ha",
  "b0", "b1", "b2", "b3", "tb", "hb", "sa", "ra", "sb", "rb", "d0", "d1", "d2", "d3",
  "br0", "br1", "br2", "br3", "inv"]
def flags : List Nat := [fEqz, fEq, fNe, fLtS, fLtU, fGtS, fGtU, fLeS, fLeU, fGeS, fGeU]
def act : Expr := (flags.map v).foldl (· + ·) 0
def op : Expr := 0x45 + 11 * v is64 +
  ((flags.zipIdx).map fun (f, i) => Expr.c i * v f).foldl (· + ·) 0
def swap : Expr := v fGtS + v fGtU + v fLeS + v fLeU
def signed : Expr := v fLtS + v fGtS + v fLeS + v fGeS
def X (i : Nat) : Expr := v (a + i) + swap * (v (b + i) - v (a + i))
def Y (i : Nat) : Expr := v (b + i) + swap * (v (a + i) - v (b + i))
def sX : Expr := v sa + swap * (v sb - v sa)
def sY : Expr := v sb + swap * (v sa - v sb)
def topInd (i : Nat) : Expr := if i = 1 then 1 - v is64 else if i = 3 then v is64 else 0
def flipX (i : Nat) : Expr := signed * (32768 - B16 * sX) * topInd i
def flipY (i : Nat) : Expr := signed * (32768 - B16 * sY) * topInd i
def brIn (i : Nat) : Expr := if i = 0 then 0 else v (br + i - 1)
def limbEq (i : Nat) : Expr :=
  X i + flipX i - (Y i + flipY i) - brIn i - v (d + i) + B16 * v (br + i)
def lt : Expr := (1 - v is64) * v (br + 1) + v is64 * v (br + 3)
def zsum : Expr := v d + v (d + 1) + v (d + 2) + v (d + 3)
def eqf : Expr := 1 - zsum * v inv
def res : Expr := (v fEqz + v fEq) * eqf + v fNe * (1 - eqf) +
  (v fLtS + v fLtU + v fGtS + v fGtU) * lt + (v fLeS + v fLeU + v fGeS + v fGeU) * (1 - lt)
def topA : Expr := v is64 * v (a + 3) + (1 - v is64) * v (a + 1)
def topB : Expr := v is64 * v (b + 3) + (1 - v is64) * v (b + 1)
def slotA : Expr := v cH - 2 + v fEqz
def constraints : List Expr :=
  (flags.map fun f => bool (v f)) ++ [bool act, bool (v is64)] ++
  ((List.range 4).map fun i => v fEqz * v (b + i)) ++
  [(1 - v is64) * v (a + 2), (1 - v is64) * v (a + 3),
   (1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3),
   bool (v sa), bool (v sb), topA - 32768 * v sa - v ra, topB - 32768 * v sb - v rb] ++
  ((List.range 4).map fun i => bool (v (br + i))) ++
  [(1 - v is64) * v (d + 2), (1 - v is64) * v (d + 3),
   (1 - v is64) * v (br + 2), (1 - v is64) * v (br + 3),
   limbEq 0, limbEq 1, v is64 * limbEq 2, v is64 * limbEq 3,
   zsum * eqf]
def inters : List Inter :=
  stdState op zeros4 act ++
  [stkRecv slotA (v is64) (limbsOf a) (v ta) act,
   stkRecv (v cH - 1) (v is64) (limbsOf b) (v tb) (act - v fEqz)] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) (act - v fEqz) ++
  [stkSend slotA 0 [res, 0, 0, 0] (v cTs) act] ++
  ((List.range 4).map fun i => r16 (v (d + i)) act) ++
  [r16 (2 * v ra) act, r16 (2 * v rb) act]
def table : Table := ⟨"CMP", cols, constraints, inters⟩
end Cmp

/-! ## CONST: i32.const, i64.const (immediate from the code record) -/
namespace Const
def act : Nat := 5
def is64 : Nat := 6
def imm : Nat := 7   -- 7..10
def cols : List String := headerCols ++ ["act", "is64", "imm0", "imm1", "imm2", "imm3"]
def op : Expr := 0x41 + v is64
def constraints : List Expr :=
  [bool (v act), bool (v is64), (1 - v is64) * v (imm + 2), (1 - v is64) * v (imm + 3)]
def inters : List Inter :=
  stdState op (limbsOf imm) (v act) ++ [stkSend (v cH) (v is64) (limbsOf imm) (v cTs) (v act)]
def table : Table := ⟨"CONST", cols, constraints, inters⟩
end Const

/-! ## STACK: drop, select -/
namespace Stack
def fDrop : Nat := 5
def fSel : Nat := 6
def tagA : Nat := 7
def A : Nat := 8     -- 8..11 (dropped value, or the select condition)
def tA : Nat := 12
def hA : Nat := 13
def tagV : Nat := 14
def V2 : Nat := 15   -- 15..18
def t2 : Nat := 19
def h2 : Nat := 20
def V1 : Nat := 21   -- 21..24
def t1 : Nat := 25
def h1 : Nat := 26
def inv : Nat := 27
def cols : List String := headerCols ++ ["f_drop", "f_sel", "tagA", "A0", "A1", "A2", "A3", "tA", "hA",
  "tagV", "V2_0", "V2_1", "V2_2", "V2_3", "t2", "h2", "V1_0", "V1_1", "V1_2", "V1_3", "t1", "h1", "inv"]
def act : Expr := v fDrop + v fSel
def op : Expr := 0x1A * v fDrop + 0x1B * v fSel
def cz : Expr := v A + v (A + 1)
def nz : Expr := cz * v inv
def out (i : Nat) : Expr := nz * v (V1 + i) + (1 - nz) * v (V2 + i)
def constraints : List Expr :=
  [bool (v fDrop), bool (v fSel), v fDrop * v fSel, bool (v tagA), bool (v tagV),
   v fSel * v tagA,
   (1 - v tagA) * v (A + 2), (1 - v tagA) * v (A + 3),
   (1 - v tagV) * v (V2 + 2), (1 - v tagV) * v (V2 + 3),
   (1 - v tagV) * v (V1 + 2), (1 - v tagV) * v (V1 + 3),
   cz * (1 - nz)]
def inters : List Inter :=
  stdState op zeros4 act ++
  [stkRecv (v cH - 1) (v tagA) (limbsOf A) (v tA) act] ++ timeChk (v cTs) (v tA) (v hA) act ++
  [stkRecv (v cH - 2) (v tagV) (limbsOf V2) (v t2) (v fSel),
   stkRecv (v cH - 3) (v tagV) (limbsOf V1) (v t1) (v fSel)] ++
  timeChk (v cTs) (v t2) (v h2) (v fSel) ++ timeChk (v cTs) (v t1) (v h1) (v fSel) ++
  [stkSend (v cH - 3) (v tagV) ((List.range 4).map out) (v cTs) (v fSel)]
def table : Table := ⟨"STACK", cols, constraints, inters⟩
end Stack

/-! ## CTRL: block / loop / nested end (NEXT), br (JUMP), br_if (JUMPIF), end-of-function /
return / br to the function label (HALT), br_if to the function label (HALTIF).  Labels and target
pcs are static (code record field `x0`); under the no-discard domain condition branches do not
touch the operand stack. -/
namespace Ctrl
def fNext : Nat := 5
def fJump : Nat := 6
def fJif : Nat := 7
def fHalt : Nat := 8
def fHif : Nat := 9
def tgt : Nat := 10
def c : Nat := 11    -- 11, 12
def tc : Nat := 13
def hc : Nat := 14
def inv : Nat := 15
def cols : List String := headerCols ++ ["f_next", "f_jump", "f_jif", "f_halt", "f_hif", "tgt",
  "c0", "c1", "tc", "hc", "inv"]
def opNext : Nat := 0x101
def opJump : Nat := 0x102
def opJif : Nat := 0x103
def opHalt : Nat := 0x104
def opHif : Nat := 0x105
def act : Expr := v fNext + v fJump + v fJif + v fHalt + v fHif
def cnd : Expr := v fJif + v fHif
def op : Expr := Expr.c opNext * v fNext + Expr.c opJump * v fJump + Expr.c opJif * v fJif +
  Expr.c opHalt * v fHalt + Expr.c opHif * v fHif
def nz : Expr := (v c + v (c + 1)) * v inv
def pc1 : Expr := v cPc + 1
def pcNext : Expr := v fNext * pc1 + v fJump * v tgt + v fJif * (nz * v tgt + (1 - nz) * pc1) +
  v fHalt * v cPc + v fHif * (nz * v cPc + (1 - nz) * pc1)
def halted : Expr := v fHalt + v fHif * nz
def constraints : List Expr :=
  [bool (v fNext), bool (v fJump), bool (v fJif), bool (v fHalt), bool (v fHif), bool act,
   (v c + v (c + 1)) * (1 - nz)]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) act,
   stateOut pcNext (v cTs + 1) (v cS + v cFee) halted act,
   fetch (v cPc) op (v cH) (v cFee) [v tgt, 0, 0, 0] act,
   stkRecv (v cH - 1) 0 [v c, v (c + 1), 0, 0] (v tc) cnd] ++
  timeChk (v cTs) (v tc) (v hc) cnd
def table : Table := ⟨"CTRL", cols, constraints, inters⟩
end Ctrl

/-! ## LOCAL: local.get, local.set, local.tee (locals are channel space 1: every access consumes
the current record and produces a fresh one) -/
namespace Local
def fGet : Nat := 5
def fSet : Nat := 6
def fTee : Nat := 7
def idx : Nat := 8
def tagL : Nat := 9
def L : Nat := 10    -- 10..13 (old local value)
def tL : Nat := 14
def hL : Nat := 15
def tagV : Nat := 16
def V : Nat := 17    -- 17..20 (stack value, set/tee)
def tV : Nat := 21
def hV : Nat := 22
def cols : List String := headerCols ++ ["f_get", "f_set", "f_tee", "idx", "tagL", "L0", "L1", "L2", "L3",
  "tL", "hL", "tagV", "V0", "V1", "V2", "V3", "tV", "hV"]
def act : Expr := v fGet + v fSet + v fTee
def wr : Expr := v fSet + v fTee
def op : Expr := 0x20 + v fSet + 2 * v fTee
def newTag : Expr := v fGet * v tagL + wr * v tagV
def newVal (i : Nat) : Expr := v fGet * v (L + i) + wr * v (V + i)
def constraints : List Expr :=
  [bool (v fGet), bool (v fSet), bool (v fTee), bool act, bool (v tagL), bool (v tagV),
   (1 - v tagL) * v (L + 2), (1 - v tagL) * v (L + 3),
   (1 - v tagV) * v (V + 2), (1 - v tagV) * v (V + 3)]
def inters : List Inter :=
  stdState op [v idx, 0, 0, 0] act ++
  [chRecv 1 (v idx) (v tagL) (limbsOf L) (v tL) act] ++ timeChk (v cTs) (v tL) (v hL) act ++
  [chSend 1 (v idx) newTag ((List.range 4).map newVal) (v cTs) act,
   stkRecv (v cH - 1) (v tagV) (limbsOf V) (v tV) wr] ++ timeChk (v cTs) (v tV) (v hV) wr ++
  [stkSend (v cH - 1 + v fGet) newTag ((List.range 4).map newVal) (v cTs) (v fGet + v fTee)]
def table : Table := ⟨"LOCAL", cols, constraints, inters⟩
end Local

/-! ## BOUNDARY (height 4): initial / final state, final stack value, initial / final locals. -/
namespace Boundary
def pcf : Nat := 0
def tpr : Nat := 1
/-- per local `j`: final tag, value limbs, producer time (6 columns from `2 + 6 j`) -/
def fin (j : Nat) : Nat := 2 + 6 * j
/-- Public values: `[N, S_final, nres, rtag, r0, r1, r2, r3]`, then one tag per local.  The code is
not public: it is the cached CODE table, whose commitment is a statement component (`code_root`).
The first instruction row has `ts = 1`; initial locals are produced at time 0. -/
def pubN : Nat := 0
def pubS : Nat := 1
def pubNres : Nat := 2
def pubTag : Nat := 3
def pubR : Nat := 4
def pubLoc : Nat := 8
def recWidth : Nat := 8
def cols (nloc : Nat) : List String := ["pcf", "tpr"] ++
  ((List.range nloc).flatMap fun j => [s!"ftag{j}", s!"fv{j}_0", s!"fv{j}_1", s!"fv{j}_2", s!"fv{j}_3", s!"ftp{j}"])
def inters (nloc : Nat) : List Inter :=
  [stateOut 0 1 0 0 .first,
   ⟨busState, false, .first, [v pcf, pv pubN, pv pubS, 1]⟩,
   stkRecv 0 (pv pubTag) ((List.range 4).map fun i => pv (pubR + i)) (v tpr) (.first * pv pubNres)] ++
  ((List.range nloc).flatMap fun j =>
    [chSend 1 (Expr.c j) (pv (pubLoc + j)) zeros4 0 .first,
     chRecv 1 (Expr.c j) (v (fin j)) ((List.range 4).map fun i => v (fin j + 1 + i)) (v (fin j + 5)) .first])
def table (nloc : Nat) : Table := ⟨"BOUNDARY", cols nloc, [], inters nloc⟩
end Boundary

/-! ## CODE: the code records `[pc, op, h, fee, x0..x3]` as a **cached** trace (columns 0..7; the
multiplicity column 8 is in the common main).  Its commitment `code_root` is exposed by L1 and
checked by V_d against the contract's code (`code_hash`): the canonical CODE matrix is a
deterministic function of the code (records in pc order, padded by repeating the last record). -/
namespace Code
def mult : Nat := 8
def cachedWidth : Nat := 8
def cols : List String := ["pc", "op", "h", "fee", "x0", "x1", "x2", "x3", "mult"]
def table : Table :=
  ⟨"CODE", cols, [], [⟨busFetch, false, v mult, (List.range 8).map v⟩]⟩
end Code

/-! ## RANGE16: the committed, derived table `v = row index`, height exactly `2^16`. -/
namespace Range16
def val : Nat := 0
def m : Nat := 1
def constraints : List Expr :=
  [.first * v val, .trans * (nv val - v val - 1), .last * (v val - 65535)]
def table : Table := ⟨"RANGE16", ["v", "m"], constraints, [⟨busR16, false, v m, [v val]⟩]⟩
end Range16

/-! ## BYTE: committed, derived table over all byte pairs `(x, y)` (bits), height exactly `2^16`,
answering pair-range (kind 0), and (1), or (2), xor (3). -/
namespace Byte
def xb : Nat := 0    -- 0..7
def yb : Nat := 8    -- 8..15
def m : Nat := 16    -- 16..19
def cols : List String := ((List.range 8).map fun i => s!"x{i}") ++ ((List.range 8).map fun i => s!"y{i}") ++
  ["m0", "m1", "m2", "m3"]
def bitsum (col : Nat → Expr) (base : Nat) (f : Expr → Expr → Expr) : Expr :=
  ((List.range 8).map fun i => Expr.c (2 ^ i) * f (col (base + i)) (col (base + 8 + i))).foldl (· + ·) 0
def X : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * v (xb + i)).foldl (· + ·) 0
def Y : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * v (yb + i)).foldl (· + ·) 0
def key : Expr := X + 256 * Y
def nkey : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * nv (xb + i)).foldl (· + ·) 0 +
  256 * ((List.range 8).map fun i => Expr.c (2 ^ i) * nv (yb + i)).foldl (· + ·) 0
def andE : Expr := bitsum v 0 fun x y => x * y
def orE : Expr := bitsum v 0 fun x y => x + y - x * y
def xorE : Expr := bitsum v 0 fun x y => x + y - 2 * x * y
def constraints : List Expr :=
  ((List.range 16).map fun i => bool (v i)) ++
  [.first * key, .trans * (nkey - key - 1), .last * (key - 65535)]
def inters : List Inter :=
  [⟨busByte, false, v m, [0, X, Y, 0]⟩,
   ⟨busByte, false, v (m + 1), [1, X, Y, andE]⟩,
   ⟨busByte, false, v (m + 2), [2, X, Y, orE]⟩,
   ⟨busByte, false, v (m + 3), [3, X, Y, xorE]⟩]
def table : Table := ⟨"BYTE", cols, constraints, inters⟩
end Byte

end Chips

open Chips in
/-- The AIR set `wasm-base-v2` for a function with `nloc` locals (the code size only sets the CODE
height). -/
def wasmBaseAir (nloc _ncode : Nat) : Air where
  tables := [Boundary.table nloc, Add.table, Bit.table, Mul.table, Shift.table, Cmp.table,
    Const.table, Stack.table, Ctrl.table, Local.table, Range16.table, Byte.table, Code.table]
  numPub := Boundary.pubLoc + nloc

end WasmBase
