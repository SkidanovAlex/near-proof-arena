import WasmBase.Prelude
import WasmBase.Check
import WasmBase.Mem
/-!
# WasmBase.Event — channel messages, the spec-state relation, and the gas/charge step

The value channel (bus CH) carries `Msg`s.  A spec state `s` with current frame `f` is related to a
set `live` of channel messages (`RelW`, README §10) when `live` is exactly the encoding of the whole
operand stack (space 0, slot = absolute stack index), of the current frame's locals (space
`16 + cid`, slot = local index), each with some producer time `< t`, and of an outer part `E.live`
(caller frames' locals, and later globals, memory words and call records) in other spaces.  The
frame environment `E : Env` carries the stack base, the activation id and the caller frames.
-/
namespace WasmBase
open NearSpecV3.Wasm

structure Msg where
  space : Nat
  slot : Nat
  tag : Nat
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  tp : Nat
  deriving DecidableEq, Repr

def Msg.val (m : Msg) : Nat := val4 m.l0 m.l1 m.l2 m.l3

/-- Limbs are 16-bit; i32 values have zero upper limbs; tags are 0/1. -/
def Msg.ok (m : Msg) : Prop :=
  m.l0 < 65536 ∧ m.l1 < 65536 ∧ m.l2 < 65536 ∧ m.l3 < 65536 ∧
  ((m.tag = 0 ∧ m.l2 = 0 ∧ m.l3 = 0) ∨ m.tag = 1)

def vTag : Val → Nat
  | .i64 _ => 1
  | _ => 0

def vNum : Val → Nat
  | .i32 v => v.toNat
  | .i64 v => v.toNat
  | .ref _ => 0

def isNum : Val → Prop
  | .ref _ => False
  | _ => True

/-- Encoding of a value as a channel message. -/
def enc (space slot : Nat) (v : Val) (tp : Nat) : Msg :=
  ⟨space, slot, vTag v, vNum v % 65536, vNum v / 65536 % 65536, vNum v / 2 ^ 32 % 65536,
   vNum v / 2 ^ 48 % 65536, tp⟩

/-- The decoded value of a well-formed message. -/
def Msg.toVal (m : Msg) : Val :=
  if m.tag = 1 then .i64 (UInt64.ofNat m.val) else .i32 (UInt32.ofNat m.val)

theorem vNum_lt_i32 (v : UInt32) : vNum (.i32 v) < 2 ^ 32 := v.toNat_lt
theorem vNum_lt_i64 (v : UInt64) : vNum (.i64 v) < 2 ^ 64 := v.toNat_lt

theorem enc_ok {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).ok := by
  cases v with
  | i32 x =>
    have := x.toNat_lt
    simp only [enc, Msg.ok, vTag, vNum, Nat.reducePow, true_and, or_true, and_true, Nat.reduceEqDiff, or_false] at *
    omega
  | i64 x =>
    have := x.toNat_lt
    simp only [enc, Msg.ok, vTag, vNum, Nat.reducePow, true_and, or_true, and_true, Nat.reduceEqDiff, or_false] at *
    omega
  | ref _ => exact absurd hv id

theorem enc_val {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).val = vNum v := by
  cases v with
  | i32 x =>
    have := x.toNat_lt
    simp only [enc, Msg.val, val4, vNum, Nat.reducePow] at *
    omega
  | i64 x =>
    have := x.toNat_lt
    simp only [enc, Msg.val, val4, vNum, Nat.reducePow] at *
    omega
  | ref _ => exact absurd hv id

theorem enc_toVal {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).toVal = v := by
  cases v with
  | i32 x =>
    have hv := enc_val (v := .i32 x) trivial space slot tp
    have ht : (enc space slot (.i32 x) tp).tag = 0 := rfl
    simp only [Msg.toVal, hv, ht, vNum]
    simp
  | i64 x =>
    have hv := enc_val (v := .i64 x) trivial space slot tp
    have ht : (enc space slot (.i64 x) tp).tag = 1 := rfl
    simp only [Msg.toVal, hv, ht, vNum]
    simp
  | ref _ => exact absurd hv id

/-- A message `m` equals the encoding of its decoded value when well-formed. -/
theorem enc_of_ok {m : Msg} (hm : m.ok) : enc m.space m.slot m.toVal m.tp = m := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := hm
  have hv : m.val < 2 ^ 64 := by simp only [Msg.val, val4, Nat.reducePow]; omega
  rcases ht with ⟨ht, z2, z3⟩ | ht
  · have hv32 : m.val < 2 ^ 32 := by simp only [Msg.val, val4, Nat.reducePow]; omega
    have : m.tag ≠ 1 := by omega
    simp only [enc, Msg.toVal, this, ite_false, vTag, vNum, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hv32]
    cases m; simp_all [Msg.val, val4, Nat.reducePow]; omega
  · simp only [enc, Msg.toVal, ht, ite_true, vTag, vNum, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hv]
    cases m; simp_all [Msg.val, val4, Nat.reducePow]; omega

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-! ## Views of the spec state as channel messages -/

def stackView (stk : Array Val) (tps : Nat → Nat) : List Msg :=
  (List.range stk.size).map fun i => enc 0 i (stk[i]?.getD default) (tps i)

/-- The locals of one activation, in channel space `sp` (`16 + cid`). -/
def localView (sp : Nat) (locs : Array Val) (tpl : Nat → Nat) : List Msg :=
  (List.range locs.size).map fun j => enc sp j (locs[j]?.getD default) (tpl j)

theorem mem_stackView {x : Msg} {stk : Array Val} {tps : Nat → Nat} :
    x ∈ stackView stk tps ↔ ∃ i, i < stk.size ∧ x = enc 0 i (stk[i]?.getD default) (tps i) := by
  simp only [stackView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem mem_localView {x : Msg} {sp : Nat} {locs : Array Val} {tpl : Nat → Nat} :
    x ∈ localView sp locs tpl ↔ ∃ j, j < locs.size ∧ x = enc sp j (locs[j]?.getD default) (tpl j) := by
  simp only [localView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

@[simp] theorem enc_space (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).space = a := rfl
@[simp] theorem enc_slot (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).slot = b := rfl
@[simp] theorem enc_tp (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).tp = tp := rfl
@[simp] theorem enc_tag (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).tag = vTag v := rfl

/-- Live messages after an event: consumed ones removed, produced ones added. -/
def stepLive (live : Msg → Prop) (cons prod : List Msg) : Msg → Prop :=
  fun x => (live x ∧ x ∉ cons) ∨ x ∈ prod

/-- The static context of one run: the prepared module, the entry function and its module-level
check (the checked functions, their code offsets and the global code records). -/
structure Ctx where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  M : ModOut
  g0 : Nat
  hM : checkModule cfg p fn = some M

def Ctx.R (X : Ctx) : Nat := X.cfg.regularOpCost
/-- Number of checked functions. -/
def Ctx.nf (X : Ctx) : Nat := X.M.fns.length
/-- Defined-function index of checked function `k`. -/
def Ctx.fnOf (X : Ctx) (k : Nat) : Nat := X.M.fns.getD k 0
def Ctx.pfOf (X : Ctx) (k : Nat) : PFunc := (X.p.funcs[X.fnOf k]?).getD default
def Ctx.ckOf (X : Ctx) (k : Nat) : CheckOut := X.M.cks.getD k default
/-- Global pc of local pc 0 of checked function `k`. -/
def Ctx.offOf (X : Ctx) (k : Nat) : Nat := X.M.offs.getD k 0
/-- The entry function (checked function 0). -/
def Ctx.pf (X : Ctx) : PFunc := X.pfOf 0
def Ctx.ck (X : Ctx) : CheckOut := X.ckOf 0
/-- Module-wide bound on the fee units of one instruction. -/
def Ctx.maxFee (X : Ctx) : Nat := X.M.maxFee

/-- The part of the machine a straight-line instruction does not touch: the current frame's stack
base and activation id, the caller frames, and the live channel messages of everything except the
operand stack and the current locals (callers' locals, call records, globals, memory words, dead
activations).  Families 2–4 refine `live` by their views. -/
structure Env where
  sb : Nat
  cid : Nat
  rest : List Frame
  live : Msg → Prop
  /-- the checked function (index into the module's function list) of the current frame -/
  k : Nat

/-- Channel space of the current activation's locals. -/
def Env.lsp (E : Env) : Nat := 16 + E.cid

/-- Spec label heights are absolute; the checker's are relative to the frame base. -/
def shiftLabels (sb : Nat) (ls : List Label) : List Label := ls.map fun l => { l with height := l.height + sb }

@[simp] theorem shiftLabels_zero (ls : List Label) : shiftLabels 0 ls = ls := by
  simp [shiftLabels]

/-! ## Linear memory as channel messages (space 3, one message per touched byte) -/

/-- A memory message: byte `x` at address `a`, produced at time `tp`. -/
def encB (a x tp : Nat) : Msg := ⟨3, a, 0, x, 0, 0, 0, tp⟩

/-- The touched bytes `T` of the memory of `s`, with producer times `tpm`. -/
def memView (T : List Nat) (s : St) (tpm : Nat → Nat) : List Msg :=
  T.map fun a => encB a (readByte s a).toNat (tpm a)

theorem mem_memView {x : Msg} {T : List Nat} {s : St} {tpm : Nat → Nat} :
    x ∈ memView T s tpm ↔ ∃ a ∈ T, x = encB a (readByte s a).toNat (tpm a) := by
  simp only [memView, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-- The globals as channel messages (space 2, slot = global index), producer times `tpg`. -/
def globView (gs : Array Val) (tpg : Nat → Nat) : List Msg :=
  (List.range gs.size).map fun g => enc 2 g (gs[g]?.getD default) (tpg g)

theorem mem_globView {x : Msg} {gs : Array Val} {tpg : Nat → Nat} :
    x ∈ globView gs tpg ↔ ∃ g, g < gs.size ∧ x = enc 2 g (gs[g]?.getD default) (tpg g) := by
  simp only [globView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

/-- The heap part of the outer live set: every page has `pageSize` bytes, and the space-3 messages
of `E.live` are exactly one message per touched byte `a ∈ T` (in bounds), carrying the current
byte, produced before `t`.  `T` is fixed for the whole run (the MEMINIT rows). -/
structure HeapOK (E : Env) (s : St) (t : Nat) : Prop where
  pages : PagesOK s
  mem : ∃ (T : List Nat) (tpm : Nat → Nat), T.Nodup ∧ (∀ a ∈ T, a < memBytes s) ∧ (∀ a ∈ T, tpm a < t) ∧
    ∀ x, x.space = 3 → (E.live x ↔ x ∈ memView T s tpm)
  /-- The globals (space 2): numeric, one live message each, produced before `t`. -/
  glob : ∃ (tpg : Nat → Nat), (∀ g, g < s.globals.size → tpg g < t ∧ isNum (s.globals[g]?.getD default)) ∧
    ∀ x, x.space = 2 → (E.live x ↔ x ∈ globView s.globals tpg)

theorem readByte_congr {s s' : St} (h : s'.pages = s.pages) (a : Nat) : readByte s' a = readByte s a := by
  simp only [readByte, h]

theorem memBytes_congr {s s' : St} (h : s'.pages = s.pages) : memBytes s' = memBytes s := by
  simp only [memBytes, h]

theorem HeapOK.mono {E : Env} {s s' : St} {t t' : Nat} (H : HeapOK E s t) (hpg : s'.pages = s.pages)
    (hgl : s'.globals = s.globals) (ht : t ≤ t') : HeapOK E s' t' := by
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H.mem
  obtain ⟨tpg, hg, hgv⟩ := H.glob
  refine ⟨fun i h => by have := H.pages i (by rw [← hpg]; exact h); simpa only [hpg] using this,
    ⟨T, tpm, hnd, fun a ha => by rw [memBytes_congr hpg]; exact hlt a ha, fun a ha => by have := htp a ha; omega,
    fun x hx => ?_⟩, ⟨tpg, fun g h => ?_, fun x hx => ?_⟩⟩
  · rw [hv x hx]
    simp only [memView, readByte_congr hpg]
  · rw [hgl] at h ⊢; have := hg g h; exact ⟨by omega, this.2⟩
  · rw [hgv x hx, hgl]

/-- **The simulation relation** between a spec state and the AIR view at time `t` (design note:
results/pq-wasm-base/README.md §10). -/
structure RelW (X : Ctx) (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat)
    (live : Msg → Prop) : Prop where
  frames : s.frames = f :: E.rest
  kLt : E.k < X.nf
  fn : f.fn = X.fnOf E.k
  pcEq : f.pc = pc
  pcLt : pc < (X.pfOf E.k).code.size
  labels : ∃ ls, (X.ckOf E.k).labels[pc]? = some ls ∧ f.labels = shiftLabels E.sb ls
  base : f.base = E.sb
  sbLe : E.sb ≤ s.stack.size
  height : (X.ckOf E.k).heights[pc]? = some (s.stack.size - E.sb)
  nloc : f.locals.size = (X.pfOf E.k).type.params.size + (X.pfOf E.k).locals.size
  gas : X.R * S + s.gas.g = X.g0
  numS : ∀ i, i < s.stack.size → isNum (s.stack[i]?.getD default)
  numL : ∀ j, j < f.locals.size → isNum (f.locals[j]?.getD default)
  tpsLt : ∀ i, i < s.stack.size → tps i < t
  tplLt : ∀ j, j < f.locals.size → tpl j < t
  envSep : ∀ x, E.live x → x.space ≠ 0 ∧ x.space ≠ E.lsp
  /-- Activation id 0 is the entry frame: no caller frames, stack base 0. -/
  entry : E.cid = 0 → E.rest = [] ∧ E.sb = 0
  /-- Field-size bounds on the frame fields (the AIR carries `sb`, `cid` as field elements). -/
  sbLt : E.sb < 2 ^ 28
  cidLt : E.cid < 2 ^ 28
  /-- The memory (space 3) part of the outer live set matches the spec memory. -/
  heap : HeapOK E s t
  live : ∀ x, live x ↔ x ∈ stackView s.stack tps ∨ x ∈ localView E.lsp f.locals tpl ∨ E.live x

/-- The relation with the frame data existential; `sb`/`cid` are the AIR state's, `k` the checked
function and `pc` the local pc (the AIR's global pc is `X.offOf k + pc`). -/
def Rel (X : Ctx) (s : St) (t k pc S sb cid : Nat) (live : Msg → Prop) : Prop :=
  ∃ E f tps tpl, E.sb = sb ∧ E.cid = cid ∧ E.k = k ∧ RelW X E s f tps tpl t pc S live

/-- A live stack message at slot `i` is the encoding of stack entry `i`. -/
theorem RelW.stack_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {x : Msg} (hx : live x)
    (hs : x.space = 0) (hi : x.slot < s.stack.size) :
    x = enc 0 x.slot (s.stack[x.slot]?.getD default) (tps x.slot) := by
  rcases (R.live x).mp hx with h | h | h
  · obtain ⟨i, hi', rfl⟩ := mem_stackView.mp h
    rfl
  · obtain ⟨j, _, rfl⟩ := mem_localView.mp h
    exfalso; simp only [enc_space, Env.lsp] at hs; omega
  · exact absurd hs (R.envSep x h).1

theorem RelW.local_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {x : Msg} (hx : live x)
    (hs : x.space = E.lsp) (hj : x.slot < f.locals.size) :
    x = enc E.lsp x.slot (f.locals[x.slot]?.getD default) (tpl x.slot) := by
  rcases (R.live x).mp hx with h | h | h
  · obtain ⟨i, _, rfl⟩ := mem_stackView.mp h
    exfalso; simp only [enc_space, Env.lsp] at hs; omega
  · obtain ⟨j, hj', rfl⟩ := mem_localView.mp h
    rfl
  · exact absurd hs (R.envSep x h).2

/-- **General view update.** The new stack keeps the first `n - k` entries and appends new ones
(producer time `t`); the locals change at most at index `J` (fresh producer time `t`). -/
theorem view_update {stk stk' locs locs' : Array Val} {tps tpl : Nat → Nat} {t k sp : Nat} (hsp : sp ≠ 0)
    (J : Option Nat) (hk : k ≤ stk.size)
    (keep : ∀ i, i < stk.size - k → stk'[i]? = stk[i]?) (hsz : stk.size - k ≤ stk'.size)
    (lsz : locs'.size = locs.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = locs[j]?)
    (hJ : ∀ j, J = some j → j < locs.size)
    (tpsLt : ∀ i, i < stk.size → tps i < t) (tplLt : ∀ j, j < locs.size → tpl j < t)
    (x : Msg) :
    (x ∈ stackView stk' (fun i => if i < stk.size - k then tps i else t) ∨
      x ∈ localView sp locs' (fun j => if some j = J then t else tpl j)) ↔
      ((x ∈ stackView stk tps ∨ x ∈ localView sp locs tpl) ∧
        x ∉ ((List.range k).map fun d => enc 0 (stk.size - k + d) (stk[stk.size - k + d]?.getD default)
          (tps (stk.size - k + d))) ++ J.toList.map (fun j => enc sp j (locs[j]?.getD default) (tpl j))) ∨
      x ∈ ((List.range (stk'.size - (stk.size - k))).map fun d =>
        enc 0 (stk.size - k + d) (stk'[stk.size - k + d]?.getD default) t) ++
        J.toList.map (fun j => enc sp j (locs'[j]?.getD default) t) := by
  simp only [mem_stackView, mem_localView, List.mem_append, List.mem_map, List.mem_range,
    Option.mem_toList]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · by_cases hlt : i < stk.size - k
      · left
        refine ⟨Or.inl ⟨i, by omega, ?_⟩, ?_⟩
        · simp [hlt, keep i hlt]
        · rintro (⟨d, hd, he⟩ | ⟨j, _, he⟩)
          · have := congrArg Msg.slot he; simp at this; omega
          · have := congrArg Msg.space he; simp at this; omega
      · right; left
        refine ⟨i - (stk.size - k), ?_, ?_⟩
        · exact Nat.sub_lt_sub_right (Nat.le_of_not_lt hlt) hi
        · have e : stk.size - k + (i - (stk.size - k)) = i := by omega
          simp only [hlt, ite_false, e]
    · by_cases hj' : some j = J
      · right; right
        exact ⟨j, hj'.symm, by simp [hj']⟩
      · left
        refine ⟨Or.inr ⟨j, by omega, ?_⟩, ?_⟩
        · simp [hj', lkeep j hj']
        · rintro (⟨d, hd, he⟩ | ⟨j0, hj0, he⟩)
          · have := congrArg Msg.space he; simp at this; omega
          · have := congrArg Msg.slot he; simp at this; subst this; exact hj' hj0.symm
  · rintro (⟨(⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩), hn⟩ | (⟨d, hd, rfl⟩ | ⟨j0, hj0, rfl⟩))
    · have hlt : i < stk.size - k := by
        refine Classical.byContradiction fun hc => hn (Or.inl ⟨i - (stk.size - k), by omega, ?_⟩)
        have e : stk.size - k + (i - (stk.size - k)) = i := by omega
        rw [e]
      left; exact ⟨i, by omega, by simp [hlt, keep i hlt]⟩
    · have hjJ : some j ≠ J := by
        intro hc; exact hn (Or.inr ⟨j, hc.symm, rfl⟩)
      right; exact ⟨j, by omega, by simp [hjJ, lkeep j hjJ]⟩
    · left; refine ⟨stk.size - k + d, by omega, ?_⟩
      rw [if_neg (by omega)]
    · right; exact ⟨j0, by rw [lsz]; exact hJ j0 hj0, by simp [hj0]⟩

end WasmBase
