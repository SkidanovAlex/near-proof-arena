import WasmBase.Prelude
import WasmBase.Check
/-!
# WasmBase.Event — channel messages, the spec-state relation, and the gas/charge step

The value channel (bus CH) carries `Msg`s.  A spec state `s` (one frame `f`) is related to a set
`live` of channel messages when `live` is exactly the encoding of the operand stack (space 0,
slot = stack index) and of the locals (space 1, slot = local index), each with some producer time
`< t`.
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

def localView (locs : Array Val) (tpl : Nat → Nat) : List Msg :=
  (List.range locs.size).map fun j => enc 1 j (locs[j]?.getD default) (tpl j)

theorem mem_stackView {x : Msg} {stk : Array Val} {tps : Nat → Nat} :
    x ∈ stackView stk tps ↔ ∃ i, i < stk.size ∧ x = enc 0 i (stk[i]?.getD default) (tps i) := by
  simp only [stackView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem mem_localView {x : Msg} {locs : Array Val} {tpl : Nat → Nat} :
    x ∈ localView locs tpl ↔ ∃ j, j < locs.size ∧ x = enc 1 j (locs[j]?.getD default) (tpl j) := by
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

/-- The static context of one function call. -/
structure Ctx where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  pf : PFunc
  ck : CheckOut
  g0 : Nat
  hpf : p.funcs[fn]? = some pf
  hck : check cfg p fn = some ck

def Ctx.R (X : Ctx) : Nat := X.cfg.regularOpCost

/-- **The simulation relation** between a spec state and the AIR view at time `t`. -/
structure RelW (X : Ctx) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) :
    Prop where
  frames : s.frames = [f]
  fn : f.fn = X.fn
  pcEq : f.pc = pc
  pcLt : pc < X.pf.code.size
  labels : X.ck.labels[pc]? = some f.labels
  base : f.base = 0
  height : X.ck.heights[pc]? = some s.stack.size
  nloc : f.locals.size = X.pf.locals.size
  gas : X.R * S + s.gas.g = X.g0
  numS : ∀ i, i < s.stack.size → isNum (s.stack[i]?.getD default)
  numL : ∀ j, j < f.locals.size → isNum (f.locals[j]?.getD default)
  tpsLt : ∀ i, i < s.stack.size → tps i < t
  tplLt : ∀ j, j < f.locals.size → tpl j < t
  live : ∀ x, live x ↔ x ∈ stackView s.stack tps ∨ x ∈ localView f.locals tpl

def Rel (X : Ctx) (s : St) (t pc S : Nat) (live : Msg → Prop) : Prop :=
  ∃ f tps tpl, RelW X s f tps tpl t pc S live

/-- A live stack message at slot `i` is the encoding of stack entry `i`. -/
theorem RelW.stack_msg {X : Ctx} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {x : Msg} (hx : live x)
    (hs : x.space = 0) (hi : x.slot < s.stack.size) :
    x = enc 0 x.slot (s.stack[x.slot]?.getD default) (tps x.slot) := by
  rcases (R.live x).mp hx with h | h
  · obtain ⟨i, hi', rfl⟩ := mem_stackView.mp h
    rfl
  · obtain ⟨j, _, rfl⟩ := mem_localView.mp h
    simp at hs

theorem RelW.local_msg {X : Ctx} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {x : Msg} (hx : live x)
    (hs : x.space = 1) (hj : x.slot < f.locals.size) :
    x = enc 1 x.slot (f.locals[x.slot]?.getD default) (tpl x.slot) := by
  rcases (R.live x).mp hx with h | h
  · obtain ⟨i, _, rfl⟩ := mem_stackView.mp h
    simp at hs
  · obtain ⟨j, hj', rfl⟩ := mem_localView.mp h
    rfl

/-- **General view update.** The new stack keeps the first `n - k` entries and appends new ones
(producer time `t`); the locals change at most at index `J` (fresh producer time `t`). -/
theorem view_update {stk stk' locs locs' : Array Val} {tps tpl : Nat → Nat} {t k : Nat}
    (J : Option Nat) (hk : k ≤ stk.size)
    (keep : ∀ i, i < stk.size - k → stk'[i]? = stk[i]?) (hsz : stk.size - k ≤ stk'.size)
    (lsz : locs'.size = locs.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = locs[j]?)
    (hJ : ∀ j, J = some j → j < locs.size)
    (tpsLt : ∀ i, i < stk.size → tps i < t) (tplLt : ∀ j, j < locs.size → tpl j < t)
    (x : Msg) :
    (x ∈ stackView stk' (fun i => if i < stk.size - k then tps i else t) ∨
      x ∈ localView locs' (fun j => if some j = J then t else tpl j)) ↔
      ((x ∈ stackView stk tps ∨ x ∈ localView locs tpl) ∧
        x ∉ ((List.range k).map fun d => enc 0 (stk.size - k + d) (stk[stk.size - k + d]?.getD default)
          (tps (stk.size - k + d))) ++ J.toList.map (fun j => enc 1 j (locs[j]?.getD default) (tpl j))) ∨
      x ∈ ((List.range (stk'.size - (stk.size - k))).map fun d =>
        enc 0 (stk.size - k + d) (stk'[stk.size - k + d]?.getD default) t) ++
        J.toList.map (fun j => enc 1 j (locs'[j]?.getD default) t) := by
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
          · have := congrArg Msg.space he; simp at this
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
          · have := congrArg Msg.space he; simp at this
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
