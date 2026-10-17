import NearCompression.PackedRangeBus

/-! Assembly of retained and reconstructed constraints on a lifted trace.
Global original-bus preservation is not established in this module. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def packedLiftTrace (layouts : Nat → List (Nat × Nat)) (tr : Trace Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r c=>match packedColumnSlot (layouts t) c with
    | .scalar j => tr.cell t r j
    | .byte j bit => Fp.ofNat ((tr.cell t r j).toNat/2^bit%2)}

theorem packed_lift_trace_height (layouts : Nat → List (Nat × Nat)) (tr : Trace Fp) (t : Nat) :
    (packedLiftTrace layouts tr).height t=tr.height t := rfl

theorem packed_lift_trace_env (layouts : Nat → List (Nat × Nat)) (tr : Trace Fp)
    (t r : Nat) (pub : List Fp) :
    rowEnv (packedLiftTrace layouts tr) t r pub=packedLiftEnv (layouts t) (rowEnv tr t r pub) := by
  unfold rowEnv packedLiftEnv packedLiftTrace Trace.height
  congr 1

def packedOldBoolean (c : Nat) : Expr :=
  .add (.mul (.col c false) (.add (.col c false) (.neg (.const 1)))) (.neg (.const 0))
def packedOldInactive (active c : Nat) : Expr :=
  .mul (.add (.const 1) (.neg (.col active false))) (.add (.col c false) (.neg (.const 0)))
def packedNewInactive (active c : Nat) : Expr :=
  .mul (.add (.const 1) (.neg (.col active false))) (.col c false)

/-- A structural witness accounts for each original constraint. There is no
fallback accepting an unrecognized or merely unrewritable expression. -/
inductive PackedConstraintWitness (regions : List (Nat × Nat)) (target : List Expr) : Expr → Prop where
  | retained (e e' : Expr)
      (rewrite : packedRewrite (packedConcreteMacro regions) (packedConcreteColumn regions) e=some e')
      (member : e'∈target) : PackedConstraintWitness regions target e
  | boolean (c j bit : Nat) (slot : packedColumnSlot regions c=.byte j bit) :
      PackedConstraintWitness regions target (packedOldBoolean c)
  | inactive (active mappedActive c j bit : Nat)
      (slot : packedColumnSlot regions c=.byte j bit)
      (activeSlot : packedColumnSlot regions active=.scalar mappedActive)
      (member : packedNewInactive mappedActive j∈target) :
      PackedConstraintWitness regions target (packedOldInactive active c)

theorem packed_constraint_witness_sound (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (env : Env Fp)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·)) (hneg : env.neg=(- ·))
    (ranges : PackedMacroRanges regions env) (target : List Expr)
    (holds : ∀ e∈target,e.evalWith env=0) (e : Expr)
    (covered : PackedConstraintWitness regions target e) :
    e.evalWith (packedLiftEnv regions env)=0 := by
  cases covered with
  | retained e e' rewrite member =>
    rw [←packed_concrete_rewrite_eval regions consistent env hn ha hm ranges e e' rewrite]
    exact holds e' member
  | boolean c j bit slot =>
    have h:=packed_lift_bit_boolean regions env c j bit false slot
    change _=0
    simp only [packedOldBoolean,Expr.evalWith]
    change env.add (env.mul ((packedLiftEnv regions env).col c false)
      (env.add ((packedLiftEnv regions env).col c false) (env.neg (env.ofNat 1))))
      (env.neg (env.ofNat 0))=0
    rw [hn,ha,hm,hneg]
    change (packedLiftEnv regions env).col c false*((packedLiftEnv regions env).col c false+ -(1:Fp)) + -(0:Fp)=0
    grind
  | inactive active mappedActive c j bit slot activeSlot member =>
    have byteZero:=holds _ member
    simp only [packedNewInactive,Expr.evalWith,hn,ha,hm,hneg] at byteZero
    have byteZero' : (1-env.col mappedActive false)*env.col j false=0 := by
      change ((1:Fp)+ -env.col mappedActive false)*env.col j false=0 at byteZero
      grind
    have h:=packed_lift_bit_inactive regions env c j bit false (env.col mappedActive false) slot byteZero'
    have act:=packed_lift_scalar regions env active mappedActive false activeSlot
    simp only [packedOldInactive,Expr.evalWith]
    change env.mul (env.add (env.ofNat 1) (env.neg ((packedLiftEnv regions env).col active false)))
      (env.add ((packedLiftEnv regions env).col c false) (env.neg (env.ofNat 0)))=0
    rw [hn,ha,hm,hneg,act]
    change ((1:Fp)+ -env.col mappedActive false)*(_+ -(0:Fp))=0
    grind

/-- Every source constraint holds on the reconstructed trace when its
structural witness is supplied and the packed AIR satisfies HoldsP. -/
theorem packed_constraints_from_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP air pub tr) (rangeTable : Nat) (source : PackedRangeSource air rangeTable)
    (layouts : Nat → List (Nat × Nat)) (t r : Nat) (ht : t<air.tables.length) (hr : r<tr.height t)
    (consistent : PackedLayoutConsistent (layouts t))
    (senders : ∀ base∈packedMacroBases (layouts t),
      packedRangeSend (packedColumnIndex (layouts t) base)∈air.tables[t]!.interactions ∧
      packedRangeSend (packedColumnIndex (layouts t) (base+8))∈air.tables[t]!.interactions)
    (original : List Expr)
    (coverage : ∀ e∈original,PackedConstraintWitness (layouts t) air.tables[t].constraints e) :
    ∀ e∈original,e.eval (packedLiftTrace layouts tr) t r pub=0 := by
  intro e he
  unfold Expr.eval
  rw [packed_lift_trace_env]
  exact packed_constraint_witness_sound (layouts t) consistent (rowEnv tr t r pub) rfl rfl rfl rfl
    (packed_macro_ranges_from_holds air tr pub holds rangeTable source (layouts t) t r ht hr senders)
    _ (holds.constr t ht r hr) e (coverage e he)

local instance : BEq Expr := instBEqOfDecidableEq
local instance : LawfulBEq Expr := instLawfulBEq

inductive PackedConstraintCert where
  | retained (rewritten : Expr)
  | boolean (column : Nat)
  | inactive (active column : Nat)

def packedConstraintCertCheck (regions : List (Nat × Nat)) (target : List Expr)
    (e : Expr) : PackedConstraintCert → Bool
  | .retained e' => decide (packedRewrite (packedConcreteMacro regions)
      (packedConcreteColumn regions) e=some e' ∧ e'∈target)
  | .boolean c => match packedColumnSlot regions c with
    | .scalar _ => false
    | .byte _ _ => decide (e=packedOldBoolean c)
  | .inactive active c => match packedColumnSlot regions c,packedColumnSlot regions active with
    | .byte j _,.scalar mapped => decide (e=packedOldInactive active c ∧ packedNewInactive mapped j∈target)
    | _,_ => false

theorem packed_constraint_cert_sound (regions : List (Nat × Nat)) (target : List Expr)
    (e : Expr) (cert : PackedConstraintCert)
    (accepted : packedConstraintCertCheck regions target e cert=true) :
    PackedConstraintWitness regions target e := by
  cases cert with
  | retained e' =>
    have h:=of_decide_eq_true accepted
    exact .retained e e' h.1 h.2
  | boolean c =>
    simp only [packedConstraintCertCheck] at accepted
    cases slot : packedColumnSlot regions c with
    | scalar j => simp [slot] at accepted
    | byte j bit =>
      rw [slot] at accepted
      have h : e=packedOldBoolean c := of_decide_eq_true accepted
      rw [h]
      exact .boolean c j bit slot
  | inactive active c =>
    simp only [packedConstraintCertCheck] at accepted
    cases slot : packedColumnSlot regions c with
    | scalar j => simp [slot] at accepted
    | byte j bit =>
      cases act : packedColumnSlot regions active with
      | byte k b => simp [slot,act] at accepted
      | scalar mapped =>
        rw [slot,act] at accepted
        have h:=of_decide_eq_true accepted
        rw [h.1]
        exact .inactive active mapped c j bit slot act h.2

end NearCompression
