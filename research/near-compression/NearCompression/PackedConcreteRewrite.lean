import NearCompression.PackedByteLayout

/-! Concrete rewrite soundness under byte ranges. No abstract macro or column
soundness assumptions remain; range derivation/global AIR assembly are separate. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def packedMacroPositions (regions : List (Nat × Nat)) : List (Nat × Bool) :=
  (packedMacroBases regions).flatMap (fun base=>[(base,false),(base,true)])

def packedConcreteMacro (regions : List (Nat × Nat)) (e : Expr) : Option Expr :=
  match (packedMacroPositions regions).find? (fun (base,nx)=>decide (e=packedSourceLimb base nx)) with
  | none => none
  | some (base,nx) => some (packedTargetLimb (packedColumnIndex regions base)
      (packedColumnIndex regions (base+8)) nx)

def packedConcreteColumn (regions : List (Nat × Nat)) (c : Nat) : Option Nat :=
  match packedColumnSlot regions c with
  | .scalar j => some j
  | .byte _ _ => none

def PackedMacroRanges (regions : List (Nat × Nat)) (env : Env Fp) : Prop :=
  ∀ base ∈ packedMacroBases regions, ∀ nx,
    (env.col (packedColumnIndex regions base) nx).toNat<256 ∧
    (env.col (packedColumnIndex regions (base+8)) nx).toNat<256

theorem packed_concrete_macro_sound (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (env : Env Fp)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·))
    (ranges : PackedMacroRanges regions env) (e e' : Expr)
    (rewritten : packedConcreteMacro regions e=some e') :
    e'.evalWith env=e.evalWith (packedLiftEnv regions env) := by
  unfold packedConcreteMacro at rewritten
  cases found : (packedMacroPositions regions).find?
      (fun (base,nx)=>decide (e=packedSourceLimb base nx)) with
  | none => simp [found] at rewritten
  | some pos =>
    obtain ⟨base,nx⟩ := pos
    simp only [found,Option.some.injEq] at rewritten
    subst e'
    have matched := List.find?_some found
    have same : e=packedSourceLimb base nx := of_decide_eq_true matched
    have mem := List.mem_of_find?_eq_some found
    obtain ⟨b,hb,hpos⟩ := List.mem_flatMap.mp mem
    have eq : base=b := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hpos
      rcases hpos with h | h <;> exact h.1
    have member : base ∈ packedMacroBases regions := eq.symm ▸ hb
    rw [same]
    exact packed_layout_macro_eval regions consistent env base member nx hn ha hm
      (ranges base member nx).1 (ranges base member nx).2

theorem packed_concrete_column_sound (regions : List (Nat × Nat)) (env : Env Fp)
    (c j : Nat) (h : packedConcreteColumn regions c=some j) (nx : Bool) :
    env.col j nx=(packedLiftEnv regions env).col c nx := by
  unfold packedConcreteColumn at h
  cases slot : packedColumnSlot regions c with
  | scalar k => simp only [slot,Option.some.injEq] at h; subst j
                exact (packed_lift_scalar regions env c k nx slot).symm
  | byte k bit => simp [slot] at h

theorem packed_concrete_rewrite_eval (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (env : Env Fp)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·))
    (ranges : PackedMacroRanges regions env) (e e' : Expr)
    (rewritten : packedRewrite (packedConcreteMacro regions) (packedConcreteColumn regions) e=some e') :
    e'.evalWith env=e.evalWith (packedLiftEnv regions env) :=
  packed_rewrite_eval _ _ _ _ (packed_lift_shared regions env)
    (packed_concrete_macro_sound regions consistent env hn ha hm ranges)
    (packed_concrete_column_sound regions env) e e' rewritten

theorem packed_concrete_constraints (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (env : Env Fp)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·))
    (ranges : PackedMacroRanges regions env) (es es' : List Expr)
    (rewritten : packedRewriteList (packedConcreteMacro regions)
      (packedConcreteColumn regions) es=some es')
    (holds : ∀ e∈es',e.evalWith env=0) :
    ∀ e∈es,e.evalWith (packedLiftEnv regions env)=0 :=
  packed_rewrite_constraints _ _ 0 _ _ (packed_lift_shared regions env)
    (packed_concrete_macro_sound regions consistent env hn ha hm ranges)
    (packed_concrete_column_sound regions env) es es' rewritten holds

theorem packed_concrete_interaction (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (env : Env Fp)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·))
    (ranges : PackedMacroRanges regions env) (i i' : Interaction)
    (rewritten : packedRewriteInteraction (packedConcreteMacro regions)
      (packedConcreteColumn regions) i=some i') :
    i'.bus=i.bus ∧ i'.send=i.send ∧
    i'.msg.map (fun e=>e.evalWith env)=i.msg.map (fun e=>e.evalWith (packedLiftEnv regions env)) ∧
    i'.mult.map (fun e=>e.evalWith env)=i.mult.map (fun e=>e.evalWith (packedLiftEnv regions env)) :=
  packed_rewrite_interaction _ _ _ _ (packed_lift_shared regions env)
    (packed_concrete_macro_sound regions consistent env hn ha hm ranges)
    (packed_concrete_column_sound regions env) i i' rewritten

end NearCompression
