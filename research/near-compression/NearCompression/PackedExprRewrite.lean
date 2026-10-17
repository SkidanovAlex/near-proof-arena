import ZkFormal.Air.Basic

/-! Fail-closed expression rewriting for byte packing. Macro and column
soundness are explicit premises, to be discharged for the concrete layout.
This is not yet a theorem about the Python generator or native verifier. -/
namespace NearCompression
open ZkFormal.Air

def packedRewrite (macroRule : Expr → Option Expr)
    (column : Nat → Option Nat) (e : Expr) : Option Expr :=
  match macroRule e with
  | some replacement => some replacement
  | none => match e with
    | .col c nx => (column c).map (fun c' => .col c' nx)
    | .add a b => do return .add (← packedRewrite macroRule column a) (← packedRewrite macroRule column b)
    | .mul a b => do return .mul (← packedRewrite macroRule column a) (← packedRewrite macroRule column b)
    | .neg a => (packedRewrite macroRule column a).map Expr.neg
    | e => some e

/-- Environments agree on everything except trace columns. -/
def PackedEnvAgreement {R : Type} (old packed : Env R) : Prop :=
  old.ofNat=packed.ofNat ∧ old.add=packed.add ∧ old.mul=packed.mul ∧
  old.neg=packed.neg ∧ old.pub=packed.pub ∧ old.isFirst=packed.isFirst ∧
  old.isLast=packed.isLast ∧ old.isTransition=packed.isTransition

theorem packed_rewrite_eval {R : Type} (old packed : Env R)
    (macroRule : Expr → Option Expr) (column : Nat → Option Nat)
    (shared : PackedEnvAgreement old packed)
    (macros : ∀ e e',macroRule e=some e' → e'.evalWith packed=e.evalWith old)
    (columns : ∀ c c',column c=some c' → ∀ nx,packed.col c' nx=old.col c nx)
    (e e' : Expr) (rewritten : packedRewrite macroRule column e=some e') :
    e'.evalWith packed=e.evalWith old := by
  obtain ⟨hn,ha,hm,hneg,hpub,hfirst,hlast,htrans⟩ := shared
  induction e generalizing e' with
  | const n | pub n | isFirst | isLast | isTransition =>
    unfold packedRewrite at rewritten
    split at rewritten
    · cases rewritten
      exact macros _ _ ‹_›
    · cases rewritten
      simp only [Expr.evalWith,hn,hpub,hfirst,hlast,htrans]
  | col c nx =>
    unfold packedRewrite at rewritten
    split at rewritten
    · cases rewritten
      exact macros _ _ ‹_›
    · cases hc : column c with
      | none => simp [hc] at rewritten
      | some c' =>
        simp only [hc,Option.map_some,Option.some.injEq] at rewritten
        subst e'
        exact columns c c' hc nx
  | add a b ia ib | mul a b ia ib =>
    unfold packedRewrite at rewritten
    split at rewritten
    · cases rewritten
      exact macros _ _ ‹_›
    · cases ea : packedRewrite macroRule column a with
      | none => simp [ea] at rewritten
      | some a' =>
        cases eb : packedRewrite macroRule column b with
        | none => simp [ea,eb] at rewritten
        | some b' =>
          simp only [ea,eb] at rewritten
          cases rewritten
          simp only [Expr.evalWith,ia _ ea,ib _ eb,ha,hm]
  | neg a ia =>
    unfold packedRewrite at rewritten
    split at rewritten
    · cases rewritten
      exact macros _ _ ‹_›
    · cases ea : packedRewrite macroRule column a with
      | none => simp [ea] at rewritten
      | some a' =>
        simp only [ea,Option.map_some,Option.some.injEq] at rewritten
        subst e'
        simp only [Expr.evalWith,ia _ ea,hneg]

def packedRewriteList (macroRule : Expr → Option Expr) (column : Nat → Option Nat) :
    List Expr → Option (List Expr)
  | [] => some []
  | e::es => do return (← packedRewrite macroRule column e)::(← packedRewriteList macroRule column es)

theorem packed_rewrite_list_eval {R : Type} (old packed : Env R)
    (macroRule : Expr → Option Expr) (column : Nat → Option Nat)
    (shared : PackedEnvAgreement old packed)
    (macros : ∀ e e',macroRule e=some e' → e'.evalWith packed=e.evalWith old)
    (columns : ∀ c c',column c=some c' → ∀ nx,packed.col c' nx=old.col c nx)
    (es es' : List Expr) (rewritten : packedRewriteList macroRule column es=some es') :
    es'.map (fun e=>e.evalWith packed)=es.map (fun e=>e.evalWith old) := by
  induction es generalizing es' with
  | nil => simp [packedRewriteList] at rewritten; subst es'; rfl
  | cons e es ih =>
    cases he : packedRewrite macroRule column e with
    | none => simp [packedRewriteList,he] at rewritten
    | some e' =>
      cases hs : packedRewriteList macroRule column es with
      | none => simp [packedRewriteList,he,hs] at rewritten
      | some tail =>
        simp [packedRewriteList,he,hs] at rewritten
        subst es'
        simp only [List.map_cons,
          packed_rewrite_eval old packed macroRule column shared macros columns e e' he,
          ih tail hs]

/-- Every retained constraint transfers from the packed to the lifted trace.
Removed Boolean/inactivity constraints must be justified separately. -/
theorem packed_rewrite_constraints {R : Type} (old packed : Env R) (zero : R)
    (macroRule : Expr → Option Expr) (column : Nat → Option Nat)
    (shared : PackedEnvAgreement old packed)
    (macros : ∀ e e',macroRule e=some e' → e'.evalWith packed=e.evalWith old)
    (columns : ∀ c c',column c=some c' → ∀ nx,packed.col c' nx=old.col c nx)
    (es es' : List Expr) (rewritten : packedRewriteList macroRule column es=some es')
    (holds : ∀ e∈es',e.evalWith packed=zero) :
    ∀ e∈es,e.evalWith old=zero := by
  have values := packed_rewrite_list_eval old packed macroRule column shared macros columns es es' rewritten
  intro e he
  have member : e.evalWith old ∈ es'.map (fun e=>e.evalWith packed) := by
    rw [values]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  obtain ⟨e',he',same⟩ := List.mem_map.mp member
  rw [←same]
  exact holds e' he'

def packedRewriteInteraction (macroRule : Expr → Option Expr)
    (column : Nat → Option Nat) (i : Interaction) : Option Interaction := do
  let msg ← packedRewriteList macroRule column i.msg
  let mult ← packedRewriteList macroRule column i.mult
  return {i with msg:=msg,mult:=mult}

/-- Messages and multiplicity-bit values, bus number and direction all survive
rewriting. This is local preservation, not yet the global bus-count theorem. -/
theorem packed_rewrite_interaction {R : Type} (old packed : Env R)
    (macroRule : Expr → Option Expr) (column : Nat → Option Nat)
    (shared : PackedEnvAgreement old packed)
    (macros : ∀ e e',macroRule e=some e' → e'.evalWith packed=e.evalWith old)
    (columns : ∀ c c',column c=some c' → ∀ nx,packed.col c' nx=old.col c nx)
    (i i' : Interaction) (rewritten : packedRewriteInteraction macroRule column i=some i') :
    i'.bus=i.bus ∧ i'.send=i.send ∧
    i'.msg.map (fun e=>e.evalWith packed)=i.msg.map (fun e=>e.evalWith old) ∧
    i'.mult.map (fun e=>e.evalWith packed)=i.mult.map (fun e=>e.evalWith old) := by
  cases hm : packedRewriteList macroRule column i.msg with
  | none => simp [packedRewriteInteraction,hm] at rewritten
  | some msg =>
    cases hc : packedRewriteList macroRule column i.mult with
    | none => simp [packedRewriteInteraction,hm,hc] at rewritten
    | some mult =>
      simp [packedRewriteInteraction,hm,hc] at rewritten
      subst i'
      exact ⟨rfl,rfl,
        packed_rewrite_list_eval old packed macroRule column shared macros columns _ _ hm,
        packed_rewrite_list_eval old packed macroRule column shared macros columns _ _ hc⟩

/-- A removed scalar bit cannot slip through without a proved macro rule. -/
theorem packed_rewrite_rejects_unmapped (macroRule : Expr → Option Expr)
    (column : Nat → Option Nat) (c : Nat) (nx : Bool)
    (noMacro : macroRule (.col c nx)=none) (removed : column c=none) :
    packedRewrite macroRule column (.col c nx)=none := by
  simp [packedRewrite,noMacro,removed]

-- Kernel-reduced regression checks cover macro precedence, next-row mapping,
-- and propagation of an unmapped-column failure through nested expressions.
private def rewriteTestMacro : Expr → Option Expr
  | .add (.col 0 false) (.col 1 false) => some (.col 7 false)
  | _ => none
private def rewriteTestColumn (c : Nat) : Option Nat :=
  if c<2 then none else some (c-1)

example : packedRewrite rewriteTestMacro rewriteTestColumn
    (.mul (.add (.col 0 false) (.col 1 false)) (.col 3 true)) =
    some (.mul (.col 7 false) (.col 2 true)) := by decide
example : packedRewrite rewriteTestMacro rewriteTestColumn
    (.neg (.mul (.const 2) (.col 0 true)))=none := by decide
example : packedRewriteInteraction rewriteTestMacro rewriteTestColumn
    {bus:=2,send:=false,msg:=[.col 3 true],mult:=[.const 1]} =
    some {bus:=2,send:=false,msg:=[.col 2 true],mult:=[.const 1]} := by decide

end NearCompression
