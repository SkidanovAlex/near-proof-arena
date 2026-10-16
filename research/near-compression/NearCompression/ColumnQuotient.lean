import ZkFormal.V2.VerifierDefs

/-! Column quotient refinement. Every original constraint and interaction is
rewritten, not discarded. The map may identify arbitrary columns: validity of
the quotient implies validity of the expanded original trace. Finding aliases
from unconditional equalities is only needed for honest-witness projection. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def quotientExpr (f : Nat → Nat) : Expr → Expr
  | .col c nx => .col (f c) nx
  | .add a b => .add (quotientExpr f a) (quotientExpr f b)
  | .mul a b => .mul (quotientExpr f a) (quotientExpr f b)
  | .neg a => .neg (quotientExpr f a)
  | e => e

def quotientTrace (f : Nat → Nat → Nat) (tr : Trace Fp) : Trace Fp :=
  ⟨tr.log,fun t r c => tr.cell t r (f t c)⟩

def quotientInteraction (f : Nat → Nat) (i : Interaction) : Interaction :=
  {i with mult := i.mult.map (quotientExpr f),msg := i.msg.map (quotientExpr f)}

theorem quotient_expr_eval (f : Nat → Nat → Nat) (tr : Trace Fp)
    (pub : List Fp) (t r : Nat) (e : Expr) :
    (quotientExpr (f t) e).eval tr t r pub=e.eval (quotientTrace f tr) t r pub := by
  induction e <;> simp_all [quotientExpr,Expr.eval,Expr.evalWith,rowEnv,quotientTrace,Trace.height] <;> rfl

theorem quotient_interaction_msg (f : Nat → Nat → Nat) (tr : Trace Fp)
    (pub : List Fp) (t r : Nat) (i : Interaction) :
    (quotientInteraction (f t) i).msgVal tr t r pub=i.msgVal (quotientTrace f tr) t r pub := by
  simp only [quotientInteraction,Interaction.msgVal,List.map_map]
  apply List.map_congr_left
  intro e he
  exact quotient_expr_eval f tr pub t r e

theorem quotient_interaction_mult (f : Nat → Nat → Nat) (tr : Trace Fp)
    (pub : List Fp) (t r : Nat) (i : Interaction) :
    (quotientInteraction (f t) i).multNat tr t r pub=i.multNat (quotientTrace f tr) t r pub := by
  have all : ∀ (es : List Expr) (k : Nat),
      Interaction.multNat.go tr t r pub (es.map (quotientExpr (f t))) k=
      Interaction.multNat.go (quotientTrace f tr) t r pub es k := by
    intro es
    induction es with
    | nil => intro k; rfl
    | cons e es ih => intro k; simp only [List.map_cons,Interaction.multNat.go,quotient_expr_eval,ih]
  exact all i.mult 0

theorem quotient_table_bus_count (f : Nat → Nat → Nat) (tr : Trace Fp)
    (pub : List Fp) (t b : Nat) (s : Bool) (m : List Fp) (is : List Interaction) :
    tableBusCount (is.map (quotientInteraction (f t))) tr t pub b s m=
      tableBusCount is (quotientTrace f tr) t pub b s m := by
  unfold tableBusCount
  have inner (r acc : Nat) :
      (is.map (quotientInteraction (f t))).foldr (fun i acc' =>
        (if i.bus=b ∧ i.send=s ∧ i.msgVal tr t r pub=m then i.multNat tr t r pub else 0)+acc') acc=
      is.foldr (fun i acc' =>
        (if i.bus=b ∧ i.send=s ∧ i.msgVal (quotientTrace f tr) t r pub=m
          then i.multNat (quotientTrace f tr) t r pub else 0)+acc') acc := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons,List.foldr_cons,quotient_interaction_msg,quotient_interaction_mult,ih]
      rfl
  change (List.range (tr.height t)).foldr _ 0=(List.range (tr.height t)).foldr _ 0
  apply congrArg (fun g => (List.range (tr.height t)).foldr g 0)
  funext r acc
  exact inner r acc

def quotientTable (f : Nat → Nat) (width : Nat) (table : Table) : Table :=
  {table with width := width,constraints := table.constraints.map (quotientExpr f), interactions := table.interactions.map (quotientInteraction f)}

def quotientTables (f : Nat → Nat → Nat) (width : Nat → Nat) : List Table → Nat → List Table
  | [], _ => []
  | table :: rest, k => quotientTable (f k) (width k) table :: quotientTables f width rest (k+1)

def quotientAir (f : Nat → Nat → Nat) (width : Nat → Nat) (air : AirP) : AirP :=
  {air with tables := quotientTables f width air.tables 0}

theorem quotient_tables_length (f : Nat → Nat → Nat) (width : Nat → Nat)
    (tables : List Table) (k : Nat) : (quotientTables f width tables k).length=tables.length := by
  induction tables generalizing k with
  | nil => rfl
  | cons t ts ih => simp [quotientTables,ih]

theorem quotient_tables_get (f : Nat → Nat → Nat) (width : Nat → Nat)
    (tables : List Table) (k t : Nat) (ht : t<tables.length) :
    (quotientTables f width tables k)[t]'(by rw [quotient_tables_length];exact ht)=
      quotientTable (f (k+t)) (width (k+t)) tables[t] := by
  induction tables generalizing k t with
  | nil => simp at ht
  | cons table rest ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simpa only [quotientTables,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (k+1) t (by simpa using ht)

theorem quotient_bus_count (f : Nat → Nat → Nat) (width : Nat → Nat) (air : AirP)
    (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount (quotientAir f width air).toAir tr pub b s m=
      busCount air.toAir (quotientTrace f tr) pub b s m := by
  have all (tables : List Table) (k : Nat) :
      busCount.go tr pub b s m (quotientTables f width tables k) k=
      busCount.go (quotientTrace f tr) pub b s m tables k := by
    induction tables generalizing k with
    | nil => rfl
    | cons table rest ih =>
      simp only [quotientTables,busCount.go,quotientTable,quotient_table_bus_count,ih]
  exact all air.tables 0

/-- Any accepted quotient AIR expands into an accepted original AIR, including
all public segments and exact natural bus multiplicities. -/
theorem quotient_holdsP (f : Nat → Nat → Nat) (width : Nat → Nat) (air : AirP)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (quotientAir f width air) pub tr) :
    HoldsP air pub (quotientTrace f tr) := by
  have table (t : Nat) (ht : t<air.tables.length) :
      (quotientAir f width air).tables[t]'(by simpa [quotientAir,quotient_tables_length] using ht)=
      quotientTable (f t) (width t) air.tables[t] := by
    simpa only [quotientAir,Nat.zero_add] using quotient_tables_get f width air.tables 0 t ht
  constructor
  · intro t ht
    have value := holds.logBound t (by simpa [quotientAir,quotient_tables_length] using ht)
    rw [table t ht] at value
    exact value
  · intro t ht r hr e he
    have value := holds.constr t (by simpa [quotientAir,quotient_tables_length] using ht) r hr
      (quotientExpr (f t) e)
    rw [table t ht] at value
    rw [←quotient_expr_eval]
    exact value (List.mem_map.mpr ⟨e,he,rfl⟩)
  · intro t ht r hr i hi e he
    have value := holds.bits t (by simpa [quotientAir,quotient_tables_length] using ht) r hr
      (quotientInteraction (f t) i)
    rw [table t ht] at value
    have bits := value (List.mem_map.mpr ⟨i,hi,rfl⟩) (quotientExpr (f t) e) (List.mem_map.mpr ⟨e,he,rfl⟩)
    simpa only [quotient_expr_eval] using bits
  · exact holds.pubFit
  · intro b m
    have balance := holds.balance b m
    rw [quotient_bus_count,quotient_bus_count] at balance
    exact balance

end NearCompression
