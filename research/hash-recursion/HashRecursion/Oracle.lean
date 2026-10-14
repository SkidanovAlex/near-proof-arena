import Std

/-!
Finite coherent hash-oracle semantics. Amplitudes are generic: no restriction to
rational or classical states is imposed. Preservation of arbitrary additive
pairings includes the complex inner product once complex scalars are supplied.
This file does not construct complex numbers, random functions, measurements,
or a QROM soundness reduction.
-/
namespace HashRecursion.Quantum

/-- Explicit complete finite basis, enumerated without duplication. -/
structure FiniteBasis (B : Type) where
  elements : List B
  unique : elements.Nodup
  complete : ∀ b, b ∈ elements

theorem FiniteBasis.involution_perm {B : Type} (basis : FiniteBasis B)
    (f : B → B) (hf : ∀ b, f (f b) = b) :
    (basis.elements.map f).Perm basis.elements := by
  have hinj : Function.Injective f := by
    intro a b h
    have hh := congrArg f h
    simpa only [hf] using hh
  have hnd : (basis.elements.map f).Nodup := by
    change (basis.elements.map f).Pairwise (fun a b => a ≠ b)
    rw [List.pairwise_map]
    exact basis.unique.imp (fun hne heq => hne (hinj heq))
  apply (List.perm_ext_iff_of_nodup hnd basis.unique).mpr
  intro b
  constructor
  · intro _; exact basis.complete b
  · intro _
    exact List.mem_map.mpr ⟨f b, basis.complete (f b), hf b⟩

/-- x: query register; y: response register; w: arbitrary private workspace.
The workspace need not be independent of the query/response amplitudes. -/
abbrev Register (inputBits outputBits : Nat) (W : Type) :=
  BitVec inputBits × BitVec outputBits × W

def oracleStep {n m : Nat} {W : Type} (h : BitVec n → BitVec m)
    (b : Register n m W) : Register n m W :=
  (b.1, b.2.1 ^^^ h b.1, b.2.2)

theorem oracleStep_involution {n m : Nat} {W : Type}
    (h : BitVec n → BitVec m) (b : Register n m W) :
    oracleStep h (oracleStep h b) = b := by
  rcases b with ⟨x, y, w⟩
  simp [oracleStep, BitVec.xor_assoc]

/-- Pullback of amplitudes by the inverse basis permutation. The standard XOR
oracle is its own inverse, so this implements |x,y,w> ↦ |x,y XOR h(x),w>. -/
def query {n m : Nat} {W A : Type} (h : BitVec n → BitVec m)
    (ψ : Register n m W → A) : Register n m W → A :=
  fun b => ψ (oracleStep h b)

theorem query_involution {n m : Nat} {W A : Type}
    (h : BitVec n → BitVec m) (ψ : Register n m W → A) :
    query h (query h ψ) = ψ := by
  funext b
  simp [query, oracleStep_involution]

/-- Pointwise linear combinations are preserved, for any scalar operations. -/
theorem query_linear {n m : Nat} {W A : Type} [Add A] [Mul A]
    (h : BitVec n → BitVec m) (a c : A) (ψ φ : Register n m W → A) :
    query h (fun b => a * ψ b + c * φ b) =
      (fun b => a * query h ψ b + c * query h φ b) := rfl

def pairSum {B A S : Type} [Lean.Grind.AddCommMonoid S]
    (basis : FiniteBasis B) (pair : A → A → S) (ψ φ : B → A) : S :=
  (basis.elements.map (fun b => pair (ψ b) (φ b))).sum

private theorem sum_perm {S : Type} [Lean.Grind.AddCommMonoid S]
    {xs ys : List S} (h : xs.Perm ys) : xs.sum = ys.sum := by
  apply h.foldr_eq'
  intro x _ y _ z
  rw [← Lean.Grind.AddCommMonoid.add_assoc,
    Lean.Grind.AddCommMonoid.add_comm y x,
    Lean.Grind.AddCommMonoid.add_assoc]

/-- In particular, take S=A=complex scalars and pair(a,b)=conj(a)*b.
Together with linearity and involution, this is the algebraic unitarity result.
The theorem itself does not assume or construct a complex scalar instance. -/
theorem query_preserves_pairSum {n m : Nat} {W A S : Type}
    [Lean.Grind.AddCommMonoid S] (basis : FiniteBasis (Register n m W))
    (pair : A → A → S) (h : BitVec n → BitVec m)
    (ψ φ : Register n m W → A) :
    pairSum basis pair (query h ψ) (query h φ) = pairSum basis pair ψ φ := by
  have hp := (basis.involution_perm (oracleStep h) (oracleStep_involution h)).map
    (fun b => pair (ψ b) (φ b))
  have hs := sum_perm hp
  simpa only [pairSum, List.map_map, Function.comp_def, query] using hs

/-- Conjugation of a density matrix by the same permutation oracle. -/
def queryDensity {n m : Nat} {W A : Type} (h : BitVec n → BitVec m)
    (ρ : Register n m W → Register n m W → A) :=
  fun i j => ρ (oracleStep h i) (oracleStep h j)

theorem queryDensity_involution {n m : Nat} {W A : Type}
    (h : BitVec n → BitVec m) (ρ : Register n m W → Register n m W → A) :
    queryDensity h (queryDensity h ρ) = ρ := by
  funext i j
  simp [queryDensity, oracleStep_involution]

/-- Pure-state and density-matrix descriptions agree, for any scalar pairing. -/
theorem queryDensity_pure {n m : Nat} {W A S : Type}
    (h : BitVec n → BitVec m) (pair : A → A → S) (ψ : Register n m W → A) :
    queryDensity h (fun i j => pair (ψ i) (ψ j)) =
      (fun i j => pair (query h ψ i) (query h ψ j)) := rfl

theorem queryDensity_trace {n m : Nat} {W S : Type} [Lean.Grind.AddCommMonoid S]
    (basis : FiniteBasis (Register n m W)) (h : BitVec n → BitVec m)
    (ρ : Register n m W → Register n m W → S) :
    (basis.elements.map (fun b => queryDensity h ρ b b)).sum =
      (basis.elements.map (fun b => ρ b b)).sum := by
  have hp := (basis.involution_perm (oracleStep h) (oracleStep_involution h)).map
    (fun b => ρ b b)
  simpa only [List.map_map, Function.comp_def, queryDensity] using sum_perm hp

/-- Measuring and forgetting the input register removes cross-input coherence.
This is a different operation from a coherent query, despite preserving trace. -/
def dephaseInput {n m : Nat} {W A : Type} [Zero A]
    (ρ : Register n m W → Register n m W → A) :=
  fun i j => if i.1 = j.1 then ρ i j else 0

theorem dephaseInput_diagonal {n m : Nat} {W A : Type} [Zero A]
    (ρ : Register n m W → Register n m W → A) (i : Register n m W) :
    dephaseInput ρ i i = ρ i i := by simp [dephaseInput]

/-- A coherent off-diagonal entry survives two oracle queries, but is destroyed
by measuring the input. A trace-only model would miss this distinction. -/
theorem recording_is_not_query {n m : Nat} {W A : Type} [Zero A]
    (h : BitVec n → BitVec m) (ρ : Register n m W → Register n m W → A)
    (i j : Register n m W) (hij : i.1 ≠ j.1) (hρ : ρ i j ≠ 0) :
    queryDensity h (queryDensity h (dephaseInput ρ)) ≠ ρ := by
  rw [queryDensity_involution]
  intro heq
  have hh := congrFun (congrFun heq i) j
  simp only [dephaseInput, hij, ite_false] at hh
  exact hρ hh.symm

end HashRecursion.Quantum
