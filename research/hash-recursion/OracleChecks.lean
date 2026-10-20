import HashRecursion

/-! Exact scalar checks of a two-qubit coherent query. The rational density
entries encode the usual |+>|0> to Bell-state example without approximating
sqrt(2). This is an example, not a restriction of the generic oracle model. -/
open HashRecursion.Quantum

abbrev B := Register 1 1 Unit

def b00 : B := (0#1, 0#1, ())
def b01 : B := (0#1, 1#1, ())
def b10 : B := (1#1, 0#1, ())
def b11 : B := (1#1, 1#1, ())

private theorem one_bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h := x.isLt
  have hn : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases hn with h0 | h1
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (BitVec.eq_of_toNat_eq h1)

def basis : FiniteBasis B where
  elements := [b00, b01, b10, b11]
  unique := by decide
  complete := by
    intro ⟨x, y, w⟩
    have hx := one_bit_cases x
    have hy := one_bit_cases y
    cases w
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [b00, b01, b10, b11]

/-- Density entries of |+><+| tensor |0><0|. -/
def initial (i j : B) : Rat :=
  if i.2.1 = 0#1 ∧ j.2.1 = 0#1 then 1 / 2 else 0

def result : B → B → Rat := queryDensity (fun x => x) initial

-- Querying identity with a zero response register correlates the registers.
example : result b00 b00 = 1 / 2 := by rfl
example : result b11 b11 = 1 / 2 := by rfl
example : result b01 b01 = 0 := by decide
example : result b10 b10 = 0 := by decide

-- Off-diagonal coherence survives; this is not a classical mixture.
example : result b00 b11 = 1 / 2 := by rfl
example : result b11 b00 = 1 / 2 := by rfl
example : dephaseInput result b00 b11 = 0 := by decide

-- Both have trace one: trace preservation alone cannot certify coherence.
example : (basis.elements.map (fun b => result b b)).sum = 1 := by
  change (1 / 2 : Rat) + (0 + (0 + (1 / 2 + 0))) = 1
  grind
example : (basis.elements.map (fun b => dephaseInput result b b)).sum = 1 := by
  simp only [dephaseInput_diagonal]
  change (1 / 2 : Rat) + (0 + (0 + (1 / 2 + 0))) = 1
  grind

example : queryDensity (fun x => x) result = initial :=
  queryDensity_involution (fun x => x) initial

-- The same loss of coherence is detected by the generic theorem.
example : queryDensity (fun x => x) (queryDensity (fun x => x)
    (dephaseInput result)) ≠ result :=
  recording_is_not_query (fun x => x) result b00 b11 (by decide) (by change (1 / 2 : Rat) ≠ 0; grind)
