import ZkFormal.PQ.Aggregation.Statement

/-!
# ZkFormal.PQ.Aggregation.Shape — the aggregation tree's shape is irrelevant

Lane `pq-base-aggregation`. Combines `Tree` (execution semantics) and `Statement` (range
statement) and states the shape-independence facts a paper needs for "arbitrary aggregation":

* **`tree_run_shape_irrelevant`**: two trees with the same leaf list have the same run.
* **`tree_root_shape_irrelevant`**: two trees with the same leaves have the same composed root,
  hence the same range digest, hence the same `V_d` statement check.
* **`root_of_tree`**: the composed root is the statement spanning the first leaf's
  context/start index/start state and the last leaf's end index/end state. Arity and depth do not
  appear.

These are the statement-level content of Z4 (final-layer statement independence) and Z5 (a fixed
point exists for every tree) in
`docs/logs/pq-arbitrary-aggregation-proof-obligations-2026-10-19.md`. The byte-level size argument
and the QROM extraction (N3/N4) are separate.
-/

namespace ZkFormal.PQ.Aggregation

open NearSpecV3.Wasm

namespace Shape

variable {α : Type} [DecidableEq α]

/-- Two trees with the same leaf list have the same run. -/
theorem tree_run_shape_irrelevant (cfg : NearCfg) (p : Prepared) (t₁ t₂ : RangeTree) (s : St)
    (h : t₁.leaves = t₂.leaves) :
    t₁.run cfg p s = t₂.run cfg p s := by
  rw [RangeTree.run_eq_foldSegments, RangeTree.run_eq_foldSegments, h]

/-- Two trees with the same leaves have the same composed root. -/
theorem tree_root_shape_irrelevant (t₁ t₂ : RangeTree) (f : Nat → Stmt.Stmt α) (r₁ r₂ : Stmt.Stmt α)
    (h : t₁.leaves = t₂.leaves)
    (h₁ : Stmt.compose (t₁.leaves.map f) = some r₁)
    (h₂ : Stmt.compose (t₂.leaves.map f) = some r₂) :
    r₁ = r₂ := by
  rw [h] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- `Stmt.root` of `s :: rest` reads its context/start from `s` and its end from the last
statement. -/
theorem root_cons (s : Stmt.Stmt α) (rest : List (Stmt.Stmt α)) (t : Stmt.Stmt α)
    (hlast : (s :: rest).getLast? = some t) :
    Stmt.root (s :: rest) = some ⟨s.ctx, s.a, t.e, s.sa, t.se⟩ := by
  cases rest with
  | nil =>
    simp only [List.getLast?_cons, List.getLast?_nil] at hlast
    have : t = s := (Option.some.inj hlast).symm
    subst this
    rfl
  | cons u us =>
    have h : (u :: us).getLast? = some t := by
      simpa [List.getLast?_cons_cons] using hlast
    simp only [Stmt.root, h]
    rfl

/-- `getLast?` of a mapped nonempty list. -/
theorem getLast?_map_cons (f : Nat → Stmt.Stmt α) (j : Nat) (tail : List Nat) (jl : Nat)
    (hlast : (j :: tail).getLast? = some jl) :
    ((j :: tail).map f).getLast? = some (f jl) := by
  rw [List.getLast?_map]
  rw [hlast]
  rfl

/-- **The root of a tree.** For a tree whose leaf statements chain, the composed statement is the
statement from the first leaf's context/start index/start state to the last leaf's end
index/end state. Arity and depth do not appear. -/
theorem root_of_tree (t : RangeTree) (f : Nat → Stmt.Stmt α) (s : Stmt.Stmt α) (j jl : Nat)
    (hne : t.leaves ≠ [])
    (hhead : t.leaves.head? = some j)
    (hlast : t.leaves.getLast? = some jl)
    (hchain : Stmt.Chainable (t.leaves.map f))
    (hcompose : Stmt.compose (t.leaves.map f) = some s) :
    s.ctx = (f j).ctx ∧ s.a = (f j).a ∧ s.sa = (f j).sa ∧
      s.e = (f jl).e ∧ s.se = (f jl).se := by
  -- decompose the leaf list as `j :: tail`
  obtain ⟨tail, htail⟩ : ∃ tail, t.leaves = j :: tail := by
    rw [List.head?_eq_some_iff] at hhead
    obtain ⟨tail, htail⟩ := hhead
    exact ⟨tail, htail⟩
  -- restate on the decomposed list
  have hchain' : Stmt.Chainable ((j :: tail).map f) := by rw [← htail]; exact hchain
  have hcompose' : Stmt.compose ((j :: tail).map f) = some s := by
    rw [← htail]; exact hcompose
  have hlast' : (j :: tail).getLast? = some jl := by rw [← htail]; exact hlast
  -- `map` pushes in, and `compose` on a chainable list is `root`
  have hmap : ((j :: tail).map f) = f j :: tail.map f := rfl
  rw [hmap] at hchain' hcompose'
  rw [Stmt.compose_eq_root (f j) (tail.map f) hchain'] at hcompose'
  -- identify the last mapped statement
  have hlastM : ((f j :: tail.map f)).getLast? = some (f jl) := by
    rw [← hmap]
    exact getLast?_map_cons f j tail jl hlast'
  rw [root_cons (f j) (tail.map f) (f jl) hlastM] at hcompose'
  injection hcompose' with heq
  subst heq
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Shape

end ZkFormal.PQ.Aggregation
