import ZkFormal.PQ.Aggregation.Tree

/-!
# ZkFormal.PQ.Aggregation.Statement — the range statement is tree-shape independent

Lane `pq-base-aggregation`. Companion to `DESIGN-BASE.md` §4 (node statement) and §9.1
(`Theorem 7.4-tree`), and to the native `RangeStmt` in
`research/near-compression/native/recursion/patches/openvm-recursion-agg.patch`.

`Tree.lean` proves that the *execution relation* a tree certifies does not depend on the tree's
shape. This file proves the same for the *statement* that aggregation (and the final verifier
`V_d`) checks.

* `Stmt` is the range statement over an abstract boundary alphabet `α`; in deployment `α` is the
  boundary-state encoding and the digest is a fixed function of the statement.
* `Stmt.compose` is the native `RangeStmt::compose`: equal context, index adjacency
  (`b.a = a.e`) and boundary continuity (`b.sa = a.se`).
* `compose_eq_root`: for **any** chainable list, composition returns exactly the root
  `(ctx, first index, last index + 1, first start, last end)`. Tree shape never enters.
* `compose_rejects`: if the list is not chainable, composition is `none`, so `V_d`'s statement
  check fails. Ragged or dropped children cannot produce the claimed root.
* `compose₂_assoc`: composition is associative, so regrouping a tree (`k`-ary to binary) leaves
  the root unchanged.

**Not proved here:** collision resistance of the boundary digest (an assumption, or A-IC as in
`PROOF.md` §1.3), and QROM extraction across nodes (N3/N4).
-/

namespace ZkFormal.PQ.Aggregation

namespace Stmt

/-- A range statement, as in the native `RangeStmt`. -/
structure Stmt (α : Type) where
  /-- chunk context -/
  ctx : α
  /-- first segment index -/
  a : Nat
  /-- exclusive end index -/
  e : Nat
  /-- boundary state encoding at the start -/
  sa : α
  /-- boundary state encoding at the end -/
  se : α

variable {α : Type} [DecidableEq α]

/-- Merge two statements. Only meaningful when they chain. -/
def merge (a b : Stmt α) : Stmt α := ⟨a.ctx, a.a, b.e, a.sa, b.se⟩

@[simp] theorem merge_ctx (a b : Stmt α) : (merge a b).ctx = a.ctx := rfl
@[simp] theorem merge_a (a b : Stmt α) : (merge a b).a = a.a := rfl
@[simp] theorem merge_sa (a b : Stmt α) : (merge a b).sa = a.sa := rfl
@[simp] theorem merge_e (a b : Stmt α) : (merge a b).e = b.e := rfl
@[simp] theorem merge_se (a b : Stmt α) : (merge a b).se = b.se := rfl

/-- Do two statements chain? Same context, contiguous indices, matching boundary. -/
def Chains (a b : Stmt α) : Prop :=
  b.ctx = a.ctx ∧ b.a = a.e ∧ b.sa = a.se

instance chainsDecidable (a b : Stmt α) : Decidable (Chains a b) := by
  unfold Chains; infer_instance

/-- Compose two statements, refusing if they do not chain. -/
def compose₂ (a b : Stmt α) : Option (Stmt α) :=
  if Chains a b then some (merge a b) else none

/-- Compose a list left to right from an accumulator. -/
def composeFrom (acc : Stmt α) : List (Stmt α) → Option (Stmt α)
  | [] => some acc
  | t :: rest => (compose₂ acc t).bind (fun acc' => composeFrom acc' rest)

/-- Compose a list of statements (the native `compose`). -/
def compose : List (Stmt α) → Option (Stmt α)
  | [] => none
  | s :: rest => composeFrom s rest

/-- Adjacent statements chain. -/
def Chainable : List (Stmt α) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Chains a b ∧ Chainable (b :: rest)

/-- The root statement of a list: first statement's context, start index and start boundary;
last statement's end index and end boundary. -/
def root : List (Stmt α) → Option (Stmt α)
  | [] => none
  | s :: rest =>
    let last := rest.getLast?.getD s
    some ⟨s.ctx, s.a, last.e, s.sa, last.se⟩

/-! ## Basics -/

@[simp] theorem composeFrom_nil (acc : Stmt α) : composeFrom acc [] = some acc := rfl

theorem compose_singleton (s : Stmt α) : compose [s] = some s := rfl

theorem compose_nil : compose ([] : List (Stmt α)) = none := rfl

theorem compose₂_eq_some {a b : Stmt α} (h : Chains a b) :
    compose₂ a b = some (merge a b) := by
  unfold compose₂
  rw [if_pos h]

theorem compose₂_eq_none {a b : Stmt α} (h : ¬ Chains a b) : compose₂ a b = none := by
  unfold compose₂
  rw [if_neg h]

/-! ## Composition equals the root -/

/-- If `acc` chains with `t` and the rest chains from `t`, then the merge chains with the rest. -/
theorem chains_merge {acc t u : Stmt α} {rest : List (Stmt α)}
    (h1 : Chains acc t) (h2 : Chainable (t :: u :: rest)) :
    Chainable (merge acc t :: u :: rest) := by
  obtain ⟨hc, ha, hs⟩ := h1
  obtain ⟨⟨hc2, ha2, hs2⟩, htail⟩ := h2
  refine ⟨⟨?_, ?_, ?_⟩, htail⟩
  · rw [merge_ctx]; exact hc2.trans hc
  · rw [merge_e]; exact ha2
  · rw [merge_se]; exact hs2

/-- `composeFrom` on a chainable list returns the root. -/
theorem composeFrom_eq_root (acc : Stmt α) (l : List (Stmt α))
    (h : Chainable (acc :: l)) :
    composeFrom acc l = root (acc :: l) := by
  induction l generalizing acc with
  | nil => simp [root]
  | cons t ts ih =>
    obtain ⟨hpair, hch'⟩ := h
    have hmerge : compose₂ acc t = some (merge acc t) := compose₂_eq_some hpair
    simp only [composeFrom, hmerge, Option.bind_some]
    cases ts with
    | nil => simp [root, merge]
    | cons u us =>
      have hch'' : Chainable (merge acc t :: u :: us) := chains_merge hpair hch'
      rw [ih _ hch'']
      simp [root, merge, List.getLast?_cons]

/-- **Composition returns the root.** For any nonempty chainable list, `compose` is the root
statement. -/
theorem compose_eq_root (s : Stmt α) (rest : List (Stmt α))
    (h : Chainable (s :: rest)) :
    compose (s :: rest) = root (s :: rest) := by
  simp only [compose]
  exact composeFrom_eq_root s rest h

/-! ## Associativity -/

/-- Merging `a, b` then `c` equals merging `a` with the merge of `b, c`. -/
theorem merge_assoc (a b c : Stmt α) :
    merge (merge a b) c = merge a (merge b c) := by
  simp [merge]

/-- **Associativity.** Composition is associative on chainable triples, so regrouping a `k`-ary
node to binary leaves the composed statement unchanged. -/
theorem compose₂_assoc {a b c : Stmt α} (h1 : Chains a b) (h2 : Chains b c) :
    compose₂ (merge a b) c = compose₂ a (merge b c) := by
  obtain ⟨hc1, ha1, hs1⟩ := h1
  obtain ⟨hc2, ha2, hs2⟩ := h2
  have hab : Chains (merge a b) c := by
    refine ⟨?_, ?_, ?_⟩
    · rw [merge_ctx]; exact hc2.trans hc1
    · rw [merge_e]; exact ha2
    · rw [merge_se]; exact hs2
  have hbc : Chains a (merge b c) := ⟨hc1, ha1, hs1⟩
  rw [compose₂_eq_some hab, compose₂_eq_some hbc, merge_assoc]

/-! ## Rejection -/

/-- A merge preserves the left statement's context, so if the merge chains with `c`, then the
original left statement chains with `c`. -/
theorem chains_of_merge_chains {a b c : Stmt α}
    (hab : Chains a b) (hm : Chains (merge a b) c) : Chains b c := by
  obtain ⟨hc, ha, hs⟩ := hab
  obtain ⟨hc₂, ha₂, hs₂⟩ := hm
  refine ⟨?_, ?_, ?_⟩
  · rw [hc₂, merge_ctx, hc]
  · exact ha₂
  · exact hs₂

/-- If `composeFrom` succeeds, the input list is chainable.

Induction on the list, carrying the accumulator. The only work is rewriting `Chains` through the
merge when the tail's head is checked. -/
theorem chainable_of_composeFrom_some (acc : Stmt α) :
    ∀ (l : List (Stmt α)), (∃ r, composeFrom acc l = some r) → Chainable (acc :: l) := by
  intro l
  induction l generalizing acc with
  | nil => intro _; trivial
  | cons t ts ih =>
    intro ⟨r, hcomp⟩
    simp only [composeFrom] at hcomp
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp hcomp
    by_cases hchain : Chains acc t
    · have hcEq : c = merge acc t := by
        rw [compose₂_eq_some hchain] at hc
        exact (Option.some.inj hc).symm
      subst hcEq
      have htail : Chainable (merge acc t :: ts) := ih _ ⟨r, hrest⟩
      cases ts with
      | nil => exact ⟨hchain, trivial⟩
      | cons u us =>
        obtain ⟨hcu, hcu_tail⟩ := htail
        exact ⟨hchain, chains_of_merge_chains hchain hcu, hcu_tail⟩
    · rw [compose₂_eq_none hchain] at hc
      exact absurd hc (by simp)

/-- **Rejection.** If the list is not chainable, composition is `none`. -/
theorem composeFrom_eq_none (acc : Stmt α) (l : List (Stmt α))
    (h : ¬ Chainable (acc :: l)) : composeFrom acc l = none := by
  cases hc : composeFrom acc l with
  | none => rfl
  | some r => exact absurd (chainable_of_composeFrom_some acc l ⟨r, hc⟩) h

/-- **Rejection.** A non-chainable statement list is refused, so `V_d`'s statement check fails. -/
theorem compose_rejects (s : Stmt α) (rest : List (Stmt α))
    (h : ¬ Chainable (s :: rest)) : compose (s :: rest) = none := by
  simp only [compose]
  exact composeFrom_eq_none s rest h

end Stmt

end ZkFormal.PQ.Aggregation
