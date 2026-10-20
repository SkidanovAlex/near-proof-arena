import NearSpecV3.Wasm.Segment

/-!
# ZkFormal.PQ.Aggregation.Tree — arbitrary-shape aggregation over execution segments

Lane `pq-base-aggregation`. Companion to
`research/near-compression/results/pq-base-aggregation/DESIGN-BASE.md` §9.1, which states the
range-statement tree theorem as a sketch (`Theorem 7.4-tree`).

This module proves the **semantic** half: the part independent of the proof system and the QROM.
It answers, for an arbitrary aggregation tree shape, *what the tree certifies* and *whether the
shape matters*.

* `RangeTree` is a finitely branching tree (arbitrary arity, arbitrary depth) whose leaves carry
  segment lengths in interpreter steps.
* `RangeTree.leaves` flattens it to the segment list in execution order.
* `RangeTree.run` executes it: a node runs its children left to right.
* **`run_eq_foldSegments`**: for every tree, the tree's run is the run of its flattened leaf list,
  so shape (arity, depth, grouping) is semantically invisible.
* **`run_node_split`**: any node over `a ++ b` equals the binary grouping
  `node [node a, node b]`, so arbitrary arity normalises to binary without changing the run.
* **`certified_root`**: if each leaf is locally valid and consecutive leaf boundaries agree, the
  whole tree run is the last leaf's result. This is the tree form of
  `NearCompression.exact_chain`.

**Not proved here** (separate obligations, see
`docs/logs/pq-arbitrary-aggregation-proof-obligations-2026-10-19.md`):

* `Theorem 7.4-tree` at the proof-system level: per-node straight-line extraction from one QROM
  database (N3), and error independence from node count (N4).
* Range-digest (tag 9) binding: the `link` relation here is abstract; the in-circuit check is
  collision resistance of the boundary digest.
* Final-layer size independence from the tree (Z4/Z5).
-/

namespace ZkFormal.PQ.Aggregation

open NearSpecV3.Wasm

/-- An aggregation tree over execution segments.

A leaf carries a segment length in interpreter steps. A node carries any finite list of children
applied left to right; the empty node is a no-op and a one-child node is a passthrough. -/
inductive RangeTree where
  /-- Run exactly `steps` interpreter steps. -/
  | leaf (steps : Nat)
  /-- Run the children in order. -/
  | node (children : List RangeTree)

namespace RangeTree

/-- Flatten a tree to its segment lengths, in execution order. -/
def leaves : RangeTree → List Nat
  | .leaf k => [k]
  | .node cs => cs.flatMap leaves

/-- Flatten a list of trees to its segment lengths. -/
def leavesList (cs : List RangeTree) : List Nat := cs.flatMap leaves

/-- Run a tree. A node runs its children left to right from the incoming state. -/
def run (cfg : NearCfg) (p : Prepared) (t : RangeTree) (s : St) : Res :=
  foldSegments cfg p t.leaves s

/-- Number of leaves (segments). -/
def numLeaves : RangeTree → Nat
  | .leaf _ => 1
  | .node cs => (cs.map numLeaves).sum

/-- Total number of interpreter steps covered. -/
def steps : RangeTree → Nat
  | .leaf k => k
  | .node cs => (cs.map steps).sum

/-! ## Basic fold lemmas -/

/-- A one-element `foldSegments` is the segment itself. -/
theorem foldSegments_single (cfg : NearCfg) (p : Prepared) (k : Nat) (s : St) :
    foldSegments cfg p [k] s = seg cfg p k s := by
  simp [foldSegments, Res.bind_cont]

/-- Concatenating leaf lists composes their runs. -/
theorem run_append (cfg : NearCfg) (p : Prepared) (a b : List Nat) (s : St) :
    foldSegments cfg p (a ++ b) s
      = (foldSegments cfg p a s).bind (foldSegments cfg p b) := by
  induction a generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.cons_append, foldSegments]
    rw [Res.bind_assoc]
    congr 1
    funext s'
    exact ih s'

/-- Leaves of a node are the flattened leaves of its children. -/
theorem leaves_node (cs : List RangeTree) :
    (RangeTree.node cs).leaves = leavesList cs := by
  simp [leaves, leavesList]

/-- Leaves of `a ++ b`. -/
theorem leavesList_append (a b : List RangeTree) :
    leavesList (a ++ b) = leavesList a ++ leavesList b := by
  simp [leavesList, List.flatMap_append]

/-- The run of a node is the run of its flattened children. -/
theorem run_node (cfg : NearCfg) (p : Prepared) (cs : List RangeTree) (s : St) :
    (RangeTree.node cs).run cfg p s = foldSegments cfg p (leavesList cs) s := by
  simp [run, leaves_node]

/-! ## Shape independence -/

/-- **Shape independence.** Running any tree equals running its flattened leaf list. The tree's
arity, depth and grouping therefore cannot change what is proven. -/
theorem run_eq_foldSegments (cfg : NearCfg) (p : Prepared) (t : RangeTree) (s : St) :
    t.run cfg p s = foldSegments cfg p t.leaves s := rfl

/-- A node over `a ++ b` runs as `a` then `b`. -/
theorem run_node_append (cfg : NearCfg) (p : Prepared) (a b : List RangeTree) (s : St) :
    (RangeTree.node (a ++ b)).run cfg p s
      = ((RangeTree.node a).run cfg p s).bind (fun s' => (RangeTree.node b).run cfg p s') := by
  simp only [run, leaves_node, leavesList, List.flatMap_append, run_append]

/-- **Regrouping at any node.** A node over `a ++ b` equals the binary node
`node [node a, node b]`. Arbitrary arity normalises to binary without changing the run. -/
theorem run_node_split (cfg : NearCfg) (p : Prepared) (a b : List RangeTree) (s : St) :
    (RangeTree.node (a ++ b)).run cfg p s
      = (RangeTree.node [RangeTree.node a, RangeTree.node b]).run cfg p s := by
  rw [run_node_append]
  simp only [run, leaves, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    run_append]

/-- A one-child node is a passthrough. -/
theorem run_node_single (cfg : NearCfg) (p : Prepared) (t : RangeTree) (s : St) :
    (RangeTree.node [t]).run cfg p s = t.run cfg p s := by
  rw [run_node, run_eq_foldSegments]
  simp [leavesList]

/-- The empty node is a no-op (a single boundary). -/
theorem run_node_nil (cfg : NearCfg) (p : Prepared) (s : St) :
    (RangeTree.node []).run cfg p s = Res.cont s := by
  rw [run_node]
  simp [leavesList, foldSegments]

/-! ## The certified relation -/

/-- A leaf's supplied witness: the segment length, its start state and its result. -/
structure LeafWitness where
  /-- steps this leaf runs -/
  steps : Nat
  /-- start state at the leaf boundary -/
  start : St
  /-- result of running `steps` from `start` -/
  finish : Res

/-- Local validity: the interpreter really maps `start` to `finish`. This is the obligation a base
proof discharges. -/
def LeafValid (cfg : NearCfg) (p : Prepared) (w : LeafWitness) : Prop :=
  seg cfg p w.steps w.start = w.finish

/-- The leaf witnesses agree with a tree's leaf lengths (same order, same step counts). -/
def Matches (t : RangeTree) (ws : List LeafWitness) : Prop :=
  ws.map LeafWitness.steps = t.leaves

/-- Adjacent witnesses are linked at their boundary. The in-circuit check is equality of the
boundary encoding (or of the range digest); this relation is abstract here. -/
def Linked (link : Res → Res → Prop) : List LeafWitness → Prop
  | [] => True
  | [_] => True
  | w :: w' :: rest => link w.finish (.cont w'.start) ∧ Linked link (w' :: rest)

/-- Running a nonempty list of locally valid, consecutively linked witnesses from the first start
reaches the last witness's finish. -/
theorem run_witnesses (cfg : NearCfg) (p : Prepared) (link : Res → Res → Prop)
    (hlinkEq : ∀ a b, link a b → a = b) :
    ∀ (ws : List LeafWitness) (s : St), ws ≠ [] →
      (∀ w ∈ ws, LeafValid cfg p w) → Linked link ws →
      (∀ w, ws.head? = some w → s = w.start) →
      ∃ z, ws.getLast? = some z ∧
        foldSegments cfg p (ws.map LeafWitness.steps) s = z.finish := by
  intro ws
  induction ws with
  | nil => intro s h; exact absurd rfl h
  | cons w rest ih =>
    intro s _ hvalid hlink hstart
    have hw : LeafValid cfg p w := hvalid w (by simp)
    have hs : s = w.start := hstart w List.head?_cons
    cases rest with
    | nil =>
      refine ⟨w, List.getLast?_cons, ?_⟩
      simp only [List.map_cons, List.map_nil]
      rw [foldSegments_single, hs]
      exact hw
    | cons w' rest' =>
      have hlinkFirst : link w.finish (.cont w'.start) := hlink.1
      have hlink' : Linked link (w' :: rest') := hlink.2
      have heq : w.finish = .cont w'.start := hlinkEq _ _ hlinkFirst
      have hvalid' : ∀ x ∈ (w' :: rest'), LeafValid cfg p x :=
        fun x hx => hvalid x (by simp [hx])
      have hne : (w' :: rest') ≠ [] := by simp
      obtain ⟨z, hzlast, hzrun⟩ :=
        ih w'.start hne hvalid' hlink' (fun x hx => by
          rw [List.head?_cons] at hx
          exact (Option.some.inj hx).symm ▸ rfl)
      refine ⟨z, ?_, ?_⟩
      · rw [List.getLast?_cons, hzlast]; rfl
      · simp only [List.map_cons, foldSegments]
        rw [hs, hw, heq, Res.cont_bind]
        exact hzrun

/-- **Tree certified root.** Take any tree `t` and leaf witnesses `ws` matching its step counts. If
each leaf is locally valid and consecutive leaves are linked, running the tree from the first leaf's
start state yields the last leaf's result.

The tree shape enters only through `Matches`; the conclusion is shape-independent, which is what
lets a verifier treat an arbitrary aggregation tree as a flat sequence of segment claims. -/
theorem certified_root (cfg : NearCfg) (p : Prepared) (t : RangeTree) (ws : List LeafWitness)
    (link : Res → Res → Prop) (input : St) (output : Res)
    (hne : ws ≠ [])
    (hmatch : t.Matches ws)
    (hvalid : ∀ w ∈ ws, LeafValid cfg p w)
    (hlink : Linked link ws)
    (hlinkEq : ∀ a b, link a b → a = b)
    (hstart : ∀ w, ws.head? = some w → input = w.start)
    (hout : ∀ w, ws.getLast? = some w → output = w.finish) :
    t.run cfg p input = output := by
  obtain ⟨z, hz, hzrun⟩ := run_witnesses cfg p link hlinkEq ws input hne hvalid hlink hstart
  rw [run_eq_foldSegments, ← hmatch, hzrun, hout z hz]

end RangeTree

end ZkFormal.PQ.Aggregation
