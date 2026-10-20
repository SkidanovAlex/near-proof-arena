import NearCompression.GenericLaneBatching
import NearCompression.GenericRSPairRepresentation

/-! Oracle-level semantics of virtual source batching. Source lanes are
arbitrary functions, not assumed to be polynomials or nearby codewords.
The ordered source oracle list and alpha are fixed parameters. Authentication
soundness means binding to THIS list; no Merkle or Fiat--Shamir claim is made.

An explicit batch oracle constrained everywhere to the deterministic batch
is equivalent to the virtual oracle. This is not equivalence to all adversarial
independently committed batch oracles checked only at sampled locations. -/
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def virtualSourceOracle (alpha : K) (sources : List (K → K)) (x : K) : K :=
  lanePowerBatch alpha (sources.map (fun f => f x))

def virtualWidePair (sources : List (K → K)) (x : K) : List (K×K) :=
  sources.map (fun f => (f x,f (-x)))

def virtualCombinePair (alpha : K) (leaf : List (K×K)) : K×K :=
  (lanePowerBatch alpha (leaf.map Prod.fst),lanePowerBatch alpha (leaf.map Prod.snd))

def virtualPairFold (r x : K) (pair : K×K) : K :=
  let eo := rsPairDecode x pair
  eo.1+r*(eo.2-eo.1)

theorem virtual_wide_pair_shape (sources : List (K → K)) (x : K) :
    (virtualWidePair sources x).length=sources.length := by
  simp only [virtualWidePair,List.length_map]

theorem virtual_combined_pair_exact (alpha : K) (sources : List (K → K)) (x : K) :
    virtualCombinePair alpha (virtualWidePair sources x)=
      (virtualSourceOracle alpha sources x,virtualSourceOracle alpha sources (-x)) := by
  simp only [virtualCombinePair,virtualWidePair,virtualSourceOracle,List.map_map,Function.comp_def]

theorem virtual_first_fold_exact (alpha r x : K) (sources : List (K → K)) :
    virtualPairFold r x (virtualCombinePair alpha (virtualWidePair sources x))=
      virtualPairFold r x (virtualSourceOracle alpha sources x,virtualSourceOracle alpha sources (-x)) := by
  rw [virtual_combined_pair_exact]

/-- Exact payload binding, conditional on a fixed authenticated wide oracle.
This is the external contract a Merkle implementation must establish. -/
def VirtualSourceAuthSound (sources : List (K → K))
    (auth : K → List (K×K) → Prop) : Prop :=
  ∀ x leaf, auth x leaf → leaf=virtualWidePair sources x

def VirtualSourceAuthComplete (sources : List (K → K))
    (auth : K → List (K×K) → Prop) : Prop :=
  ∀ x, auth x (virtualWidePair sources x)

/-- Requests contain the canonical source-pair x and the authenticated next
scalar selected by the chain geometry. Next authentication is orthogonal. -/
def VirtualWideChecks (alpha r : K) (auth : K → List (K×K) → Prop)
    (requests : List (K×K)) : Prop :=
  ∀ q ∈ requests, ∃ leaf, auth q.1 leaf ∧ virtualPairFold r q.1 (virtualCombinePair alpha leaf)=q.2

def VirtualOracleChecks (r : K) (oracle : K → K) (requests : List (K×K)) : Prop :=
  ∀ q ∈ requests, virtualPairFold r q.1 (oracle q.1,oracle (-q.1))=q.2

theorem virtual_wide_checks_sound (alpha r : K) (sources : List (K → K))
    (auth : K → List (K×K) → Prop) (sound : VirtualSourceAuthSound sources auth)
    (requests : List (K×K)) (accepted : VirtualWideChecks alpha r auth requests) :
    VirtualOracleChecks r (virtualSourceOracle alpha sources) requests := by
  intro q hq
  obtain ⟨leaf,authenticated,check⟩ := accepted q hq
  rw [sound q.1 leaf authenticated,virtual_first_fold_exact] at check
  exact check

theorem virtual_wide_checks_complete (alpha r : K) (sources : List (K → K))
    (auth : K → List (K×K) → Prop) (complete : VirtualSourceAuthComplete sources auth)
    (requests : List (K×K))
    (accepted : VirtualOracleChecks r (virtualSourceOracle alpha sources) requests) :
    VirtualWideChecks alpha r auth requests := by
  intro q hq
  refine ⟨virtualWidePair sources q.1,complete q.1,?_⟩
  rw [virtual_first_fold_exact]
  exact accepted q hq

theorem virtual_wide_oracle_checks_iff (alpha r : K) (sources : List (K → K))
    (auth : K → List (K×K) → Prop) (sound : VirtualSourceAuthSound sources auth)
    (complete : VirtualSourceAuthComplete sources auth) (requests : List (K×K)) :
    VirtualWideChecks alpha r auth requests ↔
      VirtualOracleChecks r (virtualSourceOracle alpha sources) requests :=
  ⟨virtual_wide_checks_sound alpha r sources auth sound requests,
    virtual_wide_checks_complete alpha r sources auth complete requests⟩

/-- Eliminating an explicit oracle whose ENTIRE function is specified as
the deterministic batch changes no first-chain checks. This is an oracle
semantics lemma, not a computational simulation of a Merkle commitment. -/
theorem virtual_explicit_batch_oracle_iff (alpha r : K) (sources : List (K → K))
    (requests : List (K×K)) :
    (∃ batch : K → K,
      (∀ x, batch x=lanePowerBatch alpha (sources.map (fun f => f x))) ∧
      VirtualOracleChecks r batch requests) ↔
    VirtualOracleChecks r (virtualSourceOracle alpha sources) requests := by
  constructor
  · intro explicit
    obtain ⟨batch,specified,checks⟩ := explicit
    have eq : batch=virtualSourceOracle alpha sources := funext specified
    rw [eq] at checks
    exact checks
  · intro checks
    exact ⟨virtualSourceOracle alpha sources,fun _ => rfl,checks⟩

/-- Direct forward embedding of an accepted implementation transcript into
the deterministic explicit-oracle relation, leaving all later checks intact. -/
theorem virtual_first_chain_embedding (alpha r : K) (sources : List (K → K))
    (auth : K → List (K×K) → Prop) (sound : VirtualSourceAuthSound sources auth)
    (requests : List (K×K)) (laterChecks : Prop)
    (accepted : VirtualWideChecks alpha r auth requests ∧ laterChecks) :
    ∃ batch : K → K,
      (∀ x, batch x=lanePowerBatch alpha (sources.map (fun f => f x))) ∧
      VirtualOracleChecks r batch requests ∧ laterChecks := by
  exact ⟨virtualSourceOracle alpha sources,fun _ => rfl,
    virtual_wide_checks_sound alpha r sources auth sound requests accepted.1,accepted.2⟩

end NearCompression
