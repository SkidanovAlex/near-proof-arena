import NearSpecV3.Wasm.Segment

/-!
Commitment-linked execution segments against the ACTUAL NearSpecV3 interpreter.
This is a semantic reduction, not a recursive proof-system security theorem.
Each local segment equation must eventually be obtained from an AIR/IOP proof.
No global injectivity of a finite hash is assumed. A failed composition exposes
a collision at an actual checked boundary (including terminal result tags).
-/
namespace NearCompression
open NearSpecV3.Wasm

structure SegmentWitness where
  steps : Nat
  start : St
  finish : Res

def LocalValid (cfg : NearCfg) (program : Prepared) (w : SegmentWitness) : Prop :=
  seg cfg program w.steps w.start = w.finish

/-- Include the initial boundary, all intermediate boundaries and final output.
The result tag is part of the bound object: a return/abort cannot become a
continuation merely because its state fields match. -/
def boundaryLinks : Res → List SegmentWitness → Res → List (Res × Res)
  | input, [], output => [(input, output)]
  | input, w :: ws, output =>
    (input, .cont w.start) :: boundaryLinks w.finish ws output

def CertifiedChain {Digest : Type} (commit : Res → Digest)
    (cfg : NearCfg) (program : Prepared) (input : Res)
    (ws : List SegmentWitness) (output : Res) : Prop :=
  (∀ w ∈ ws, LocalValid cfg program w) ∧
  ∀ a b, (a, b) ∈ boundaryLinks input ws output → commit a = commit b

/-- Only collisions in the finite supplied boundary list count in this theorem.
It does not appeal to the unavoidable existence of collisions somewhere in an
unbounded state space. -/
def BoundaryCollision {Digest : Type} (commit : Res → Digest)
    (input : Res) (ws : List SegmentWitness) (output : Res) : Prop :=
  ∃ a b, (a, b) ∈ boundaryLinks input ws output ∧ a ≠ b ∧ commit a = commit b

theorem boundaryLinks_length (input : Res) (ws : List SegmentWitness) (output : Res) :
    (boundaryLinks input ws output).length = ws.length + 1 := by
  induction ws generalizing input with
  | nil => rfl
  | cons w ws ih => simp [boundaryLinks, ih, Nat.add_assoc]

/-- Exact state linking composes local execution, including early termination. -/
theorem exact_chain (cfg : NearCfg) (program : Prepared) (input : Res)
    (ws : List SegmentWitness) (output : Res)
    (localValid : ∀ w ∈ ws, LocalValid cfg program w)
    (links : ∀ a b, (a, b) ∈ boundaryLinks input ws output → a = b) :
    input.bind (foldSegments cfg program (ws.map SegmentWitness.steps)) = output := by
  induction ws generalizing input with
  | nil =>
    have he := links input output (by simp [boundaryLinks])
    simpa only [List.map_nil, foldSegments, Res.bind_cont] using he
  | cons w ws ih =>
    have he := links input (.cont w.start) (by simp [boundaryLinks])
    have hl := localValid w (by simp)
    rw [he]
    simp only [Res.cont_bind, List.map_cons, foldSegments]
    rw [show seg cfg program w.steps w.start = w.finish from hl]
    apply ih w.finish
    · intro x hx
      exact localValid x (by simp [hx])
    · intro a b hab
      exact links a b (by simp [boundaryLinks, hab])

/-- Either the actual segmented interpreter reaches the certified result, or
one of the supplied boundary pairs is an explicit commitment collision. -/
theorem certified_chain_or_collision {Digest : Type} (commit : Res → Digest)
    (cfg : NearCfg) (program : Prepared) (input : Res)
    (ws : List SegmentWitness) (output : Res)
    (cert : CertifiedChain commit cfg program input ws output) :
    input.bind (foldSegments cfg program (ws.map SegmentWitness.steps)) = output ∨
      BoundaryCollision commit input ws output := by
  classical
  by_cases he : ∀ a b, (a, b) ∈ boundaryLinks input ws output → a = b
  · exact Or.inl (exact_chain cfg program input ws output cert.1 he)
  · apply Or.inr
    simp only [Classical.not_forall] at he
    obtain ⟨a, b, hab, hne⟩ := he
    exact ⟨a, b, hab, hne, cert.2 a b hab⟩

/-- Connection to the existing fuel-bounded run, rather than only an abstract
transition relation. The suffix is necessary: run 0 is fuel exhaustion, whereas
a zero-length segment returns a continuation. -/
theorem certified_run_or_collision {Digest : Type} (commit : Res → Digest)
    (cfg : NearCfg) (program : Prepared) (start : St)
    (ws : List SegmentWitness) (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain commit cfg program (.cont start) ws output) :
    run cfg program ((ws.map SegmentWitness.steps).sum + remainingFuel) start =
        output.bind (run cfg program remainingFuel) ∨
      BoundaryCollision commit (.cont start) ws output := by
  rcases certified_chain_or_collision commit cfg program (.cont start) ws output cert with h | h
  · apply Or.inl
    rw [run_foldSegments]
    simpa only [Res.cont_bind] using congrArg (fun r => r.bind (run cfg program remainingFuel)) h
  · exact Or.inr h

/-- Final results must remain terminal; matching only the stored state would
permit an invalid resume after return. -/
theorem terminal_tag_matters {Digest : Type} (commit : Res → Digest) (s : St)
    (h : commit (.fin s) = commit (.cont s)) :
    BoundaryCollision commit (.fin s) [⟨0, s, .cont s⟩] (.cont s) := by
  refine ⟨.fin s, .cont s, ?_, ?_, h⟩
  · simp [boundaryLinks]
  · intro he
    cases he

/-- Only the finite states actually used at boundaries need a round-trip
encoding. This is deliberately NOT an injectivity assumption on all St: St
contains a function-valued backing store. A concrete implementation must supply
a finite store representation and prove this reconstruction property. -/
def BoundaryDecodes (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (input : Res) (ws : List SegmentWitness) (output : Res) : Prop :=
  ∀ a b, (a, b) ∈ boundaryLinks input ws output →
    decode (encode a) = some a ∧ decode (encode b) = some b

/-- The collision is now on distinct BYTE STRINGS, not merely distinct machine
states that an incomplete encoder might map to the same bytes. -/
theorem boundary_collision_to_hash {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (input : Res) (ws : List SegmentWitness) (output : Res)
    (roundtrip : BoundaryDecodes encode decode input ws output)
    (collision : BoundaryCollision (fun r => hash (encode r)) input ws output) :
    ∃ a b, (a, b) ∈ boundaryLinks input ws output ∧
      encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  obtain ⟨a, b, hab, hne, hh⟩ := collision
  refine ⟨a, b, hab, ?_, hh⟩
  intro he
  have hd := congrArg decode he
  rw [(roundtrip a b hab).1, (roundtrip a b hab).2] at hd
  exact hne (Option.some.inj hd)

/-- End-to-end semantic statement for hash-linked execution segments. Local
segment validity, finite-state encoding and extraction of these witnesses are
still obligations for a cryptographic compressor, not facts asserted here. -/
theorem certified_run_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (program : Prepared) (start : St)
    (ws : List SegmentWitness) (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg program (.cont start) ws output)
    (roundtrip : BoundaryDecodes encode decode (.cont start) ws output) :
    run cfg program ((ws.map SegmentWitness.steps).sum + remainingFuel) start =
        output.bind (run cfg program remainingFuel) ∨
      ∃ a b, (a, b) ∈ boundaryLinks (.cont start) ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  rcases certified_run_or_collision (fun r => hash (encode r)) cfg program start
      ws output remainingFuel cert with he | hc
  · exact Or.inl he
  · exact Or.inr (boundary_collision_to_hash hash encode decode _ _ _ roundtrip hc)

/-- Omitting the terminal tag cannot satisfy even a two-state round trip. -/
theorem erased_tag_cannot_decode (encode : Res → List UInt8)
    (decode : List UInt8 → Option Res) (s : St)
    (he : encode (.fin s) = encode (.cont s))
    (hf : decode (encode (.fin s)) = some (.fin s))
    (hc : decode (encode (.cont s)) = some (.cont s)) : False := by
  have hd := congrArg decode he
  rw [hf, hc] at hd
  cases Option.some.inj hd

end NearCompression
