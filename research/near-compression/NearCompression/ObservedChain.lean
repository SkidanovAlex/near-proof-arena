import NearCompression.Observational
import NearCompression.Segments

/-! Hash-linked composition with observational decoding. These results retain
explicit whole-step simulation and codec premises; neither is implemented here.
The conclusion exposes collisions on actual distinct encoded boundary bytes. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem observational_chain (cfg : NearCfg) (program : Prepared)
    (stepSim : StepPreservesMaps cfg program) (input : Res)
    (ws : List SegmentWitness) (output : Res)
    (localValid : ∀ w ∈ ws, LocalValid cfg program w)
    (links : ∀ a b, (a, b) ∈ boundaryLinks input ws output → ResultEquivalent a b) :
    ResultEquivalent (input.bind (foldSegments cfg program (ws.map SegmentWitness.steps))) output := by
  induction ws generalizing input with
  | nil =>
    simpa only [List.map_nil, foldSegments, Res.bind_cont] using
      links input output (by simp [boundaryLinks])
  | cons w ws ih =>
    have he := links input (.cont w.start) (by simp [boundaryLinks])
    have hl := localValid w (by simp)
    have hb := result_equiv_bind input (.cont w.start) he
      (foldSegments cfg program ((w :: ws).map SegmentWitness.steps))
      (foldSegments cfg program ((w :: ws).map SegmentWitness.steps))
      (fold_equiv_of_step cfg program stepSim _)
    simp only [Res.cont_bind, List.map_cons, foldSegments,
      show seg cfg program w.steps w.start = w.finish from hl] at hb
    apply result_equiv_trans _ _ _ hb
    apply ih w.finish
    · intro x hx
      exact localValid x (by simp [hx])
    · intro a b hab
      exact links a b (by simp [boundaryLinks, hab])

/-- Decoding may rebuild map buckets, but must preserve every observable field. -/
def ObservedDecodes (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (r : Res) : Prop :=
  ∃ decoded, decode (encode r) = some decoded ∧ ResultEquivalent r decoded

def ObservedBoundaryDecodes (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (input : Res) (ws : List SegmentWitness) (output : Res) : Prop :=
  ∀ a b, (a, b) ∈ boundaryLinks input ws output →
    ObservedDecodes encode decode a ∧ ObservedDecodes encode decode b

theorem observational_encoding_alias (encode : Res → List UInt8)
    (decode : List UInt8 → Option Res) (a b : Res)
    (ha : ObservedDecodes encode decode a) (hb : ObservedDecodes encode decode b)
    (same : encode a = encode b) : ResultEquivalent a b := by
  obtain ⟨da, hda, hea⟩ := ha
  obtain ⟨db, hdb, heb⟩ := hb
  have hd := congrArg decode same
  rw [hda, hdb] at hd
  have he := Option.some.inj hd
  subst db
  exact result_equiv_trans _ _ _ hea (result_equiv_symm _ _ heb)

theorem observational_chain_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (program : Prepared) (stepSim : StepPreservesMaps cfg program)
    (input : Res) (ws : List SegmentWitness) (output : Res)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg program input ws output)
    (roundtrip : ObservedBoundaryDecodes encode decode input ws output) :
    ResultEquivalent (input.bind (foldSegments cfg program (ws.map SegmentWitness.steps))) output ∨
      ∃ a b, (a, b) ∈ boundaryLinks input ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  classical
  by_cases he : ∀ a b, (a, b) ∈ boundaryLinks input ws output → ResultEquivalent a b
  · exact Or.inl (observational_chain cfg program stepSim input ws output cert.1 he)
  · apply Or.inr
    simp only [Classical.not_forall] at he
    obtain ⟨a, b, hab, hne⟩ := he
    refine ⟨a, b, hab, ?_, cert.2 a b hab⟩
    intro same
    exact hne (observational_encoding_alias encode decode a b
      (roundtrip a b hab).1 (roundtrip a b hab).2 same)

theorem observational_run_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (program : Prepared) (stepSim : StepPreservesMaps cfg program)
    (start : St) (ws : List SegmentWitness) (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg program (.cont start) ws output)
    (roundtrip : ObservedBoundaryDecodes encode decode (.cont start) ws output) :
    ResultEquivalent (run cfg program ((ws.map SegmentWitness.steps).sum + remainingFuel) start)
        (output.bind (run cfg program remainingFuel)) ∨
      ∃ a b, (a, b) ∈ boundaryLinks (.cont start) ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  rcases observational_chain_or_hash_collision hash encode decode cfg program stepSim
    (.cont start) ws output cert roundtrip with he | hc
  · apply Or.inl
    rw [run_foldSegments]
    simp only [Res.cont_bind] at he
    exact result_equiv_bind _ _ he _ _ (run_equiv_of_step cfg program stepSim remainingFuel)
  · exact Or.inr hc

end NearCompression
