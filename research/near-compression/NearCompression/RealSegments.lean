import NearCompression.RunPersistence

/-! Segment persistence and simulation for the checked real-backend wrapper scope. -/
namespace NearCompression
open NearSpecV3.Wasm

def ResultHasReal : Res → Prop
  | .cont s | .fin s | .abort s _ => s.real.isSome = true
  | .unmodeled _ => True

theorem keeps_backend_has_real (s : St) (r : Res) (real : s.real.isSome = true)
    (keeps : ResultKeepsBackend s r) : ResultHasReal r := by
  cases r <;> simp only [ResultKeepsBackend, ResultHasReal] at keeps ⊢
  all_goals first | exact keeps.trans real | trivial

theorem result_equiv_has_real (a b : Res) (he : ResultEquivalent a b)
    (real : ResultHasReal a) : ResultHasReal b := by
  cases a <;> cases b <;> simp only [ResultEquivalent, ResultHasReal] at he real ⊢
  all_goals first
    | exact (state_equiv_real_is_some _ _ he).symm.trans real
    | exact (state_equiv_real_is_some _ _ he.1).symm.trans real
    | trivial

theorem checked_real_segment_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (n : Nat)
    (s : St) (real : s.real.isSome = true) : ResultKeepsBackend s (seg cfg p n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [seg]
    have hp := checked_real_step_keeps_backend cfg p checked s real
    cases he : step cfg p s with
    | cont u =>
      simp only [he] at hp
      exact result_keeps_backend_trans s u _ hp (ih u (hp.trans real))
    | fin u => simpa only [he, Res.bind] using hp
    | abort u e => simpa only [he, Res.bind] using hp
    | unmodeled e => trivial

theorem checked_real_segment_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (n : Nat)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) :
    ResultEquivalent (seg cfg p n s) (seg cfg p n t) := by
  induction n generalizing s t with
  | zero => exact h
  | succ n ih =>
    simp only [seg]
    apply result_equiv_bind_cont _ _ (checked_real_step_equiv cfg p checked s t h real)
    intro u v hu huv
    have hp := checked_real_step_keeps_backend cfg p checked s real
    exact ih u v huv ((backend_invariant_cont s u _ hp hu).trans real)

theorem checked_real_fold_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (ks : List Nat)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) :
    ResultEquivalent (foldSegments cfg p ks s) (foldSegments cfg p ks t) := by
  rw [foldSegments_eq_seg, foldSegments_eq_seg]
  exact checked_real_segment_equiv cfg p checked _ s t h real

theorem checked_real_observational_chain (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (input : Res) (real : ResultHasReal input)
    (ws : List SegmentWitness) (output : Res)
    (localValid : ∀ w ∈ ws, LocalValid cfg p w)
    (links : ∀ a b, (a, b) ∈ boundaryLinks input ws output → ResultEquivalent a b) :
    ResultEquivalent (input.bind (foldSegments cfg p (ws.map SegmentWitness.steps))) output := by
  induction ws generalizing input with
  | nil =>
    simpa only [List.map_nil, foldSegments, Res.bind_cont] using
      links input output (by simp [boundaryLinks])
  | cons w ws ih =>
    have he := links input (.cont w.start) (by simp [boundaryLinks])
    have startReal : w.start.real.isSome = true := result_equiv_has_real _ _ he real
    have hl := localValid w (by simp)
    have finishReal : ResultHasReal w.finish := by
      rw [← hl]
      exact keeps_backend_has_real _ _ startReal
        (checked_real_segment_keeps_backend cfg p checked _ _ startReal)
    have hb := result_equiv_bind_cont input (.cont w.start) he
      (foldSegments cfg p ((w :: ws).map SegmentWitness.steps))
      (foldSegments cfg p ((w :: ws).map SegmentWitness.steps))
      (fun s t hs hst => checked_real_fold_equiv cfg p checked _ s t hst
        (by simpa only [hs, ResultHasReal] using real))
    simp only [Res.cont_bind, List.map_cons, foldSegments,
      show seg cfg p w.steps w.start = w.finish from hl] at hb
    apply result_equiv_trans _ _ _ hb
    apply ih w.finish finishReal
    · intro x hx; exact localValid x (by simp [hx])
    · intro a b hab; exact links a b (by simp [boundaryLinks, hab])

theorem checked_real_chain_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (program : Prepared) (checked : checkRealWrapperImports program = true)
    (input : Res) (real : ResultHasReal input) (ws : List SegmentWitness) (output : Res)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg program input ws output)
    (roundtrip : ObservedBoundaryDecodes encode decode input ws output) :
    ResultEquivalent (input.bind (foldSegments cfg program (ws.map SegmentWitness.steps))) output ∨
      ∃ a b, (a, b) ∈ boundaryLinks input ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  classical
  by_cases he : ∀ a b, (a, b) ∈ boundaryLinks input ws output → ResultEquivalent a b
  · exact Or.inl (checked_real_observational_chain cfg program checked input real ws output cert.1 he)
  · apply Or.inr
    simp only [Classical.not_forall] at he
    obtain ⟨a, b, hab, hne⟩ := he
    refine ⟨a, b, hab, ?_, cert.2 a b hab⟩
    intro same
    exact hne (observational_encoding_alias encode decode a b
      (roundtrip a b hab).1 (roundtrip a b hab).2 same)

theorem checked_real_run_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (p : Prepared) (checked : checkRealWrapperImports p = true)
    (start : St) (real : start.real.isSome = true)
    (ws : List SegmentWitness) (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg p (.cont start) ws output)
    (roundtrip : ObservedBoundaryDecodes encode decode (.cont start) ws output) :
    ResultEquivalent (run cfg p ((ws.map SegmentWitness.steps).sum + remainingFuel) start)
        (output.bind (run cfg p remainingFuel)) ∨
      ∃ a b, (a, b) ∈ boundaryLinks (.cont start) ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) := by
  rcases checked_real_chain_or_hash_collision hash encode decode cfg p checked
    (.cont start) real ws output cert roundtrip with he | hc
  · apply Or.inl
    rw [run_foldSegments]
    simp only [Res.cont_bind] at he
    apply result_equiv_bind_cont _ _ he
    intro u v hu huv
    have hp : ResultKeepsBackend start (foldSegments cfg p (ws.map SegmentWitness.steps) start) := by
      rw [foldSegments_eq_seg]
      exact checked_real_segment_keeps_backend cfg p checked _ start real
    exact checked_real_run_equiv cfg p checked remainingFuel u v huv
      ((backend_invariant_cont start u _ hp hu).trans real)
  · exact Or.inr hc

end NearCompression
