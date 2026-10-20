import NearCompression.BackendPersistence

/-! A one-way real-backend invariant, including host error states. -/
namespace NearCompression
open NearSpecV3.Wasm

def hostFinalState {A : Type} : EStateM.Result String St A → St
  | .ok _ s | .error _ s => s

def HostKeepsReal {A : Type} (x : HM A) : Prop :=
  ∀ s, s.real.isSome = true → (hostFinalState (x.run s)).real.isSome = true

theorem host_real_pure {A : Type} (a : A) : HostKeepsReal (pure a) := by
  intro s hs
  exact hs

theorem host_real_throw {A : Type} (message : String) : HostKeepsReal (throw message : HM A) := by
  intro s hs
  exact hs

theorem host_real_bind {A B : Type} (x : HM A) (f : A → HM B)
    (hx : HostKeepsReal x) (hf : ∀ a, HostKeepsReal (f a)) : HostKeepsReal (x >>= f) := by
  intro s hs
  have hp := hx s hs
  rw [NearSpecV3.Logged.W.HM_run_bind]
  cases he : x.run s with
  | ok a u =>
    simp only [he, hostFinalState] at hp
    exact hf a u hp
  | error e u =>
    simp only [he, hostFinalState] at hp
    exact hp

theorem host_real_get_bind {A : Type} (f : St → HM A)
    (hf : ∀ s, s.real.isSome = true → (hostFinalState ((f s).run s)).real.isSome = true) :
    HostKeepsReal (get >>= f) := hf

theorem host_real_modify (f : St → St)
    (hf : ∀ s, s.real.isSome = true → (f s).real.isSome = true) :
    HostKeepsReal (modify f) := hf

theorem host_real_with_gas (f : Gas → Gas × Option String) : HostKeepsReal (withGas f) := by
  unfold withGas
  apply host_real_get_bind
  intro s hs
  dsimp only
  apply host_real_bind
  · apply host_real_modify
    intro u hu
    exact hu
  · intro _
    split
    · exact host_real_throw _
    · exact host_real_pure ()
  · exact hs

theorem host_real_op (r : TTN.RealStore)
    (f : TTN.RealStore → ByteArray → Gas → TTN.Out) (k : ByteArray) :
    HostKeepsReal (realOpH r f k) := by
  unfold realOpH
  apply host_real_get_bind
  intro s hs
  dsimp only
  apply host_real_bind
  · apply host_real_modify
    intro u hu
    rfl
  · intro _
    split
    · exact host_real_throw _
    · exact host_real_pure _
  · exact hs

theorem host_real_put (key : ByteArray) (value : Option ByteArray) :
    HostKeepsReal (realPutH key value) := by
  unfold realPutH
  apply host_real_modify
  intro s hs
  split <;> first | rfl | exact hs

theorem host_real_set (r : TTN.RealStore) (key : ByteArray) (value : Option ByteArray) :
    HostKeepsReal (realSetH r key value) := by
  unfold realSetH
  apply host_real_modify
  intro s hs
  split <;> first | rfl | exact hs

theorem host_real_get (key : ByteArray) : HostKeepsReal (realGetH key) := by
  unfold realGetH
  apply host_real_get_bind
  intro s hs
  repeat' split
  all_goals exact hs

theorem host_real_has (key : ByteArray) : HostKeepsReal (realHasH key) := by
  unfold realHasH
  apply host_real_get_bind
  intro s hs
  repeat' split
  all_goals exact hs

theorem call_host_keeps_real (s : St) (real : s.real.isSome = true) (name : String)
    (hostKeeps : ∀ call, hostCall name = some call → HostKeepsReal call) :
    ResultKeepsBackend s (callHost s name) := by
  unfold callHost
  split
  · trivial
  · cases hs : sync s with
    | error e => trivial
    | ok u =>
      have hu : u.real.isSome = true := by rw [sync_keeps_backend s u hs]; exact real
      cases hc : hostCall name with
      | none => trivial
      | some call =>
        have hp := hostKeeps call hc u hu
        cases hr : call.run u with
        | ok a v =>
          simp only [hr]
          simp only [hr, hostFinalState] at hp
          exact hp.trans real.symm
        | error e v =>
          simp only [hr]
          simp only [hr, hostFinalState] at hp
          split
          · trivial
          · exact hp.trans real.symm

theorem call_func_keeps_real (cfg : NearCfg) (p : Prepared) (s : St)
    (real : s.real.isSome = true) (fi : Nat)
    (hostKeeps : ∀ i (hi : i < p.m.imports.size) call,
      hostCall p.m.imports[i].name = some call → HostKeepsReal call) :
    ResultKeepsBackend s (callFunc cfg p s fi) := by
  unfold callFunc
  split
  · rename_i hi
    exact call_host_keeps_real s real _ (hostKeeps fi hi)
  · exact enter_keeps_backend p s fi

end NearCompression
