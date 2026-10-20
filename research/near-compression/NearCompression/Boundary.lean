import NearCompression.Segments
import NearCompression.Scope
import NearSpecV3.Logged.WasmRun

/-!
Finite boundary DATA representation for the actual interpreter. It eliminates
only the function-valued backing-store field, which is supplied by one immutable
context. No memory, gas, host or terminal fields are omitted. HashMaps remain
finite data structures; a canonical byte codec and authenticated-memory layout
are separate obligations. This is not yet a compact boundary commitment.
-/
namespace NearCompression
open NearSpecV3.Wasm

structure RealBoundary where
  root : ByteArray
  overlay : Std.HashMap ByteArray (Option ByteArray)
  acct : TTN.Acct
  pfx : ByteArray
  recd : TTN.Recorder
  recBefore : Nat
  writes : Array (ByteArray × Option ByteArray)

def captureReal (r : TTN.RealStore) : RealBoundary :=
  ⟨r.root, r.overlay, r.acct, r.pfx, r.recd, r.recBefore, r.writes⟩

def restoreReal (store : TTN.Store) (r : RealBoundary) : TTN.RealStore :=
  ⟨store, r.root, r.overlay, r.acct, r.pfx, r.recd, r.recBefore, r.writes⟩

structure StateBoundary where
  stack : Array Val
  frames : List Frame
  pages : Array ByteArray
  globals : Array Val
  table : Array (Option Nat)
  tableMax : Nat
  elems : Array (Array (Option Nat))
  datas : Array ByteArray
  stackRem : Nat
  gas : Gas
  ctx : CallCtx
  ret : Option (ByteArray ⊕ Nat)
  balance : Nat
  storageUsage : Nat
  registers : Array (Nat × ByteArray)
  regUsage : Nat
  logs : Array ByteArray
  totalLogLen : Nat
  promises : Array PromiseV
  trie : Array (ByteArray × ByteArray)
  actions : Array MAct
  dataCount : Nat
  real : Option RealBoundary
  subsidized : Nat

def captureState (s : St) : StateBoundary where
  stack := s.stack
  frames := s.frames
  pages := s.pages
  globals := s.globals
  table := s.table
  tableMax := s.tableMax
  elems := s.elems
  datas := s.datas
  stackRem := s.stackRem
  gas := s.gas
  ctx := s.ctx
  ret := s.ret
  balance := s.balance
  storageUsage := s.storageUsage
  registers := s.registers
  regUsage := s.regUsage
  logs := s.logs
  totalLogLen := s.totalLogLen
  promises := s.promises
  trie := s.trie
  actions := s.actions
  dataCount := s.dataCount
  real := s.real.map captureReal
  subsidized := s.subsidized

def restoreState (store : TTN.Store) (s : StateBoundary) : St where
  stack := s.stack
  frames := s.frames
  pages := s.pages
  globals := s.globals
  table := s.table
  tableMax := s.tableMax
  elems := s.elems
  datas := s.datas
  stackRem := s.stackRem
  gas := s.gas
  ctx := s.ctx
  ret := s.ret
  balance := s.balance
  storageUsage := s.storageUsage
  registers := s.registers
  regUsage := s.regUsage
  logs := s.logs
  totalLogLen := s.totalLogLen
  promises := s.promises
  trie := s.trie
  actions := s.actions
  dataCount := s.dataCount
  real := s.real.map (restoreReal store)
  subsidized := s.subsidized

/-- Terminal status and abort/unmodeled details are explicitly represented. -/
inductive ResultBoundary where
  | cont (s : StateBoundary)
  | fin (s : StateBoundary)
  | abort (s : StateBoundary) (error : String)
  | unmodeled (reason : String)

def captureResult : Res → ResultBoundary
  | .cont s => .cont (captureState s)
  | .fin s => .fin (captureState s)
  | .abort s e => .abort (captureState s) e
  | .unmodeled e => .unmodeled e

def restoreResult (store : TTN.Store) : ResultBoundary → Res
  | .cont s => .cont (restoreState store s)
  | .fin s => .fin (restoreState store s)
  | .abort s e => .abort (restoreState store s) e
  | .unmodeled e => .unmodeled e

/-- Reuses the exact finite HStore lookup used by D3.functionCall. It does not
switch to a different map/deduplication policy or assume hash injectivity. -/
def boundaryStore (store : NearSpecV3.D2.HStore) : TTN.Store :=
  fun h => (NearSpecV3.D2.hGet store h.toList).map NearSpecV3.D3.toBA

structure ExecutionContext where
  cfg : NearCfg
  program : Prepared
  backing : NearSpecV3.D2.HStore

theorem capture_restore_real (store : TTN.Store) (r : RealBoundary) :
    captureReal (restoreReal store r) = r := by cases r; rfl

theorem restore_capture_state (store : TTN.Store) (s : St) :
    restoreState store (captureState s) = NearSpecV3.Logged.W.E store s := by
  cases s
  simp only [restoreState, captureState, NearSpecV3.Logged.W.E, Option.map_map,
    Function.comp_def]
  rfl

theorem capture_restore_state (store : TTN.Store) (s : StateBoundary) :
    captureState (restoreState store s) = s := by
  cases s
  simp only [restoreState, captureState, Option.map_map, Function.comp_def,
    capture_restore_real, Option.map_id']

theorem restored_state_backed (store : TTN.Store) (s : StateBoundary) :
    NearSpecV3.Logged.W.StOK store (restoreState store s) := by
  intro r hr
  simp only [restoreState] at hr
  cases hs : s.real with
  | none => simp [hs] at hr
  | some b =>
    simp only [hs, Option.map_some, Option.some.injEq] at hr
    rw [← hr]
    rfl

theorem backed_state_roundtrip (store : TTN.Store) (s : St)
    (h : NearSpecV3.Logged.W.StOK store s) : restoreState store (captureState s) = s := by
  rw [restore_capture_state]
  exact NearSpecV3.Logged.W.E_of_StOK h

theorem capture_restore_result (store : TTN.Store) (r : ResultBoundary) :
    captureResult (restoreResult store r) = r := by
  cases r <;> simp only [restoreResult, captureResult, capture_restore_state]

theorem restore_capture_result (store : TTN.Store) (r : Res) :
    restoreResult store (captureResult r) =
      NearSpecV3.Logged.W.mapRes (NearSpecV3.Logged.W.E store) r := by
  cases r <;> simp only [restoreResult, captureResult, restore_capture_state,
    NearSpecV3.Logged.W.mapRes]

theorem backed_result_roundtrip (store : TTN.Store) (r : Res)
    (h : NearSpecV3.Logged.W.ResOK store r) : restoreResult store (captureResult r) = r := by
  rw [restore_capture_result]
  exact h

/-- Same captured data under one backing context implies the same full state.
Changing the backing context invalidates the premise; it must be bound once. -/
theorem capture_state_injective_on_backed (store : TTN.Store) (s t : St)
    (hs : NearSpecV3.Logged.W.StOK store s) (ht : NearSpecV3.Logged.W.StOK store t)
    (he : captureState s = captureState t) : s = t := by
  have h := congrArg (restoreState store) he
  simpa only [backed_state_roundtrip store s hs, backed_state_roundtrip store t ht] using h

theorem boundary_store_agrees (store : NearSpecV3.D2.HStore) :
    TTN.StoreAgrees (boundaryStore store) (NearSpecV3.D2.hGet store) := by
  intro h
  rfl

/-- Even storage-host steps retain the immutable backing store. Their overlay,
recorder and accounting state may change and remain in the captured data. -/
theorem step_preserves_backing (store : NearSpecV3.D2.HStore)
    (cfg : NearCfg) (p : Prepared) (s : St)
    (hs : NearSpecV3.Logged.W.StOK (boundaryStore store) s) :
    NearSpecV3.Logged.W.ResOK (boundaryStore store) (step cfg p s) := by
  let σ := boundaryStore store
  cases hsp : NearSpecV3.Logged.W.stepPre p s with
  | none =>
    have he := NearSpecV3.Logged.W.E_step (σ := σ) cfg p hsp
    rw [NearSpecV3.Logged.W.E_of_StOK hs] at he
    exact he.symm
  | some q =>
    obtain ⟨s1, name⟩ := q
    have he := @NearSpecV3.Logged.W.E_stepPre σ s p
    rw [NearSpecV3.Logged.W.E_of_StOK hs, hsp] at he
    simp only [Option.map_some] at he
    have hs1 : s1 = NearSpecV3.Logged.W.E σ s1 := by
      injection he with he
      injection he
    have hb : NearSpecV3.Logged.W.StOK σ s1 := by
      rw [hs1]
      exact NearSpecV3.Logged.W.StOK_E _
    rw [NearSpecV3.Logged.W.step_of_stepPre cfg p s s1 name hsp]
    exact (NearSpecV3.Logged.W.callHostL_spec (boundary_store_agrees store) hb name
      (NearSpecV3.Logged.W.stepPre_storage hsp)).2

theorem segment_preserves_backing (store : NearSpecV3.D2.HStore)
    (cfg : NearCfg) (p : Prepared) (n : Nat) (s : St)
    (hs : NearSpecV3.Logged.W.StOK (boundaryStore store) s) :
    NearSpecV3.Logged.W.ResOK (boundaryStore store) (seg cfg p n s) := by
  induction n generalizing s with
  | zero =>
    show Res.cont (NearSpecV3.Logged.W.E (boundaryStore store) s) = .cont s
    rw [NearSpecV3.Logged.W.E_of_StOK hs]
  | succ n ih =>
    have hp := step_preserves_backing store cfg p s hs
    cases hr : step cfg p s with
    | cont s' =>
      simpa only [seg, hr, Res.cont_bind] using
        ih s' (NearSpecV3.Logged.W.ResOK_cont hp hr)
    | fin s' => simpa only [seg, hr, Res.bind] using hp
    | abort s' e => simpa only [seg, hr, Res.bind] using hp
    | unmodeled e => simpa only [seg, hr, Res.bind] using hp

/-- Executable finite-data segment runner using the SAME interpreter. This is
the representation reference, not an optimized prover or succinct certificate. -/
def finiteSegment (context : ExecutionContext) (steps : Nat) (s : StateBoundary) : ResultBoundary :=
  captureResult (seg context.cfg context.program steps
    (restoreState (boundaryStore context.backing) s))

/-- No caller-supplied preservation premise: it is discharged for every segment
length and every finite boundary by the actual storage-host proofs above. -/
theorem finite_segment_correct (context : ExecutionContext) (steps : Nat) (s : StateBoundary) :
    restoreResult (boundaryStore context.backing) (finiteSegment context steps s) =
      seg context.cfg context.program steps (restoreState (boundaryStore context.backing) s) := by
  apply backed_result_roundtrip
  exact segment_preserves_backing context.backing context.cfg context.program steps _
    (restored_state_backed _ _)

theorem restore_result_injective (store : TTN.Store) (a b : ResultBoundary)
    (h : restoreResult store a = restoreResult store b) : a = b := by
  have he := congrArg captureResult h
  simpa only [capture_restore_result] using he

/-- A shared context is a necessary part of the statement, not an optional
optimization. Identical boundary data can mean different full machine states
when its external store is changed. -/
theorem different_backing_changes_state (σ τ : TTN.Store) (s : StateBoundary)
    (r : RealBoundary) (hr : s.real = some r) (key : ByteArray)
    (hne : σ key ≠ τ key) : restoreState σ s ≠ restoreState τ s := by
  intro he
  have hreal := congrArg St.real he
  simp only [restoreState, hr, Option.map_some, Option.some.injEq] at hreal
  have hh := congrArg (fun r : TTN.RealStore => r.store key) hreal
  exact hne hh

def ResultBoundary.bind (r : ResultBoundary) (f : StateBoundary → ResultBoundary) : ResultBoundary :=
  match r with
  | .cont s => f s
  | r => r

def finiteFold (context : ExecutionContext) : List Nat → StateBoundary → ResultBoundary
  | [], s => .cont s
  | k :: ks, s => (finiteSegment context k s).bind (finiteFold context ks)

/-- Exact segmentation on finite data, including early return, abort and
unmodeled results. No bound on the number of segments is imposed. -/
theorem finite_fold_correct (context : ExecutionContext) (ks : List Nat) (s : StateBoundary) :
    restoreResult (boundaryStore context.backing) (finiteFold context ks s) =
      foldSegments context.cfg context.program ks (restoreState (boundaryStore context.backing) s) := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [finiteFold, foldSegments]
    rw [← finite_segment_correct]
    cases hr : finiteSegment context k s with
    | cont s' => exact ih s'
    | fin s' => rfl
    | abort s' e => rfl
    | unmodeled e => rfl

/-- The actual original run equals the restored finite-data segment execution,
followed by the same remaining fuel. This closes the representation/segmentation
bridge without assuming a serializer, hash binding, or local trace validity. -/
theorem finite_run_correct (context : ExecutionContext) (ks : List Nat)
    (s : StateBoundary) (remainingFuel : Nat) :
    run context.cfg context.program (ks.sum + remainingFuel)
        (restoreState (boundaryStore context.backing) s) =
      (restoreResult (boundaryStore context.backing) (finiteFold context ks s)).bind
        (run context.cfg context.program remainingFuel) := by
  rw [finite_fold_correct, run_foldSegments]

/-- Every linked endpoint is backed by the fixed context when segment starts
and the public endpoints are backed. Segment finishes need no extra premise:
local execution validity and the storage preservation theorem imply it. -/
theorem boundary_links_backed (context : ExecutionContext) (input output : Res)
    (ws : List SegmentWitness)
    (hi : NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) input)
    (ho : NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) output)
    (hs : ∀ w ∈ ws, NearSpecV3.Logged.W.StOK (boundaryStore context.backing) w.start)
    (hv : ∀ w ∈ ws, LocalValid context.cfg context.program w) :
    ∀ a b, (a, b) ∈ boundaryLinks input ws output →
      NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) a ∧
      NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) b := by
  induction ws generalizing input with
  | nil =>
    intro a b hab
    simp only [boundaryLinks, List.mem_singleton, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    exact ⟨hi, ho⟩
  | cons w ws ih =>
    have hw := hs w (by simp)
    have hf : NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) w.finish := by
      rw [← hv w (by simp)]
      exact segment_preserves_backing _ _ _ _ _ hw
    intro a b hab
    simp only [boundaryLinks, List.mem_cons] at hab
    rcases hab with he | ht
    · cases he
      refine ⟨hi, ?_⟩
      change Res.cont (NearSpecV3.Logged.W.E _ w.start) = Res.cont w.start
      rw [NearSpecV3.Logged.W.E_of_StOK hw]
    · exact ih w.finish hf (fun x hx => hs x (by simp [hx]))
        (fun x hx => hv x (by simp [hx])) a b ht

/-- A finite-data codec lifts to a full-state codec under the fixed backing
context. The byte-codec premise is explicit; no serializer is invented here. -/
theorem finite_codec_roundtrip (store : TTN.Store)
    (encode : ResultBoundary → List UInt8)
    (decode : List UInt8 → Option ResultBoundary)
    (codec : ∀ r, decode (encode r) = some r)
    (r : Res) (hr : NearSpecV3.Logged.W.ResOK store r) :
    (decode (encode (captureResult r))).map (restoreResult store) = some r := by
  rw [codec, Option.map_some, backed_result_roundtrip store r hr]

/-- This discharges the old full-state decoding hypothesis using a finite-data
codec and backing invariants proved for the real interpreter. -/
theorem finite_codec_boundary_decodes (context : ExecutionContext)
    (encode : ResultBoundary → List UInt8)
    (decode : List UInt8 → Option ResultBoundary)
    (codec : ∀ r, decode (encode r) = some r)
    (input output : Res) (ws : List SegmentWitness)
    (hi : NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) input)
    (ho : NearSpecV3.Logged.W.ResOK (boundaryStore context.backing) output)
    (hs : ∀ w ∈ ws, NearSpecV3.Logged.W.StOK (boundaryStore context.backing) w.start)
    (hv : ∀ w ∈ ws, LocalValid context.cfg context.program w) :
    BoundaryDecodes (fun r => encode (captureResult r))
      (fun bytes => (decode bytes).map (restoreResult (boundaryStore context.backing)))
      input ws output := by
  intro a b hab
  obtain ⟨ha, hb⟩ := boundary_links_backed context input output ws hi ho hs hv a b hab
  exact ⟨finite_codec_roundtrip _ encode decode codec a ha,
    finite_codec_roundtrip _ encode decode codec b hb⟩

/-- Concrete fixed-context version of the hash-linked execution reduction.
All serialized objects are finite boundary data. Local validity and the byte
codec still require implementations; cryptographic extraction is not assumed
proved by this deterministic theorem. -/
theorem finite_certified_run_or_hash_collision {Digest : Type}
    (context : ExecutionContext) (hash : List UInt8 → Digest)
    (encode : ResultBoundary → List UInt8)
    (decode : List UInt8 → Option ResultBoundary)
    (codec : ∀ r, decode (encode r) = some r)
    (start : StateBoundary) (ws : List SegmentWitness) (output : ResultBoundary)
    (remainingFuel : Nat)
    (hs : ∀ w ∈ ws, NearSpecV3.Logged.W.StOK (boundaryStore context.backing) w.start)
    (cert : CertifiedChain (fun r => hash (encode (captureResult r)))
      context.cfg context.program (.cont (restoreState (boundaryStore context.backing) start))
      ws (restoreResult (boundaryStore context.backing) output)) :
    run context.cfg context.program ((ws.map SegmentWitness.steps).sum + remainingFuel)
        (restoreState (boundaryStore context.backing) start) =
      (restoreResult (boundaryStore context.backing) output).bind
        (run context.cfg context.program remainingFuel) ∨
    ∃ a b, (a, b) ∈ boundaryLinks
        (.cont (restoreState (boundaryStore context.backing) start)) ws
        (restoreResult (boundaryStore context.backing) output) ∧
      encode (captureResult a) ≠ encode (captureResult b) ∧
      hash (encode (captureResult a)) = hash (encode (captureResult b)) := by
  apply certified_run_or_hash_collision hash (fun r => encode (captureResult r))
    (fun bytes => (decode bytes).map (restoreResult (boundaryStore context.backing)))
    context.cfg context.program _ ws _ remainingFuel cert
  apply finite_codec_boundary_decodes context encode decode codec _ _ ws
  · change Res.cont (NearSpecV3.Logged.W.E _ _) = Res.cont _
    rw [NearSpecV3.Logged.W.E_of_StOK (restored_state_backed _ _)]
  · unfold NearSpecV3.Logged.W.ResOK
    rw [← restore_capture_result, capture_restore_result]
  · exact hs
  · exact cert.1

end NearCompression
