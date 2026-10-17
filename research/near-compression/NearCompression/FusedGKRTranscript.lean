import NearCompression.SHA384TranscriptDraw
import NearCompression.SHA384HashFrameDecoder
namespace NearCompression

/-- A separately versioned protocol. No random-oracle or quantum security claim. -/
def fusedGKRProfile : List UInt8 := [110,101,97,114,112,114,111,111,102,45,102,117,115,101,100,45,116,101,114,109,105,110,97,108,45,103,107,114,45,118,51]

def fusedGKRParts (seed payload : List UInt8) (round counter : Nat) : List (List UInt8) :=
  [fusedGKRProfile, seed, [103,107,114,45,118,101,99,116,111,114], payload,
   [103,107,114,45,99,104,97,108,108,101,110,103,101], NearSpec.leN 8 round,
   NearSpec.leN 8 1, NearSpec.leN 8 4, NearSpec.leN 8 counter]

def fusedGKRFrame (seed payload : List UInt8) (round counter : Nat) : List UInt8 :=
  sha384HashFrame sha384SqueezeTag (fusedGKRParts seed payload round counter)

/-- Counter bounds are essential: leN alone truncates large integers. -/
theorem fused_gkr_frame_injective
    (s p s' p' : List UInt8) (r c r' c' : Nat)
    (hr : r < 2^64) (hc : c < 2^64) (hr' : r' < 2^64) (hc' : c' < 2^64)
    (fits : SHA384HashFrameFits sha384SqueezeTag (fusedGKRParts s p r c))
    (fits' : SHA384HashFrameFits sha384SqueezeTag (fusedGKRParts s' p' r' c'))
    (same : fusedGKRFrame s p r c = fusedGKRFrame s' p' r' c') :
    s=s' ∧ p=p' ∧ r=r' ∧ c=c' := by
  have parts := (sha384_hash_frame_injective _ _ _ _ fits fits' same).2
  simp only [fusedGKRParts, List.cons.injEq, and_true, true_and] at parts
  obtain ⟨hs, hp, hround, hcounter⟩ := parts
  have rr := congrArg NearSpec.leNat hround
  have cc := congrArg NearSpec.leNat hcounter
  rw [NearSpec.leNat_leN 8 r hr, NearSpec.leNat_leN 8 r' hr'] at rr
  rw [NearSpec.leNat_leN 8 c hc, NearSpec.leNat_leN 8 c' hc'] at cc
  exact ⟨hs,hp,rr,cc⟩

/-- All retry hashes use the SAME previous seed and pending payload. Only the
counter changes; a successful draw then adopts its final digest as next seed. -/
def fusedGKRScanLoop (blocks : Nat → List UInt8) :
    Nat → Nat → Nat → Option SHA384DrawResult
  | 0,_,_ => none
  | fuel+1,counter,needed =>
    let block := blocks counter
    if block.length ≠ 48 then none else
    let scan := sha384ScanWords needed (sha384DigestWords block)
    if scan.done then some ⟨scan.values,scan.rejected,counter+1,block⟩ else do
      let tail ← fusedGKRScanLoop blocks fuel (counter+1) (needed-scan.values.length)
      pure ⟨scan.values++tail.values,scan.rejected+tail.rejected,tail.blocks,tail.nextSeed⟩

/-- Successful bounded scans return exactly the requested canonical values,
with a 48-byte seed equal to an actually consumed block and no skipped counter. -/
theorem fused_gkr_scan_spec (blocks : Nat → List UInt8)
    (fuel counter needed : Nat) (result : SHA384DrawResult)
    (accepted : fusedGKRScanLoop blocks fuel counter needed = some result) :
    result.values.length = needed ∧
    (∀ v, v ∈ result.values → v < sha384SamplePrime) ∧
    counter < result.blocks ∧ result.blocks ≤ counter+fuel ∧
    result.nextSeed = blocks (result.blocks-1) ∧ result.nextSeed.length=48 := by
  induction fuel generalizing counter needed result with
  | zero => simp [fusedGKRScanLoop] at accepted
  | succ fuel ih =>
    simp only [fusedGKRScanLoop] at accepted
    split at accepted
    · contradiction
    · rename_i good
      split at accepted
      · rename_i done
        cases accepted
        dsimp only
        refine ⟨sha384_scan_done_length _ _ done,sha384_scan_values_range _ _,?_,?_,?_,?_⟩
        · omega
        · omega
        · simp
        · omega
      · cases next : fusedGKRScanLoop blocks fuel (counter+1)
            (needed-(sha384ScanWords needed (sha384DigestWords (blocks counter))).values.length) with
        | none => simp [next] at accepted
        | some tail =>
          simp only [next,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at accepted
          cases accepted
          dsimp only
          obtain ⟨len,range,lower,upper,seed,width⟩ := ih _ _ _ next
          have head := sha384_scan_length_le needed (sha384DigestWords (blocks counter))
          refine ⟨?_,?_,?_,?_,seed,width⟩
          · simp only [List.length_append]; omega
          · intro v hv
            rcases List.mem_append.mp hv with first | rest
            · exact sha384_scan_values_range _ _ v first
            · exact range v rest
          · omega
          · omega

structure FusedGKRState where
  seed : List UInt8
  round : Nat
  pending : Option (List UInt8)
  deriving DecidableEq

def fusedGKRCommit (state : FusedGKRState) (payload : List UInt8) : Option FusedGKRState :=
  match state.pending with
  | none => some { state with pending := some payload }
  | some _ => none

def fusedGKRDraw (hash : SHA384HashFunction) (state : FusedGKRState)
    (maxBlocks : Nat) : Option SHA384DrawResult := do
  let payload ← state.pending
  if state.round < 2^64 ∧ 0 < maxBlocks ∧ maxBlocks ≤ 2^20 then
    fusedGKRScanLoop (fun counter => hash sha384SqueezeTag
      (fusedGKRParts state.seed payload state.round counter)) maxBlocks 0 4
  else none

/-- Accepted public draws produce four field coefficients, consume a bounded
positive number of blocks, and use the final counter's actual hash as seed. -/
theorem fused_gkr_draw_spec (hash : SHA384HashFunction) (state : FusedGKRState)
    (fuel : Nat) (result : SHA384DrawResult)
    (accepted : fusedGKRDraw hash state fuel = some result) :
    result.values.length=4 ∧
    (∀ v, v ∈ result.values → v < sha384SamplePrime) ∧
    0 < result.blocks ∧ result.blocks ≤ fuel ∧
    result.nextSeed.length=48 ∧
    ∃ payload, state.pending=some payload ∧ result.nextSeed = hash sha384SqueezeTag
      (fusedGKRParts state.seed payload state.round (result.blocks-1)) := by
  cases pending : state.pending with
  | none => simp [fusedGKRDraw,pending] at accepted
  | some payload =>
    simp only [fusedGKRDraw,pending,Bind.bind,Option.bind] at accepted
    split at accepted
    · obtain ⟨len,range,lower,upper,seed,width⟩ := fused_gkr_scan_spec _ _ _ _ _ accepted
      exact ⟨len,range,lower,by simpa using upper,width,payload,rfl,seed⟩
    · contradiction

def fusedGKRUpdate (state : FusedGKRState) (result : Option SHA384DrawResult) : FusedGKRState :=
  match result with
  | none => state
  | some r => ⟨r.nextSeed,state.round+1,none⟩

theorem fused_gkr_failure_preserves_state (state : FusedGKRState) :
    fusedGKRUpdate state none = state := rfl

theorem fused_gkr_success_advances_once (state : FusedGKRState) (result : SHA384DrawResult) :
    (fusedGKRUpdate state (some result)).round = state.round+1 ∧
    (fusedGKRUpdate state (some result)).pending = none ∧
    (fusedGKRUpdate state (some result)).seed = result.nextSeed := ⟨rfl,rfl,rfl⟩

theorem fused_gkr_double_commit_rejected (state : FusedGKRState) (p q : List UInt8)
    (pending : state.pending = some p) : fusedGKRCommit state q = none := by
  simp [fusedGKRCommit,pending]

theorem fused_gkr_no_commit_no_draw (hash : SHA384HashFunction) (state : FusedGKRState)
    (fuel : Nat) (empty : state.pending=none) : fusedGKRDraw hash state fuel=none := by
  simp [fusedGKRDraw,empty]
end NearCompression
