import NearCompression.SHA384TranscriptCommit
import NearCompression.FieldRejectionSampler
namespace NearCompression

abbrev SHA384HashFunction := List UInt8 → List (List UInt8) → List UInt8

def sha384ModelHash : SHA384HashFunction := fun tag parts=>sha384ChainDigest (sha384HashFrame tag parts)
def sha384SamplePrime : Nat := 2013265921
def sha384SampleLimit : Nat := 2*sha384SamplePrime

def sha384AcceptWord (word : Nat) : Option Nat :=
  if word<sha384SampleLimit then some (word%sha384SamplePrime) else none

def sha384DigestWords (block : List UInt8) : List Nat :=
  (List.range 12).map (fun i=>NearSpec.leNat ((block.drop (4*i)).take 4))

structure SHA384WordScan where
  values : List Nat
  rejected : Nat
  done : Bool
  deriving Repr

/-- Consumes only through the requested accepted word, not the unused digest
suffix. This distinction matters to rejected_words in the Python API. -/
def sha384ScanWords : Nat → List Nat → SHA384WordScan
  | 0,_ => ⟨[],0,true⟩
  | _+1,[] => ⟨[],0,false⟩
  | n+1,w::ws =>
    match sha384AcceptWord w with
    | some v => let tail:=sha384ScanWords n ws; ⟨v::tail.values,tail.rejected,tail.done⟩
    | none => let tail:=sha384ScanWords (n+1) ws; ⟨tail.values,tail.rejected+1,tail.done⟩
termination_by n ws => ws.length + n

structure SHA384DrawResult where
  values : List Nat
  rejected : Nat
  blocks : Nat
  nextSeed : List UInt8
  deriving Repr

def sha384RequestTag : List UInt8 := [116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47, 114, 101, 113, 117, 101, 115, 116]
def sha384SqueezeTag : List UInt8 := [116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47, 115, 113, 117, 101, 101, 122, 101]
def sha384RatchetTag : List UInt8 := [116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47, 114, 97, 116, 99, 104, 101, 116]
def sha384DrawResultTag : List UInt8 := [116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47, 100, 114, 97, 119, 45, 114, 101, 115, 117, 108, 116]

/-- Bounded operational loop, with exact request dimensions retained separately
from their product. Hash uniformity is neither required nor asserted. -/
def sha384DrawLoop (hash : SHA384HashFunction) (label : List UInt8) (count coefficients : Nat) :
    Nat → Nat → Nat → List UInt8 → Option SHA384DrawResult
  | 0,_,_,_ => none
  | fuel+1,counter,needed,seed =>
    let block:=hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]
    if block.length≠48 then none else
    let ratchet:=hash sha384RatchetTag [seed,label,block]
    let scan:=sha384ScanWords needed (sha384DigestWords block)
    if scan.done then
      some ⟨scan.values,scan.rejected,counter+1,
        hash sha384DrawResultTag [ratchet,label,NearSpec.leN 8 count,
          NearSpec.leN 8 coefficients,NearSpec.leN 8 (counter+1)]⟩
    else do
      let tail ← sha384DrawLoop hash label count coefficients fuel (counter+1)
        (needed-scan.values.length) ratchet
      pure ⟨scan.values++tail.values,scan.rejected+tail.rejected,tail.blocks,tail.nextSeed⟩

def sha384TranscriptDraw (hash : SHA384HashFunction) (seed label : List UInt8)
    (count coefficients maxBlocks : Nat) : Option SHA384DrawResult :=
  if 0<count ∧ count≤4096 ∧ 0<coefficients ∧ coefficients≤64 ∧ 0<maxBlocks ∧ maxBlocks≤2^20 then
    sha384DrawLoop hash label count coefficients maxBlocks 0 (count*coefficients)
      (hash sha384RequestTag [seed,label,NearSpec.leN 8 count,NearSpec.leN 8 coefficients])
  else none

def sha384DrawStateUpdate (seed : List UInt8) (result : Option SHA384DrawResult) : List UInt8 :=
  match result with | none=>seed | some r=>r.nextSeed

theorem sha384_sample_limit_exact : (2^32/sha384SamplePrime)*sha384SamplePrime=sha384SampleLimit := by decide

theorem sha384_accept_word_some (word value : Nat) :
    sha384AcceptWord word=some value ↔ word<sha384SampleLimit ∧ value=word%sha384SamplePrime := by
  simp [sha384AcceptWord]
  omega

theorem sha384_accept_word_none (word : Nat) :
    sha384AcceptWord word=none ↔ sha384SampleLimit≤word := by simp [sha384AcceptWord]

theorem sha384_accept_word_range (word value : Nat) (h : sha384AcceptWord word=some value) :
    value<sha384SamplePrime := by
  rw [(sha384_accept_word_some word value).mp h |>.2]
  exact Nat.mod_lt _ (by decide)

theorem sha384_scan_values_range (needed : Nat) (words : List Nat) :
    ∀ v,v∈(sha384ScanWords needed words).values → v<sha384SamplePrime := by
  induction words generalizing needed with
  | nil => cases needed <;> simp [sha384ScanWords]
  | cons w ws ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord w with
      | none => simpa [sha384ScanWords,accepted] using ih (n+1)
      | some v =>
        intro x hx
        simp only [sha384ScanWords,accepted,List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact sha384_accept_word_range w x accepted
        · exact ih n x hx

theorem sha384_scan_done_length (needed : Nat) (words : List Nat)
    (done : (sha384ScanWords needed words).done=true) :
    (sha384ScanWords needed words).values.length=needed := by
  induction words generalizing needed with
  | nil => cases needed <;> simp_all [sha384ScanWords]
  | cons w ws ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord w with
      | none => simpa [sha384ScanWords,accepted] using ih (n+1) (by simpa [sha384ScanWords,accepted] using done)
      | some v =>
        have tail := ih n (by simpa [sha384ScanWords,accepted] using done)
        simp [sha384ScanWords,accepted,tail]

theorem sha384_draw_failure_preserves_seed (seed : List UInt8) :
    sha384DrawStateUpdate seed none=seed := rfl
private theorem leNat_range (bs : List UInt8) : NearSpec.leNat bs<256^bs.length := by
  induction bs with
  | nil => simp [NearSpec.leNat]
  | cons b bs ih =>
    have bound:=b.toNat_lt
    simp only [NearSpec.leNat,List.length_cons,Nat.pow_succ]
    omega

theorem sha384_digest_words_shape (block : List UInt8) :
    (sha384DigestWords block).length=12 ∧ ∀ w,w∈sha384DigestWords block → w<2^32 := by
  constructor
  · simp [sha384DigestWords]
  · intro w hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    have bound:=leNat_range ((block.drop (4*i)).take 4)
    have len : ((block.drop (4*i)).take 4).length≤4 := by simp only [List.length_take];exact Nat.min_le_left _ _
    have small : 256^((block.drop (4*i)).take 4).length≤256^4 := Nat.pow_le_pow_right (by omega) len
    omega

theorem sha384_scan_length_le (needed : Nat) (words : List Nat) :
    (sha384ScanWords needed words).values.length≤needed := by
  induction words generalizing needed with
  | nil => cases needed <;> simp [sha384ScanWords]
  | cons w ws ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord w with
      | none => simpa [sha384ScanWords,accepted] using ih (n+1)
      | some v => simpa [sha384ScanWords,accepted] using Nat.succ_le_succ (ih n)

theorem sha384_draw_loop_range (hash : SHA384HashFunction) (label : List UInt8)
    (count coefficients fuel counter needed : Nat) (seed : List UInt8) (result : SHA384DrawResult)
    (accepted : sha384DrawLoop hash label count coefficients fuel counter needed seed=some result) :
    ∀ v,v∈result.values → v<sha384SamplePrime := by
  induction fuel generalizing counter needed seed result with
  | zero => simp [sha384DrawLoop] at accepted
  | succ fuel ih =>
    simp only [sha384DrawLoop] at accepted
    split at accepted
    · contradiction
    · split at accepted
      · cases accepted
        exact sha384_scan_values_range _ _
      · cases next : sha384DrawLoop hash label count coefficients fuel (counter+1)
            (needed-(sha384ScanWords needed (sha384DigestWords
              (hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]))).values.length)
            (hash sha384RatchetTag [seed,label,hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]]) with
        | none => simp [next] at accepted
        | some tail =>
          simp only [next,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at accepted
          cases accepted
          intro v hv
          rcases List.mem_append.mp hv with head | rest
          · exact sha384_scan_values_range _ _ v head
          · exact ih _ _ _ _ next v rest

theorem sha384_draw_loop_length (hash : SHA384HashFunction) (label : List UInt8)
    (count coefficients fuel counter needed : Nat) (seed : List UInt8) (result : SHA384DrawResult)
    (accepted : sha384DrawLoop hash label count coefficients fuel counter needed seed=some result) :
    result.values.length=needed := by
  induction fuel generalizing counter needed seed result with
  | zero => simp [sha384DrawLoop] at accepted
  | succ fuel ih =>
    simp only [sha384DrawLoop] at accepted
    split at accepted
    · contradiction
    · split at accepted
      · cases accepted
        exact sha384_scan_done_length _ _ (by assumption)
      · cases next : sha384DrawLoop hash label count coefficients fuel (counter+1)
            (needed-(sha384ScanWords needed (sha384DigestWords
              (hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]))).values.length)
            (hash sha384RatchetTag [seed,label,hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]]) with
        | none => simp [next] at accepted
        | some tail =>
          simp only [next,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at accepted
          cases accepted
          have head:=sha384_scan_length_le needed (sha384DigestWords
            (hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]))
          have tailLength:=ih _ _ _ _ next
          simp only [List.length_append]
          omega

theorem sha384_draw_values_range (hash : SHA384HashFunction) (seed label : List UInt8)
    (count coefficients maxBlocks : Nat) (result : SHA384DrawResult)
    (accepted : sha384TranscriptDraw hash seed label count coefficients maxBlocks=some result) :
    ∀ v,v∈result.values → v<sha384SamplePrime := by
  unfold sha384TranscriptDraw at accepted
  split at accepted
  · exact sha384_draw_loop_range _ _ _ _ _ _ _ _ _ accepted
  · contradiction
theorem sha384_draw_values_length (hash : SHA384HashFunction) (seed label : List UInt8)
    (count coefficients maxBlocks : Nat) (result : SHA384DrawResult)
    (accepted : sha384TranscriptDraw hash seed label count coefficients maxBlocks=some result) :
    result.values.length=count*coefficients := by
  unfold sha384TranscriptDraw at accepted
  split at accepted
  · exact sha384_draw_loop_length _ _ _ _ _ _ _ _ _ accepted
  · contradiction
/-- Connects the operational accept function to the existing exact two-preimage
count. Uniformity follows only for an independently justified uniform word. -/
theorem sha384_accept_word_preimages (word value : Nat) (hv : value<sha384SamplePrime) :
    (word<2^32 ∧ sha384AcceptWord word=some value) ↔
      word=value ∨ word=value+sha384SamplePrime := by
  rw [sha384_accept_word_some]
  have fact := rejection_prime32 value word hv
  simpa only [sha384SamplePrime,sha384SampleLimit,rejectionAccept,rejectionValue,eq_comm] using fact
end NearCompression
