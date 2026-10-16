import NearCompression.SHA384TranscriptDraw
namespace NearCompression

/-- A scan counts only consumed words, including rejection, even when it
stops before the digest suffix. -/
theorem sha384_scan_consumed_bound (needed : Nat) (words : List Nat) :
    (sha384ScanWords needed words).values.length+(sha384ScanWords needed words).rejected≤words.length := by
  induction words generalizing needed with
  | nil => cases needed <;> simp [sha384ScanWords]
  | cons word rest ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord word with
      | none => have h:=ih (n+1);simp only [sha384ScanWords,accepted,List.length_cons];omega
      | some v => have h:=ih n;simp only [sha384ScanWords,accepted,List.length_cons];omega

/-- Successful loops consume a positive number of blocks within their fuel,
and the accepted plus rejected word count fits those consumed blocks. -/
theorem sha384_draw_loop_budget (hash : SHA384HashFunction) (label : List UInt8)
    (count coefficients fuel counter needed : Nat) (seed : List UInt8) (result : SHA384DrawResult)
    (accepted : sha384DrawLoop hash label count coefficients fuel counter needed seed=some result) :
    counter<result.blocks ∧ result.blocks≤counter+fuel ∧
      result.values.length+result.rejected≤12*(result.blocks-counter) := by
  induction fuel generalizing counter needed seed result with
  | zero => simp [sha384DrawLoop] at accepted
  | succ fuel ih =>
    have scan:=sha384_scan_consumed_bound needed
      (sha384DigestWords (hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]))
    rw [(sha384_digest_words_shape _).1] at scan
    simp only [sha384DrawLoop] at accepted
    split at accepted
    · contradiction
    · split at accepted
      · cases accepted
        simp only
        omega
      · cases next : sha384DrawLoop hash label count coefficients fuel (counter+1)
            (needed-(sha384ScanWords needed (sha384DigestWords
              (hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]))).values.length)
            (hash sha384RatchetTag [seed,label,hash sha384SqueezeTag [seed,label,NearSpec.leN 8 counter]]) with
        | none => simp [next] at accepted
        | some tail =>
          simp only [next,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at accepted
          cases accepted
          have bounds:=ih _ _ _ _ next
          simp only [List.length_append]
          omega

/-- Successful public requests have an in-range u64 block counter and
bounded metadata. This is deterministic bookkeeping, not a probabilistic
termination or uniformity claim. -/
theorem sha384_draw_request_budget (hash : SHA384HashFunction) (seed label : List UInt8)
    (count coefficients maxBlocks : Nat) (result : SHA384DrawResult)
    (accepted : sha384TranscriptDraw hash seed label count coefficients maxBlocks=some result) :
    0<result.blocks ∧ result.blocks≤maxBlocks ∧ result.blocks<2^64 ∧
      count<2^64 ∧ coefficients<2^64 ∧
      count*coefficients+result.rejected≤12*result.blocks := by
  have length:=sha384_draw_values_length hash seed label count coefficients maxBlocks result accepted
  unfold sha384TranscriptDraw at accepted
  split at accepted
  · rename_i shape
    have bounds:=sha384_draw_loop_budget _ _ _ _ _ _ _ _ _ accepted
    simp only [Nat.zero_add,Nat.sub_zero] at bounds
    rw [length] at bounds
    omega
  · contradiction
end NearCompression
