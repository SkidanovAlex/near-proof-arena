import NearCompression.SHA512FeedForward
import NearCompression.SHA512BlockDecode
import NearCompression.SHA512WindowBounds

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def sha512DecodedState (row : Nat → Fp) : List Nat :=
  (List.range 8).map (sha512FeedForwardVarsWord (sha512CombinedVars row))

/-- Decode an eight-word state without unfolding any compression rounds. -/
theorem sha512_vars_list_roundtrip (v : Vars) :
    ofList ((List.range 8).map (sha512FeedForwardVarsWord v)) = v := by
  cases v
  rfl

/-- Feed-forward list identity with an abstract result, avoiding round reduction. -/
theorem sha512_vars_feedforward_list (v result : Vars) :
    [add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 0 0) result.a,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 1 0) result.b,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 2 0) result.c,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 3 0) result.d,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 4 0) result.e,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 5 0) result.f,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 6 0) result.g,
     add64 (((List.range 8).map (sha512FeedForwardVarsWord v)).getD 7 0) result.h] =
    (List.range 8).map (fun i => add64 (sha512FeedForwardVarsWord v i)
      (sha512FeedForwardVarsWord result i)) := by rfl

/-- Symbolic feed-forward identity: the round result stays opaque to reduction. -/
theorem sha512_compress_vars (v : Vars) (block : List Nat) :
    compress ((List.range 8).map (sha512FeedForwardVarsWord v)) block =
      (List.range 8).map (fun i => add64 (sha512FeedForwardVarsWord v i)
        (sha512FeedForwardVarsWord (rounds v K (words block)) i)) := by
  have identity := sha512_vars_feedforward_list v (rounds v K (words block))
  with_reducible
    unfold compress
    rw [sha512_vars_list_roundtrip]
    exact identity

/-- Compression correctness for the state and byte block decoded from the trace.
Binding them to public inputs, and padding a message, are separate obligations. -/
theorem sha512_compression_sound (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length) (table : air.tables[t] = sha512FeedForwardTable)
    (holds : Holds air pub tr) :
    sha512FeedForwardOutput (tr.cell t 79) =
      compress (sha512DecodedState (tr.cell t 0)) (sha512DecodedBlock (tr.cell t 0)) := by
  rw [sha512_ff_endpoint air tr pub t ht table holds]
  unfold sha512DecodedState
  rw [sha512_compress_vars,sha512_decoded_block_words]
  rfl

/-- The decoded block consists of genuine byte values, not merely arbitrary naturals. -/
theorem sha512_compression_bytes_bound (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length) (table : air.tables[t] = sha512FeedForwardTable)
    (holds : Holds air pub tr) (byte : Nat) (member : byte ∈ sha512DecodedBlock (tr.cell t 0)) :
    byte < 256 := by
  have constants := sha512_ff_constants_holds air tr pub t ht table holds
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl constants
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl combined
  obtain ⟨i,hi,hb⟩ := List.mem_flatMap.mp member
  apply sha512_word_bytes_bound (tr.cell t 0) (sha512ScheduleWindowBase i) _ byte hb
  intro bit hbit
  have bound := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0
    (Nat.two_pow_pos _) i (List.mem_range.mp hi) bit hbit
  simpa only [sha512CombinedProjection,Nat.zero_add] using bound

end NearCompression
