import NearCompression.SHA384TranscriptDraw
namespace NearCompression

/-- Connects the operational short-circuit scan to the filter/take reference
used to populate circuit outputs. Rejected-word accounting remains separate. -/
theorem sha384_scan_values_filter_take (needed : Nat) (words : List Nat) :
    (sha384ScanWords needed words).values = (words.filterMap sha384AcceptWord).take needed := by
  induction words generalizing needed with
  | nil => cases needed <;> simp [sha384ScanWords]
  | cons word words ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord word with
      | none => simpa [sha384ScanWords,accepted] using ih (n+1)
      | some value => simpa [sha384ScanWords,accepted] using congrArg (List.cons value) (ih n)

/-- A one-block circuit must reject if fewer than four words pass the threshold;
zero-filling the missing outputs would not implement the transcript. -/
theorem sha384_scan_done_iff (needed : Nat) (words : List Nat) :
    (sha384ScanWords needed words).done = true ↔
      needed ≤ (words.filterMap sha384AcceptWord).length := by
  induction words generalizing needed with
  | nil => cases needed <;> simp [sha384ScanWords]
  | cons word words ih =>
    cases needed with
    | zero => simp [sha384ScanWords]
    | succ n =>
      cases accepted : sha384AcceptWord word with
      | none => simpa [sha384ScanWords,accepted] using ih (n+1)
      | some value => simpa [sha384ScanWords,accepted] using ih n

#print axioms sha384_scan_values_filter_take
#print axioms sha384_scan_done_iff
end NearCompression
