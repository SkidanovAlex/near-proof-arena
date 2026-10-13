import NearSpecV3.WitnessV3

/-! Declarations of `ZkFormal.NearV3.Rcpt.Candidates.OrderedSources` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

theorem lookupLast_key {key : Bytes} {entries : List ProofEntry} {e : ProofEntry}
    (h : lookupLast key entries = some e) : e.key = key := by
  induction entries with
  | nil => cases h
  | cons a rest ih =>
    simp only [lookupLast] at h
    split at h
    · rename_i f hf
      cases h
      exact ih hf
    · split at h
      · rename_i he
        cases h
        simpa using he
      · cases h

end ZkFormal.NearV3.Rcpt.Candidates
