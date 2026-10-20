import NearCompression.SHA384ComputedSource
namespace NearCompression
open ZkFormal.Algebra

/-- Evaluation form of the already certified mutable FFT source. This avoids
replaying functional update chains when executing validation fixtures. -/
def sha384EvaluatedSourceWords (n p width : Nat) (table : Nat→Nat→Fp)
    (omega : Fp) (index : Nat) : List Nat :=
  sha384FpPairWords (sourceWideLeaf (packedComputedSources n p width table) (omega^index))

theorem sha384_evaluated_source_words (n p width : Nat) (table : Nat→Nat→Fp)
    (omega : Fp) (halfOrder : omega^(2^(n+p+1))= -1)
    (index : Nat) (bound : index<2^(n+p+1)) :
    sha384EvaluatedSourceWords n p width table omega index=
      sha384ComputedSourceWords n p width table omega index := by
  unfold sha384EvaluatedSourceWords sha384ComputedSourceWords
  rw [packed_computed_wide_leaf n p width table omega halfOrder index bound]

def sha384EvaluatedSource (n p width : Nat) (table : Nat→Nat→Fp) (omega : Fp) : List (List Nat) :=
  (List.range (2^(n+p+1))).map (sha384EvaluatedSourceWords n p width table omega)

theorem sha384_evaluated_source (n p width : Nat) (table : Nat→Nat→Fp)
    (omega : Fp) (halfOrder : omega^(2^(n+p+1))= -1) :
    sha384EvaluatedSource n p width table omega=sha384ComputedSource n p width table omega := by
  unfold sha384EvaluatedSource sha384ComputedSource
  apply List.map_congr_left
  intro i hi
  exact sha384_evaluated_source_words n p width table omega halfOrder i (List.mem_range.mp hi)
end NearCompression
