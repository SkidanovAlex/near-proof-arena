import NearCompression.Ext4PairBytes
import NearCompression.WeightedTerminalAuthentication
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Full typed leaf serialization, lane pairs in order. The terminal has one lane. -/
def ext4TerminalRoot (hash : SHA384ByteHash) (context : List UInt8) (depth : Nat)
    (leaves : List (List (Fp4×Fp4))) : List UInt8 :=
  sha384SourceRoot hash context (leaves.map (fun leaf => leaf.flatMap ext4PairBytes)) depth

def ext4TerminalReconstructedPairs (anchors : List Fp4) (terminal : Fp4) : List (Fp4×Fp4) :=
  anchors.map (fun x => ((Poly.mk [terminal]).eval x,(Poly.mk [terminal]).eval (-x)))

def ext4TerminalOraclePairs (half : Nat) (oracle : Nat → Fp4) : List (Fp4×Fp4) :=
  (List.range half).map (fun i => (oracle i,oracle (i+half)))

/-- Collision supported on paths in the two actual serialized terminal trees. -/
def Ext4TerminalHashCollision (hash : SHA384ByteHash) (context : List UInt8) (depth : Nat)
    (anchors : List Fp4) (terminal : Fp4) (oracle : Nat → Fp4) : Prop :=
  let left := (ext4TerminalReconstructedPairs anchors terminal).map ext4PairBytes
  let right := (ext4TerminalOraclePairs anchors.length oracle).map ext4PairBytes
  ∃ index,index<anchors.length ∧
    ∃ a,a∈sha384MerklePathQueries hash context anchors.length index (left.getD index [])
      (sha384TreePath hash context left depth 0 index) ∧
    ∃ b,b∈sha384MerklePathQueries hash context anchors.length index (right.getD index [])
      (sha384TreePath hash context right depth 0 index) ∧ a≠b ∧ hash a=hash b

/-- The concrete serialized reconstruction check authenticates every terminal
index, or supplies a supported byte-level hash collision. No abstract tree
injectivity, oracle degree or canonical-coordinate premise is assumed. -/
theorem ext4_terminal_check_authenticates_or_collision (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : List UInt8) (depth : Nat)
    (anchors : List Fp4) (terminal weight claim : Fp4) (oracle : Nat → Fp4)
    (positive : 0<depth) (shape : anchors.length=2^depth)
    (capacity : anchors.length<2^64) (contextBound : context.length<2^64)
    (checked : reconstructedRSChecks (ext4TerminalRoot hash context depth) 1 1
      [[terminal]] [[weight]] anchors (weightedTerminalPairLeaves anchors.length oracle) claim=true) :
    (∀ y,y<2*anchors.length → oracle y=terminal) ∨
      Ext4TerminalHashCollision hash context depth anchors terminal oracle := by
  classical
  by_cases authenticated : ∀ y,y<2*anchors.length → oracle y=terminal
  · exact Or.inl authenticated
  · right
    let left := ext4TerminalReconstructedPairs anchors terminal
    let right := ext4TerminalOraclePairs anchors.length oracle
    have different : left≠right := by
      intro same
      apply authenticated
      apply weighted_terminal_pair_constant anchors.length oracle anchors rfl terminal
      have cells := congrArg (fun pairs : List (Fp4×Fp4) => pairs.map (fun pair => [pair])) same.symm
      simpa only [left,right,ext4TerminalReconstructedPairs,ext4TerminalOraclePairs,
        weightedTerminalPairLeaves,reconstructedRSLeaves,List.map_map,Function.comp_def,
        List.map_cons,List.map_nil] using cells
    have roots : sha384SourceRoot hash context (left.map ext4PairBytes) depth=
        sha384SourceRoot hash context (right.map ext4PairBytes) depth := by
      simp only [reconstructedRSChecks,Bool.and_eq_true,decide_eq_true_eq] at checked
      have same := checked.1.2
      simpa only [ext4TerminalRoot,reconstructedRSLeaves,weightedTerminalPairLeaves,
        left,right,ext4TerminalReconstructedPairs,ext4TerminalOraclePairs,List.map_map,
        Function.comp_def,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil] using same
    obtain ⟨index,position,neq,a,ha,b,hb,differentInputs,equalHash⟩ :=
      ext4_pair_tree_hash_collision hash width context left right depth positive
        (by simpa [left,ext4TerminalReconstructedPairs] using shape)
        (by simpa [right,ext4TerminalOraclePairs] using shape)
        (by simpa [left,ext4TerminalReconstructedPairs] using capacity) contextBound different roots
    refine ⟨index,?_,a,?_,b,?_,differentInputs,equalHash⟩
    · simpa [left,ext4TerminalReconstructedPairs] using position
    · simpa only [left,ext4TerminalReconstructedPairs,List.length_map] using ha
    · simpa only [left,ext4TerminalReconstructedPairs,List.length_map] using hb

/-- Exact terminal-oracle premise for folding, conditional only on absence of
the concrete supported hash collision. Its probability remains to be bounded. -/
theorem ext4_terminal_check_authenticated (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : List UInt8) (depth : Nat)
    (anchors : List Fp4) (terminal weight claim : Fp4) (oracle : Nat → Fp4)
    (positive : 0<depth) (shape : anchors.length=2^depth)
    (capacity : anchors.length<2^64) (contextBound : context.length<2^64)
    (checked : reconstructedRSChecks (ext4TerminalRoot hash context depth) 1 1
      [[terminal]] [[weight]] anchors (weightedTerminalPairLeaves anchors.length oracle) claim=true)
    (binding : ¬Ext4TerminalHashCollision hash context depth anchors terminal oracle) :
    ∀ y,y<2*anchors.length → oracle y=terminal := by
  rcases ext4_terminal_check_authenticates_or_collision hash width context depth anchors terminal weight
    claim oracle positive shape capacity contextBound checked with authenticated | collision
  · exact authenticated
  · exact False.elim (binding collision)

end NearCompression
