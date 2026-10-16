import NearCompression.SHA384MerklePath
namespace NearCompression

def sha384TreeValue (hash : SHA384ByteHash) (context : List UInt8) (leaves : List (List UInt8)) :
    Nat → Nat → List UInt8
  | 0,index=>hash (sha384HashFrame sha384MerkleLeafTag [context,NearSpec.leN 8 index,leaves.getD index []])
  | depth+1,index=>hash (sha384HashFrame sha384MerkleNodeTag [context,NearSpec.leN 8 (depth+1),
      sha384TreeValue hash context leaves depth (2*index),sha384TreeValue hash context leaves depth (2*index+1)])

def sha384SiblingIndex (index : Nat) : Nat := if index%2=1 then index-1 else index+1

/-- The low-to-high sibling order used by Python merkle_path. -/
def sha384TreePath (hash : SHA384ByteHash) (context : List UInt8) (leaves : List (List UInt8)) :
    Nat → Nat → Nat → List (List UInt8)
  | 0,_,_=>[]
  | remaining+1,level,index=>sha384TreeValue hash context leaves level (sha384SiblingIndex index)::
      sha384TreePath hash context leaves remaining (level+1) (index/2)

def sha384SourceRoot (hash : SHA384ByteHash) (context : List UInt8)
    (leaves : List (List UInt8)) (depth : Nat) : List UInt8 :=
  hash (sha384HashFrame sha384MerkleRootTag
    [context,NearSpec.leN 8 leaves.length,sha384TreeValue hash context leaves depth 0])

theorem sha384_tree_value_width (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (leaves : List (List UInt8)) (depth index : Nat) :
    (sha384TreeValue hash context leaves depth index).length=48 := by
  cases depth <;> exact width _

theorem sha384_tree_path_shape (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (leaves : List (List UInt8)) (remaining level index : Nat) :
    (sha384TreePath hash context leaves remaining level index).length=remaining ∧
      ∀ x,x∈sha384TreePath hash context leaves remaining level index → x.length=48 := by
  induction remaining generalizing level index with
  | zero => simp [sha384TreePath]
  | succ n ih =>
    have tail:=ih (level+1) (index/2)
    constructor
    · simp [sha384TreePath,tail.1]
    · intro x hx
      simp only [sha384TreePath,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact sha384_tree_value_width hash width context leaves level _
      · exact tail.2 x hx

private theorem tree_parent (hash : SHA384ByteHash) (context : List UInt8)
    (leaves : List (List UInt8)) (level index : Nat) :
    hash (sha384HashFrame sha384MerkleNodeTag ([context,NearSpec.leN 8 (level+1)]++
      (if index%2=1 then
        [sha384TreeValue hash context leaves level (sha384SiblingIndex index),sha384TreeValue hash context leaves level index]
      else [sha384TreeValue hash context leaves level index,sha384TreeValue hash context leaves level (sha384SiblingIndex index)])))=
      sha384TreeValue hash context leaves (level+1) (index/2) := by
  have modBound:=Nat.mod_lt index (by omega : 0<2)
  have decomp:=Nat.mod_add_div index 2
  by_cases odd : index%2=1
  · have a : index-1=2*(index/2) := by omega
    have b : index=2*(index/2)+1 := by omega
    simp only [sha384SiblingIndex,ite_eq_left odd,sha384TreeValue,a]
    congr 3
    simp only [List.cons_append,List.nil_append,List.cons.injEq,true_and,and_true]
    exact congrArg (sha384TreeValue hash context leaves level) b
  · have a : index=2*(index/2) := by omega
    have b : index+1=2*(index/2)+1 := by omega
    simp only [sha384SiblingIndex,ite_eq_right odd,sha384TreeValue,b]
    congr 3
    simp only [List.cons_append,List.nil_append,List.cons.injEq,true_and,and_true]
    exact congrArg (sha384TreeValue hash context leaves level) a

theorem sha384_tree_path_fold (hash : SHA384ByteHash) (context : List UInt8)
    (leaves : List (List UInt8)) (remaining level index : Nat) :
    sha384MerkleFold hash context (level+1) index (sha384TreeValue hash context leaves level index)
      (sha384TreePath hash context leaves remaining level index)=
      sha384TreeValue hash context leaves (level+remaining) (index/2^remaining) := by
  induction remaining generalizing level index with
  | zero => simp [sha384TreePath,sha384MerkleFold]
  | succ n ih =>
    simp only [sha384TreePath,sha384MerkleFold,tree_parent]
    have tail:=ih (level+1) (index/2)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n,Nat.pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm] using tail
theorem sha384_source_constructed_root (hash : SHA384ByteHash) (context : List UInt8)
    (leaves : List (List UInt8)) (depth index : Nat)
    (shape : leaves.length=2^depth) (position : index<leaves.length) :
    sha384MerkleRoot hash context leaves.length index (leaves.getD index [])
      (sha384TreePath hash context leaves depth 0 index)=sha384SourceRoot hash context leaves depth := by
  have folded:=sha384_tree_path_fold hash context leaves depth 0 index
  have quotient : index/2^depth=0 := Nat.div_eq_of_lt (by omega)
  simp only [Nat.zero_add,quotient] at folded
  unfold sha384MerkleRoot sha384SourceRoot
  change hash (sha384HashFrame sha384MerkleRootTag [context,NearSpec.leN 8 leaves.length,
    sha384MerkleFold hash context 1 index (sha384TreeValue hash context leaves 0 index)
      (sha384TreePath hash context leaves depth 0 index)])=_
  rw [folded]

theorem sha384_source_path_accepts (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (leaves : List (List UInt8)) (depth index : Nat)
    (positive : 0<depth) (shape : leaves.length=2^depth)
    (capacity : leaves.length<2^64) (position : index<leaves.length)
    (contextBound : context.length<2^64) (leafBound : (leaves.getD index []).length<2^64) :
    sha384VerifyPath hash (sha384SourceRoot hash context leaves depth) context leaves.length index
      (leaves.getD index []) (sha384TreePath hash context leaves depth 0 index)=true := by
  have pathShape:=sha384_tree_path_shape hash width context leaves depth 0 index
  have minCount : 2≤leaves.length := by
    rw [shape]
    exact Nat.pow_le_pow_right (n:=2) (by omega) positive
  simp only [sha384VerifyPath,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  refine ⟨⟨minCount,?_,position,capacity,contextBound,leafBound,width _,pathShape.2⟩,?_⟩
  · rw [pathShape.1,shape]
  · exact sha384_source_constructed_root hash context leaves depth index shape position

/-- Binding to a fixed, fully specified source tree. The arbitrary opening is
compared with the constructed source opening; any differing leaf supplies a
collision among those two finite query supports. No unknown-root extraction. -/
theorem sha384_fixed_source_opening (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (leaves : List (List UInt8)) (depth index : Nat)
    (positive : 0<depth) (shape : leaves.length=2^depth)
    (capacity : leaves.length<2^64) (position : index<leaves.length)
    (contextBound : context.length<2^64) (leafBound : (leaves.getD index []).length<2^64)
    (claimed : List UInt8) (path : List (List UInt8))
    (accepted : sha384VerifyPath hash (sha384SourceRoot hash context leaves depth)
      context leaves.length index claimed path=true) :
    claimed=leaves.getD index [] ∨
      ∃ a,a∈sha384MerklePathQueries hash context leaves.length index claimed path ∧
        ∃ b,b∈sha384MerklePathQueries hash context leaves.length index (leaves.getD index [])
          (sha384TreePath hash context leaves depth 0 index) ∧ a≠b ∧ hash a=hash b := by
  by_cases same : claimed=leaves.getD index []
  · exact Or.inl same
  · exact Or.inr (sha384_merkle_conflicting_openings hash width _ context leaves.length index claimed
      (leaves.getD index []) path (sha384TreePath hash context leaves depth 0 index) accepted
      (sha384_source_path_accepts hash width context leaves depth index positive shape capacity position contextBound leafBound) same)
/-- Two different fully reconstructed byte trees with the same root yield an
explicit hash collision on constructed paths to a differing leaf. This supplies
full-tree binding from finite hash-query binding, without assuming root
injectivity. It does not extract a tree from an arbitrary digest. -/
theorem sha384_source_tree_collision (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : List UInt8)
    (left right : List (List UInt8)) (depth : Nat)
    (positive : 0<depth) (leftShape : left.length=2^depth)
    (rightShape : right.length=2^depth) (capacity : left.length<2^64)
    (contextBound : context.length<2^64)
    (leftBound : ∀ i,i<left.length → (left.getD i []).length<2^64)
    (rightBound : ∀ i,i<right.length → (right.getD i []).length<2^64)
    (different : left≠right)
    (roots : sha384SourceRoot hash context left depth=sha384SourceRoot hash context right depth) :
    ∃ index,index<left.length ∧ left.getD index []≠right.getD index [] ∧
      ∃ a,a∈sha384MerklePathQueries hash context left.length index (left.getD index [])
        (sha384TreePath hash context left depth 0 index) ∧
      ∃ b,b∈sha384MerklePathQueries hash context left.length index (right.getD index [])
        (sha384TreePath hash context right depth 0 index) ∧ a≠b ∧ hash a=hash b := by
  classical
  have size : left.length=right.length := leftShape.trans rightShape.symm
  have witness : ∃ i,i<left.length ∧ left.getD i []≠right.getD i [] := by
    apply Classical.byContradiction
    intro absent
    apply different
    apply List.ext_getElem size
    intro i hl hr
    have same : left.getD i []=right.getD i [] := by
      apply Classical.byContradiction
      intro neq
      exact absent ⟨i,hl,neq⟩
    simpa [List.getD,hl,hr] using same
  obtain ⟨index,position,neq⟩ := witness
  have rightPosition : index<right.length := by omega
  have leftAccept := sha384_source_path_accepts hash width context left depth index positive
    leftShape capacity position contextBound (leftBound index position)
  have rightAccept := sha384_source_path_accepts hash width context right depth index positive
    rightShape (by omega) rightPosition contextBound (rightBound index rightPosition)
  rw [←roots,←size] at rightAccept
  exact ⟨index,position,neq,sha384_merkle_conflicting_openings hash width _ context left.length index
    (left.getD index []) (right.getD index []) (sha384TreePath hash context left depth 0 index)
    (sha384TreePath hash context right depth 0 index) leftAccept rightAccept neq⟩

end NearCompression
