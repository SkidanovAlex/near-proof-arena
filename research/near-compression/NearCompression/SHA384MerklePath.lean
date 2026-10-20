import NearCompression.SHA384HashFrameDecoder
namespace NearCompression
abbrev SHA384ByteHash := List UInt8 → List UInt8

def sha384MerkleLeafTag : List UInt8 := [109, 101, 114, 107, 108, 101, 47, 108, 101, 97, 102]
def sha384MerkleNodeTag : List UInt8 := [109, 101, 114, 107, 108, 101, 47, 110, 111, 100, 101]
def sha384MerkleRootTag : List UInt8 := [109, 101, 114, 107, 108, 101, 47, 114, 111, 111, 116]

def sha384MerkleFold (hash : SHA384ByteHash) (context : List UInt8) :
    Nat → Nat → List UInt8 → List (List UInt8) → List UInt8
  | _,_,value,[] => value
  | level,index,value,sibling::rest =>
    let pair := if index%2=1 then [sibling,value] else [value,sibling]
    sha384MerkleFold hash context (level+1) (index/2)
      (hash (sha384HashFrame sha384MerkleNodeTag ([context,NearSpec.leN 8 level]++pair))) rest

def sha384MerkleRoot (hash : SHA384ByteHash) (context : List UInt8)
    (count index : Nat) (leaf : List UInt8) (path : List (List UInt8)) : List UInt8 :=
  let value:=hash (sha384HashFrame sha384MerkleLeafTag [context,NearSpec.leN 8 index,leaf])
  hash (sha384HashFrame sha384MerkleRootTag
    [context,NearSpec.leN 8 count,sha384MerkleFold hash context 1 index value path])

/-- Typed semantic equivalent of accepted verify_path shape checks. Explicit
u64 bounds cover the Python serialization calls; values are UInt8 lists. -/
def sha384VerifyPath (hash : SHA384ByteHash) (expected context : List UInt8)
    (count index : Nat) (leaf : List UInt8) (path : List (List UInt8)) : Bool :=
  decide (2≤count ∧ count=2^path.length ∧ index<count ∧ count<2^64 ∧
    context.length<2^64 ∧ leaf.length<2^64 ∧ expected.length=48 ∧
    ∀ sibling,sibling∈path → sibling.length=48) &&
    sha384MerkleRoot hash context count index leaf path==expected

private theorem fold_width (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (level index : Nat) (value : List UInt8) (path : List (List UInt8))
    (hv : value.length=48) : (sha384MerkleFold hash context level index value path).length=48 := by
  induction path generalizing level index value with
  | nil => exact hv
  | cons sibling rest ih => exact ih _ _ _ (width _)

private theorem node_frame_fits (context left right : List UInt8) (level : Nat)
    (hc : context.length<2^64) (hl : left.length=48) (hr : right.length=48) :
    SHA384HashFrameFits sha384MerkleNodeTag [context,NearSpec.leN 8 level,left,right] := by
  constructor
  · decide
  constructor
  · simp only [List.length_cons,List.length_nil];decide
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact hc
  · rw [NearSpec.leN_length];decide
  · rw [hl];decide
  · rw [hr];decide

private theorem three_frame_fits (tag context value : List UInt8) (n : Nat)
    (ht : tag.length<2^32) (hc : context.length<2^64) (hv : value.length<2^64) :
    SHA384HashFrameFits tag [context,NearSpec.leN 8 n,value] := by
  refine ⟨ht,?_,?_⟩
  · simp only [List.length_cons,List.length_nil];decide
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hc
    · rw [NearSpec.leN_length];decide
    · exact hv

/-- Exact byte inputs queried by the node fold, in execution order. -/
def sha384MerkleFoldQueries (hash : SHA384ByteHash) (context : List UInt8) :
    Nat → Nat → List UInt8 → List (List UInt8) → List (List UInt8)
  | _,_,_,[]=>[]
  | level,index,value,sibling::rest=>
    let pair:=if index%2=1 then [sibling,value] else [value,sibling]
    let message:=sha384HashFrame sha384MerkleNodeTag ([context,NearSpec.leN 8 level]++pair)
    message::sha384MerkleFoldQueries hash context (level+1) (index/2) (hash message) rest

def sha384MerklePathQueries (hash : SHA384ByteHash) (context : List UInt8)
    (count index : Nat) (leaf : List UInt8) (path : List (List UInt8)) : List (List UInt8) :=
  let message:=sha384HashFrame sha384MerkleLeafTag [context,NearSpec.leN 8 index,leaf]
  message::(sha384MerkleFoldQueries hash context 1 index (hash message) path ++
    [sha384HashFrame sha384MerkleRootTag [context,NearSpec.leN 8 count,
      sha384MerkleFold hash context 1 index (hash message) path]])

/-- Only equal-output queries actually occurring in the two paths matter. -/
def SHA384CrossQueryBinding (hash : SHA384ByteHash) (left right : List (List UInt8)) : Prop :=
  ∀ a,a∈left → ∀ b,b∈right → hash a=hash b → a=b

private theorem fold_query_binding (hash : SHA384ByteHash) (width : ∀ m,(hash m).length=48)
    (context : List UInt8) (hc : context.length<2^64) (leftPath rightPath : List (List UInt8))
    (lengths : leftPath.length=rightPath.length)
    (hlp : ∀ x,x∈leftPath → x.length=48) (hrp : ∀ x,x∈rightPath → x.length=48)
    (level index : Nat) (left right : List UInt8) (hl : left.length=48) (hr : right.length=48)
    (binding : SHA384CrossQueryBinding hash
      (sha384MerkleFoldQueries hash context level index left leftPath)
      (sha384MerkleFoldQueries hash context level index right rightPath))
    (eq : sha384MerkleFold hash context level index left leftPath=
      sha384MerkleFold hash context level index right rightPath) : left=right := by
  induction leftPath generalizing rightPath level index left right with
  | nil => cases rightPath <;> simp_all [sha384MerkleFold]
  | cons sibling rest ih =>
    cases rightPath with
    | nil => simp at lengths
    | cons other tail =>
      have sl:=hlp sibling (by simp)
      have sr:=hrp other (by simp)
      have step:=ih tail (by simpa using lengths)
        (by intro x hx;exact hlp x (by simp [hx]))
        (by intro x hx;exact hrp x (by simp [hx]))
        (level+1) (index/2) _ _ (width _) (width _)
        (by intro a ha b hb heq;exact binding a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) heq) eq
      have frameEq:=binding _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) step
      by_cases odd : index%2=1
      · simp only [ite_eq_left odd] at frameEq
        have fields:=(sha384_hash_frame_injective _ _ _ _
          (node_frame_fits context sibling left level hc sl hl)
          (node_frame_fits context other right level hc sr hr) frameEq).2
        simpa using congrArg (fun xs=>xs.getD 3 []) fields
      · simp only [ite_eq_right odd] at frameEq
        have fields:=(sha384_hash_frame_injective _ _ _ _
          (node_frame_fits context left sibling level hc hl sl)
          (node_frame_fits context right other level hc hr sr) frameEq).2
        simpa using congrArg (fun xs=>xs.getD 2 []) fields

/-- Finite supported binding: the only no-collision condition concerns the two
concrete verification query lists, not all possible hash inputs. -/
theorem sha384_merkle_query_binding (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : List UInt8) (count index : Nat)
    (left right : List UInt8) (leftPath rightPath : List (List UInt8))
    (hc : context.length<2^64) (hl : left.length<2^64) (hr : right.length<2^64)
    (lengths : leftPath.length=rightPath.length)
    (hlp : ∀ x,x∈leftPath → x.length=48) (hrp : ∀ x,x∈rightPath → x.length=48)
    (binding : SHA384CrossQueryBinding hash
      (sha384MerklePathQueries hash context count index left leftPath)
      (sha384MerklePathQueries hash context count index right rightPath))
    (roots : sha384MerkleRoot hash context count index left leftPath=
      sha384MerkleRoot hash context count index right rightPath) : left=right := by
  let lv:=hash (sha384HashFrame sha384MerkleLeafTag [context,NearSpec.leN 8 index,left])
  let rv:=hash (sha384HashFrame sha384MerkleLeafTag [context,NearSpec.leN 8 index,right])
  have lw:=fold_width hash width context 1 index lv leftPath (width _)
  have rw:=fold_width hash width context 1 index rv rightPath (width _)
  have rootEq:=binding _ (by simp [sha384MerklePathQueries]) _ (by simp [sha384MerklePathQueries]) roots
  have rootFields:=(sha384_hash_frame_injective _ _ _ _
    (three_frame_fits _ _ _ count (by decide) hc (by rw [lw];decide))
    (three_frame_fits _ _ _ count (by decide) hc (by rw [rw];decide)) rootEq).2
  have folded : sha384MerkleFold hash context 1 index lv leftPath=
      sha384MerkleFold hash context 1 index rv rightPath := by
    simpa using congrArg (fun xs=>xs.getD 2 []) rootFields
  have foldBinding : SHA384CrossQueryBinding hash
      (sha384MerkleFoldQueries hash context 1 index lv leftPath)
      (sha384MerkleFoldQueries hash context 1 index rv rightPath) := by
    intro a ha b hb heq
    apply binding a ?_ b ?_ heq
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hb)
  have leaves:=fold_query_binding hash width context hc leftPath rightPath lengths hlp hrp
    1 index lv rv (width _) (width _) foldBinding folded
  have leafEq:=binding _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) leaves
  have leafFields:=(sha384_hash_frame_injective _ _ _ _
    (three_frame_fits _ _ _ index (by decide) hc hl)
    (three_frame_fits _ _ _ index (by decide) hc hr) leafEq).2
  simpa using congrArg (fun xs=>xs.getD 2 []) leafFields

/-- A conflicting accepted opening yields a collision supported on the two
actual path-query lists. No global collision-existence shortcut is used. -/
theorem sha384_merkle_conflicting_openings (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (expected context : List UInt8)
    (count index : Nat) (left right : List UInt8) (leftPath rightPath : List (List UInt8))
    (acceptLeft : sha384VerifyPath hash expected context count index left leftPath=true)
    (acceptRight : sha384VerifyPath hash expected context count index right rightPath=true)
    (different : left≠right) :
    ∃ a,a∈sha384MerklePathQueries hash context count index left leftPath ∧
      ∃ b,b∈sha384MerklePathQueries hash context count index right rightPath ∧ a≠b ∧ hash a=hash b := by
  apply Classical.byContradiction
  intro noCollision
  have binding : SHA384CrossQueryBinding hash
      (sha384MerklePathQueries hash context count index left leftPath)
      (sha384MerklePathQueries hash context count index right rightPath) := by
    intro a ha b hb eq
    apply Classical.byContradiction
    intro neq
    exact noCollision ⟨a,ha,b,hb,neq,eq⟩
  simp only [sha384VerifyPath,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at acceptLeft acceptRight
  have lengths : leftPath.length=rightPath.length :=
    (Nat.pow_right_inj (by omega : 1<2)).mp (acceptLeft.1.2.1.symm.trans acceptRight.1.2.1)
  exact different (sha384_merkle_query_binding hash width context count index left right leftPath rightPath
    acceptLeft.1.2.2.2.2.1 acceptLeft.1.2.2.2.2.2.1 acceptRight.1.2.2.2.2.2.1 lengths
    acceptLeft.1.2.2.2.2.2.2.2 acceptRight.1.2.2.2.2.2.2.2 binding (acceptLeft.2.trans acceptRight.2.symm))
theorem sha384_merkle_fold_query_count (hash : SHA384ByteHash) (context : List UInt8)
    (level index : Nat) (value : List UInt8) (path : List (List UInt8)) :
    (sha384MerkleFoldQueries hash context level index value path).length=path.length := by
  induction path generalizing level index value with
  | nil => rfl
  | cons s rest ih => simpa only [sha384MerkleFoldQueries,List.length_cons] using congrArg Nat.succ (ih (level+1) (index/2) _)

theorem sha384_merkle_path_query_count (hash : SHA384ByteHash) (context : List UInt8)
    (count index : Nat) (leaf : List UInt8) (path : List (List UInt8)) :
    (sha384MerklePathQueries hash context count index leaf path).length=path.length+2 := by
  simp [sha384MerklePathQueries,sha384_merkle_fold_query_count,Nat.add_assoc]
end NearCompression
