import NearCompression.SHA384MerkleSource
import NearCompression.HeterogeneousSourcePair
namespace NearCompression
open NearSpec

def sha384FieldWords (values : List Nat) : Bytes := values.flatMap (leN 4)

def sha384ReadWords : Nat → Parser (List Nat)
  | 0 => fun bs=>some ([],bs)
  | n+1 => fun bs=>do
      let (value,rest) ← readLE 4 bs
      let (values,rest) ← sha384ReadWords n rest
      pure (value::values,rest)

theorem sha384_field_words_length (values : List Nat) :
    (sha384FieldWords values).length=4*values.length := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    simp only [sha384FieldWords,List.flatMap_cons,List.length_append,leN_length,List.length_cons] at *
    omega

theorem sha384_field_words_read (values : List Nat) (rest : Bytes)
    (canonical : ∀v,v∈values → v<2013265921) :
    sha384ReadWords values.length (sha384FieldWords values++rest)=some (values,rest) := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    have bound : v<256^4 := by have hv:=canonical v (by simp);omega
    have tail:=ih (by intro x hx;exact canonical x (by simp [hx]))
    unfold sha384FieldWords at tail
    simp only [sha384FieldWords,List.flatMap_cons,List.length_cons,List.append_assoc,sha384ReadWords]
    rw [readLE_append 4 v _ bound]
    dsimp only [Bind.bind,Option.bind]
    rw [tail]
    rfl

theorem sha384_field_words_injective (left right : List Nat)
    (hl : ∀v,v∈left → v<2013265921) (hr : ∀v,v∈right → v<2013265921)
    (encoded : sha384FieldWords left=sha384FieldWords right) : left=right := by
  have len:=congrArg List.length encoded
  rw [sha384_field_words_length,sha384_field_words_length] at len
  have lengths : left.length=right.length := by omega
  have a:=sha384_field_words_read left [] hl
  have b:=sha384_field_words_read right [] hr
  simp only [List.append_nil] at a b
  rw [encoded,lengths,b] at a
  exact (congrArg Prod.fst (Option.some.inj a)).symm

/-- Concrete lane-major adjacent plus/minus slots read by first=True. -/
def sha384SourceWordPairs {K : Type} [Lean.Grind.Field K] (values : List Nat) : List (K×K) :=
  (List.range (values.length/2)).map (fun lane=>
    (@Nat.cast K Lean.Grind.Semiring.natCast (values.getD (2*lane) 0),
      @Nat.cast K Lean.Grind.Semiring.natCast (values.getD (2*lane+1) 0)))

/-- Byte authentication plus canonical LE32 decoding binds the entire word
vector. The fixed source is explicitly supplied; adversarial-root extraction is
not part of this theorem. -/
theorem sha384_fixed_source_words (hash : SHA384ByteHash) (width : ∀m,(hash m).length=48)
    (context : Bytes) (source : List (List Nat)) (depth index : Nat)
    (positive : 0<depth) (shape : source.length=2^depth) (capacity : source.length<2^64)
    (position : index<source.length) (contextBound : context.length<2^64)
    (leafBound : (sha384FieldWords (source.getD index [])).length<2^64)
    (sourceCanonical : ∀v,v∈source.getD index [] → v<2013265921)
    (claimed : List Nat) (claimedCanonical : ∀v,v∈claimed → v<2013265921)
    (path : List Bytes)
    (accepted : sha384VerifyPath hash (sha384SourceRoot hash context (source.map sha384FieldWords) depth)
      context source.length index (sha384FieldWords claimed) path=true) :
    claimed=source.getD index [] ∨
      ∃a,a∈sha384MerklePathQueries hash context source.length index (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash context source.length index (sha384FieldWords (source.getD index []))
          (sha384TreePath hash context (source.map sha384FieldWords) depth 0 index) ∧ a≠b ∧ hash a=hash b := by
  have get : (source.map sha384FieldWords).getD index []=sha384FieldWords (source.getD index []) := by
    simp [List.getD,position]
  have result:=sha384_fixed_source_opening hash width context (source.map sha384FieldWords) depth index
    positive (by simpa using shape) (by simpa using capacity) (by simpa using position) contextBound
    (by simpa only [get] using leafBound) (sha384FieldWords claimed) path (by simpa using accepted)
  simp only [List.length_map,get] at result
  rcases result with equal | collision
  · exact Or.inl (sha384_field_words_injective claimed (source.getD index []) claimedCanonical sourceCanonical equal)
  · exact Or.inr collision
/-- The concrete first-stage projected beta pair is authenticated jointly
across all lanes. Index selection is the actual sample mod2d expression.
Coefficients may be verifier-derived/adaptive; this is byte binding only. -/
theorem sha384_fixed_source_projected_pair {K : Type} [Lean.Grind.Field K] (beta : List K) (k d sample : Nat)
    (hash : SHA384ByteHash) (width : ∀m,(hash m).length=48)
    (context : Bytes) (source : List (List Nat)) (depth : Nat)
    (positive : 0<depth) (shape : source.length=2^depth) (capacity : source.length<2^64)
    (position : (sample%(2*d))<source.length) (contextBound : context.length<2^64)
    (leafBound : (sha384FieldWords (source.getD (sample%(2*d)) [])).length<2^64)
    (sourceCanonical : ∀v,v∈source.getD (sample%(2*d)) [] → v<2013265921)
    (claimed : List Nat) (claimedCanonical : ∀v,v∈claimed → v<2013265921)
    (path : List Bytes)
    (accepted : sha384VerifyPath hash (sha384SourceRoot hash context (source.map sha384FieldWords) depth)
      context source.length (sample%(2*d)) (sha384FieldWords claimed) path=true) :
    projectedBetaPair k d sample beta (sha384SourceWordPairs claimed)=
      projectedBetaPair k d sample beta (sha384SourceWordPairs (source.getD (sample%(2*d)) [])) ∨
      ∃a,a∈sha384MerklePathQueries hash context source.length (sample%(2*d)) (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash context source.length (sample%(2*d)) (sha384FieldWords (source.getD (sample%(2*d)) []))
          (sha384TreePath hash context (source.map sha384FieldWords) depth 0 (sample%(2*d))) ∧ a≠b ∧ hash a=hash b := by
  have result:=sha384_fixed_source_words hash width context source depth (sample%(2*d)) positive shape capacity
    position contextBound leafBound sourceCanonical claimed claimedCanonical path accepted
  rcases result with equal | collision
  · exact Or.inl (congrArg (fun values=>projectedBetaPair k d sample beta (sha384SourceWordPairs values)) equal)
  · exact Or.inr collision

end NearCompression
