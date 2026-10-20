import NearCompression.SHA384HashFraming
import NearCompression.PowerTwoRootOrder
namespace NearCompression
set_option maxRecDepth 65536
open NearSpec ZkFormal.Algebra

def sha384PackingPrefix : Bytes := [78, 69, 65, 82, 45, 80, 81, 51, 56, 52, 45, 82, 83, 45, 80, 65, 67, 75, 69, 68, 45, 86, 50, 47, 114, 111, 119, 45, 108, 111, 119, 45, 99, 111, 108, 117, 109, 110, 45, 104, 105, 103, 104, 45, 109, 111, 98, 105, 117, 115, 47, 99, 111, 110, 115, 101, 99, 117, 116, 105, 118, 101, 45, 99, 111, 108, 117, 109, 110, 45, 103, 114, 111, 117, 112, 115, 47, 122, 101, 114, 111, 45, 112, 97, 100, 45, 99, 111, 108, 117, 109, 110, 115, 45, 97, 110, 100, 45, 108, 100, 101, 52, 47, 110, 97, 116, 117, 114, 97, 108, 45, 100, 111, 109, 97, 105, 110, 47, 108, 97, 110, 101, 45, 109, 97, 106, 111, 114, 45, 112, 97, 105, 114, 115, 47, 108, 101, 45, 117, 51, 50]

def sha384PackingFields (n width p : Nat) : List Nat :=
  [2013265921,2^n,width,2^p,(width+2^p-1)/2^p,2^(n+p+2),(nativeBabyBearRoot (n+p+2)).toNat]

def sha384U64Words (values : List Nat) : Bytes := values.flatMap (leN 8)

def sha384PackingContext (n width p : Nat) : Bytes :=
  sha384PackingPrefix++sha384U64Words (sha384PackingFields n width p)

def SHA384PackingFits (n width p : Nat) : Prop :=
  1≤n ∧ n≤25 ∧ 0<width ∧ width≤2^20 ∧ p≤20 ∧ n+p+2≤27

def sha384ReadU64s : Nat → Parser (List Nat)
  | 0=>fun bs=>some ([],bs)
  | n+1=>fun bs=>do
    let (v,rest) ← readLE 8 bs
    let (values,rest) ← sha384ReadU64s n rest
    pure (v::values,rest)

theorem sha384_packing_field_bounds (n width p : Nat) (fits : SHA384PackingFits n width p) :
    ∀v,v∈sha384PackingFields n width p → v<2^64 := by
  have rowBound : 2^n≤2^25 := Nat.pow_le_pow_right (by omega) fits.2.1
  have packBound : 2^p≤2^20 := Nat.pow_le_pow_right (by omega) fits.2.2.2.2.1
  have domainBound : 2^(n+p+2)≤2^27 := Nat.pow_le_pow_right (by omega) fits.2.2.2.2.2
  have laneBound := Nat.div_le_self (width+2^p-1) (2^p)
  have rootBound := (nativeBabyBearRoot (n+p+2)).toNat_lt
  change (nativeBabyBearRoot (n+p+2)).toNat<2013265921 at rootBound
  intro v hv
  simp only [sha384PackingFields,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold SHA384PackingFits at fits <;> omega

theorem sha384_u64_words_length (values : List Nat) :
    (sha384U64Words values).length=8*values.length := by
  induction values with
  | nil=>rfl
  | cons v vs ih=>simp only [sha384U64Words,List.flatMap_cons,List.length_append,leN_length,List.length_cons] at *;omega

theorem sha384_u64_words_read (values : List Nat) (rest : Bytes)
    (fits : ∀v,v∈values → v<2^64) :
    sha384ReadU64s values.length (sha384U64Words values++rest)=some (values,rest) := by
  induction values with
  | nil=>rfl
  | cons v vs ih=>
    have bound : v<256^8 := fits v (by simp)
    have tail:=ih (by intro x hx;exact fits x (by simp [hx]))
    unfold sha384U64Words at tail
    simp only [sha384U64Words,List.flatMap_cons,List.length_cons,List.append_assoc,sha384ReadU64s]
    rw [readLE_append 8 v _ bound]
    dsimp only [Bind.bind,Option.bind]
    rw [tail]
    rfl

theorem sha384_packing_context_length (n width p : Nat) :
    (sha384PackingContext n width p).length=197 := by
  rw [sha384PackingContext,List.length_append,sha384_u64_words_length]
  rfl

theorem sha384_packing_context_fields (n width p : Nat) (fits : SHA384PackingFits n width p) :
    sha384ReadU64s 7 ((sha384PackingContext n width p).drop sha384PackingPrefix.length)=
      some (sha384PackingFields n width p,[]) := by
  simp only [sha384PackingContext,List.drop_append_length]
  have decoded:=sha384_u64_words_read (sha384PackingFields n width p) [] (sha384_packing_field_bounds n width p fits)
  simpa only [List.append_nil,sha384PackingFields,List.length_cons,List.length_nil] using decoded

theorem sha384_packing_context_injective (n w p n' w' p' : Nat)
    (fits : SHA384PackingFits n w p) (fits' : SHA384PackingFits n' w' p')
    (same : sha384PackingContext n w p=sha384PackingContext n' w' p') :
    n=n' ∧ w=w' ∧ p=p' := by
  have decoded:=congrArg (fun bytes=>sha384ReadU64s 7 (bytes.drop sha384PackingPrefix.length)) same
  rw [sha384_packing_context_fields _ _ _ fits,sha384_packing_context_fields _ _ _ fits'] at decoded
  have fields:=congrArg Prod.fst (Option.some.inj decoded)
  have rows:=congrArg (fun xs=>xs.getD 1 0) fields
  have columns:=congrArg (fun xs=>xs.getD 2 0) fields
  have packing:=congrArg (fun xs=>xs.getD 3 0) fields
  simp only [sha384PackingFields,List.getD_cons_succ,List.getD_cons_zero] at rows columns packing
  exact ⟨(Nat.pow_right_inj (by omega : 1<2)).mp rows,columns,(Nat.pow_right_inj (by omega : 1<2)).mp packing⟩

theorem sha384_packing_root_field (n width p : Nat) :
    (sha384PackingFields n width p).getD 6 0=440564289^((2^27)/(2^(n+p+2)))%2013265921 := by
  exact native_babybear_root_value (n+p+2)
end NearCompression
