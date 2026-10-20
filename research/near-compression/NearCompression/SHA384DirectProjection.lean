import NearCompression.SHA384DirectRouting
import NearCompression.SHA384BatchedSoundness

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The retained compression tables read no public cells. Their parameter only
changes constants, so the finite certificate is independent of message length. -/
theorem sha384_direct_core_no_public (n : Nat) :
    ∀ t∈[sha384BatchCoreTable n,sha384EndpointTable n],∀ e∈t.exprs,e.pubBound=0 := by
  have certificate : ([sha384BatchCoreTable n,sha384EndpointTable n].all
      (fun t=>t.exprs.all (fun e=>decide (e.pubBound=0))))=true := by
    change ([sha384BatchCoreTable 0,sha384EndpointTable 0].all
      (fun t=>t.exprs.all (fun e=>decide (e.pubBound=0))))=true
    decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using certificate

theorem sha384_direct_eval_public (e : Expr) (bound : e.pubBound=0)
    (tr : Trace Fp) (t r : Nat) (a b : List Fp) : e.eval tr t r a=e.eval tr t r b := by
  induction e with
  | pub i => simp [Expr.pubBound] at bound
  | add x y hx hy =>
    have bounds : x.pubBound=0 ∧ y.pubBound=0 := by simpa [Expr.pubBound] using bound
    change x.eval tr t r a+y.eval tr t r a=x.eval tr t r b+y.eval tr t r b
    rw [hx bounds.1,hy bounds.2]
  | mul x y hx hy =>
    have bounds : x.pubBound=0 ∧ y.pubBound=0 := by simpa [Expr.pubBound] using bound
    change x.eval tr t r a*y.eval tr t r a=x.eval tr t r b*y.eval tr t r b
    rw [hx bounds.1,hy bounds.2]
  | neg x hx =>
    change -x.eval tr t r a = -x.eval tr t r b
    rw [hx bound]
  | _ => rfl

private theorem interaction_public (i : Interaction)
    (bound : ∀e∈i.exprs,e.pubBound=0) (tr : Trace Fp) (t r : Nat) (a b : List Fp) :
    i.msgVal tr t r a=i.msgVal tr t r b ∧ i.multNat tr t r a=i.multNat tr t r b := by
  constructor
  · apply List.map_congr_left
    intro e he
    exact sha384_direct_eval_public e (bound e (List.mem_append_right _ he)) tr t r a b
  · unfold Interaction.multNat
    have hb : ∀e∈i.mult,e.eval tr t r a=e.eval tr t r b :=
      fun e he=>sha384_direct_eval_public e (bound e (List.mem_append_left _ he)) tr t r a b
    have go (es : List Expr) (hb : ∀e∈es,e.eval tr t r a=e.eval tr t r b) (k : Nat) :
        Interaction.multNat.go tr t r a es k=Interaction.multNat.go tr t r b es k := by
      induction es generalizing k with
      | nil => rfl
      | cons e es ih =>
        simp only [Interaction.multNat.go]
        rw [hb e (by simp),ih (fun x hx=>hb x (by simp [hx]))]
    exact go i.mult hb 0

private theorem fold_congr {α β : Type} (xs : List α) (f g : α→β→β) (init : β)
    (h : ∀x∈xs,∀acc,f x acc=g x acc) : xs.foldr f init=xs.foldr g init := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

theorem sha384_direct_table_count_public (table : Table)
    (bound : ∀e∈table.exprs,e.pubBound=0) (tr : Trace Fp) (t : Nat)
    (a b : List Fp) (bus : Nat) (side : Bool) (msg : List Fp) :
    tableBusCount table.interactions tr t a bus side msg=
      tableBusCount table.interactions tr t b bus side msg := by
  have eq (r : Nat) (i : Interaction) (hi : i∈table.interactions) :=
    interaction_public i (fun e he=>bound e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,he⟩))) tr t r a b
  unfold tableBusCount
  apply fold_congr
  intro r hr acc
  apply fold_congr
  intro i hi acc'
  rw [(eq r i hi).1,(eq r i hi).2]

/-- Exact natural-count substitution removes the input sender table. This
structural lemma is used with canonical public-record count proofs; it does
not assert that a matching sender alone suffices. The trace is unchanged,
but the target AIR reads only its first two tables. -/
theorem sha384_direct_project (n : Nat) (fixed : List (Nat × Nat))
    (pub expanded : List Fp) (tr : Trace Fp)
    (holds : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (fits : pubFit (sha384BatchedAir n) expanded=true)
    (counts : ∀ bus side msg,
      pubCount (sha384BatchedAir n) expanded bus side msg=
        tableBusCount (sha384DirectInputTable n fixed).interactions tr 2 pub bus side msg+
        pubCount (sha384DirectInputAir n fixed) pub bus side msg) :
    HoldsP (sha384BatchedAir n) expanded tr := by
  have tableEq (t : Nat) (ht : t<(sha384BatchedAir n).tables.length) :
      (sha384BatchedAir n).tables[t]=(sha384DirectInputAir n fixed).tables[t]'(by
        simp only [sha384BatchedAir,List.length_cons,List.length_nil] at ht
        simp only [sha384DirectInputAir,List.length_cons,List.length_nil];omega) := by
    have cases : t=0 ∨ t=1 := by simpa [sha384BatchedAir] using (show t=0 ∨ t=1 by
      simp only [sha384BatchedAir,List.length_cons,List.length_nil] at ht;omega)
    rcases cases with rfl|rfl <;> rfl
  have oldBound (t : Nat) (ht : t<(sha384BatchedAir n).tables.length) :
      ∀e∈(sha384BatchedAir n).tables[t].exprs,e.pubBound=0 :=
    sha384_direct_core_no_public n _ (List.getElem_mem ht)
  constructor
  · intro t ht
    rw [tableEq t ht]
    exact holds.logBound t _
  · intro t ht r hr e he
    rw [sha384_direct_eval_public e (oldBound t ht e (List.mem_append_left _ he)) tr t r expanded pub]
    apply holds.constr t _ r hr e
    rwa [←tableEq t ht]
  · intro t ht r hr i hi e he
    have hb := oldBound t ht e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
    rw [sha384_direct_eval_public e hb tr t r expanded pub]
    apply holds.bits t _ r hr i
    · rwa [←tableEq t ht]
    · exact he
  · exact fits
  · intro bus msg
    have balance := holds.balance bus msg
    have first := sha384_direct_table_count_public (sha384BatchCoreTable n)
      (sha384_direct_core_no_public n _ (by simp)) tr 0 expanded pub bus true msg
    have second := sha384_direct_table_count_public (sha384EndpointTable n)
      (sha384_direct_core_no_public n _ (by simp)) tr 1 expanded pub bus true msg
    have first' := sha384_direct_table_count_public (sha384BatchCoreTable n)
      (sha384_direct_core_no_public n _ (by simp)) tr 0 expanded pub bus false msg
    have second' := sha384_direct_table_count_public (sha384EndpointTable n)
      (sha384_direct_core_no_public n _ (by simp)) tr 1 expanded pub bus false msg
    rw [counts bus true msg,counts bus false msg]
    simp only [busCount,sha384BatchedAir,sha384DirectInputAir,busCount.go,
      Nat.zero_add,Nat.add_zero,show 1+1=2 from rfl] at balance ⊢
    rw [first,second,first',second']
    omega

/-- Canonical byte interpretation of the actual input row. -/
def sha384DirectMessageBytes (n : Nat) (pub : List Fp) (tr : Trace Fp) : List UInt8 :=
  (sha384CommittedMessage n pub tr).map UInt8.ofNat

theorem sha384_direct_message_bytes_length (n : Nat) (pub : List Fp) (tr : Trace Fp) :
    (sha384DirectMessageBytes n pub tr).length=n := by
  simp only [sha384DirectMessageBytes,List.length_map,sha384_committed_message_length]

theorem sha384_direct_message_bytes_exact (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (holds : HoldsP (sha384DirectInputAir n fixed) pub tr) :
    (sha384DirectMessageBytes n pub tr).map UInt8.toNat=sha384CommittedMessage n pub tr := by
  simp only [sha384DirectMessageBytes,sha384CommittedMessage,List.map_map]
  apply List.map_congr_left
  intro i hi
  have bound := sha384_direct_message_byte_bound n fixed pub tr holds i (List.mem_range.mp hi)
  rw [sha384_committed_message_byte n pub tr i (List.mem_range.mp hi)] at bound
  dsimp only [Function.comp_def]
  rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt bound]

end NearCompression
