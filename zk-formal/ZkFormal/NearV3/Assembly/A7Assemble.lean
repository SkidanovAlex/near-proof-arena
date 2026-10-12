import ZkFormal.NearV3.Assembly.A7Native
import ZkFormal.NearV3.Assembly.TrieA7Repl

/-!
# ZkFormal.NearV3.Assembly.A7Assemble — `A7RecordBound` from (B) and the per-segment facts

`A7Native.A7RecordBound tr r K` (`Σ_{τ≤K} (U (Fpre r τ) + U (Qrec tr r τ)) ≤ nodeA7Sum + valA7Sum + Σ a7S`)
follows from

* **(B)** `Σ_{τ≤K} U (Fpre r τ) ≤ Σ_n |ser n| + Σ_t len_t` (`recNode r + recVal r`), and
* **`SegOk tr r s`** for every `upsV3` segment `s` (instance `τ = (upsE s).tau`): a run `run` with
  - (C)+(D) `U (Fpre r τ) + outputByteCharge run + |sv τ| = U (Qrec tr r τ) + replacedCharge run + oldValCharge run`
    (`traceUpsert_replaced` on `Tpost r τ`, `U (Tpost r τ) = U (Fpre r τ)`),
  - (E) `outputByteCharge run + |sv τ| ≤ a7S s`, the `RPL` names of `s` weigh at most
    `replacedCharge run` (`wN`: `|ser n|` of the named record) and its `RPLV` names at most
    `oldValCharge run` (`wV`: `len` of the named value record),

with the `RPL` / `RPLV` balances (`A7Bound.a7_rpl_perm` / `a7_rplv_perm`) and the instance chain
(`RootChain.ups_count`: one segment per `τ ≤ K`): **`recordBound_of`**.
-/

namespace ZkFormal.NearV3.Assembly

namespace A7Assemble

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3
open NearSpec NearSpecV3 Render.UpsGen

/-- Weight of an `RPL` message `[n]`: the serialized length of node record `n`. -/
def wN (r : V3Records) (m : List Fp) : Nat := ((r.nodes.getD (m.headD 0).toNat default).v.ser false).length

/-- Weight of an `RPLV` message `[vid]`: the length of value record `vid`. -/
def wV (r : V3Records) (m : List Fp) : Nat := (r.values.getD (m.headD 0).toNat default).len

def recNode (r : V3Records) : Nat :=
  ((List.range r.nodes.length).map fun n => ((r.nodes.getD n default).v.ser false).length).sum

def recVal (r : V3Records) : Nat :=
  ((List.range r.values.length).map fun t => (r.values.getD t default).len).sum

/-- The per-segment facts (C)+(D)+(E). -/
def SegOk (tr : Trace Fp) (r : V3Records) (s : UpsSeg) : Prop :=
  ∃ run : TreeRun,
    unfoldedBytesT (LinkImplicit.Fpre r (UpsRows.upsE s).tau) + outputByteCharge run +
        (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)).length =
      unfoldedBytesT (A7Native.Qrec tr r (UpsRows.upsE s).tau) + TrieA7Repl.replacedCharge run +
        TrieA7Repl.oldValCharge run ∧
    outputByteCharge run + (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)).length ≤ s.a7S ∧
    (((s.a7Rpl).map Msg.toFp).map (wN r)).sum ≤ TrieA7Repl.replacedCharge run ∧
    (((s.a7Rplv).map Msg.toFp).map (wV r)).sum ≤ TrieA7Repl.oldValCharge run

/-! ## Generic sums -/

theorem weighted_add (S : Nat → Bool) (a : Nat → Nat) : ∀ L,
    ((List.range L).map fun n => (if S n then 1 else 2) * a n).sum +
      (((List.range L).filter S).map a).sum = 2 * ((List.range L).map a).sum
  | 0 => by simp
  | L + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.map_append, List.map_append,
      List.sum_append, List.sum_append, List.sum_append]
    have := weighted_add S a L
    by_cases h : S L = true
    · simp [List.filter, h]; omega
    · simp [List.filter, h]; omega

theorem count_map_tau {α : Type} (f : α → Nat) (K : Nat) (L : List α)
    (hc : ∀ τ, (L.map f).countP (· == τ) = if τ ≤ K then 1 else 0) :
    (L.map f).Perm (List.range (K + 1)) := by
  rw [List.perm_iff_count]
  intro τ
  have h1 : (L.map f).count τ = (L.map f).countP (· == τ) := List.count_eq_countP
  rw [h1, hc τ, List.count_range]
  split <;> split <;> omega

theorem sum_le_sum_list {α : Type} (f g : α → Nat) : ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h a (List.mem_cons_self ..)
    have := sum_le_sum_list f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem sum_flatMap_map {α β : Type} (g : α → List β) (F : β → Nat) : ∀ l : List α,
    ((l.flatMap g).map F).sum = (l.map fun a => ((g a).map F).sum).sum
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_map g F l]; rfl

/-! ## The assembly -/

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- **`A7RecordBound` from (B) and the per-segment facts.** -/
theorem recordBound_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r)
    (W : V3RecordsWf pub r) {K : Nat}
    (hcnt : ∀ τ, (r.ups.map UpsRows.upsE).countP (fun u => u.tau == τ) = if τ ≤ K then 1 else 0)
    (hB : ((List.range (K + 1)).map fun τ => unfoldedBytesT (LinkImplicit.Fpre r τ)).sum ≤
      recNode r + recVal r)
    (hS : ∀ s ∈ r.ups, SegOk tr r s) :
    A7Native.A7RecordBound tr r K := by
  unfold A7Native.A7RecordBound
  -- the segments' instances are `0..K`, once each
  have hp : (r.ups.map fun s => (UpsRows.upsE s).tau).Perm (List.range (K + 1)) := by
    apply count_map_tau
    intro τ
    have := hcnt τ
    rw [List.countP_map] at this ⊢
    rw [← this]
    rfl
  have hsum : ∀ F : Nat → Nat, (r.ups.map fun s => F (UpsRows.upsE s).tau).sum =
      ((List.range (K + 1)).map F).sum := by
    intro F
    have := (hp.map F).sum_nat
    rw [List.map_map] at this
    exact this
  -- the `RPL` / `RPLV` weights
  have hN : (r.ups.map fun s => (((s.a7Rpl).map Msg.toFp).map (wN r)).sum).sum =
      (((List.range r.nodes.length).filter r.rplN).map fun n => ((r.nodes.getD n default).v.ser false).length).sum := by
    have e1 : (r.ups.map fun s => (((s.a7Rpl).map Msg.toFp).map (wN r)).sum).sum =
        (((r.ups.flatMap UpsSeg.a7Rpl).map Msg.toFp).map (wN r)).sum := by
      rw [List.map_flatMap, sum_flatMap_map]
    rw [e1, ((A7Bound.a7_rpl_perm hH T).map (wN r)).sum_nat, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro n hn
    have hn' : n < r.nodes.length := List.mem_range.mp (List.mem_filter.mp hn).1
    have hP : n < ZkFormal.Algebra.P := by have := W.nodes.count; unfold ZkFormal.Algebra.P; omega
    simp [wN, Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hP]
  have hV : (r.ups.map fun s => (((s.a7Rplv).map Msg.toFp).map (wV r)).sum).sum =
      (((List.range r.values.length).filter r.rplV).map fun t => (r.values.getD t default).len).sum := by
    have e1 : (r.ups.map fun s => (((s.a7Rplv).map Msg.toFp).map (wV r)).sum).sum =
        (((r.ups.flatMap UpsSeg.a7Rplv).map Msg.toFp).map (wV r)).sum := by
      rw [List.map_flatMap, sum_flatMap_map]
    rw [e1, ((A7Bound.a7_rplv_perm hH T).map (wV r)).sum_nat, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    have ht' : t < r.values.length := List.mem_range.mp (List.mem_filter.mp ht).1
    have hvid : (r.values.getD t default).vid = t := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
      exact Link3.vid_small W.values ht'
    have hP : t < ZkFormal.Algebra.P := by
      have := (W.values.canon _ (List.getElem_mem ht')).1
      rw [Link3.vid_small W.values ht'] at this; exact this
    rw [List.getD_eq_getElem?_getD] at hvid
    simp [wV, Msg.toFp, Fp.toNat_ofNat, hvid, Nat.mod_eq_of_lt hP]
  -- per segment
  have hseg : (r.ups.map fun s => unfoldedBytesT (LinkImplicit.Fpre r (UpsRows.upsE s).tau) +
        unfoldedBytesT (A7Native.Qrec tr r (UpsRows.upsE s).tau) +
        (((s.a7Rpl).map Msg.toFp).map (wN r)).sum + (((s.a7Rplv).map Msg.toFp).map (wV r)).sum).sum ≤
      (r.ups.map fun s => 2 * unfoldedBytesT (LinkImplicit.Fpre r (UpsRows.upsE s).tau) + s.a7S).sum := by
    apply sum_le_sum_list
    intro s hs
    obtain ⟨run, h1, h2, h3, h4⟩ := hS s hs
    omega
  have hsplit : ∀ (l : List UpsSeg) (a b c d : UpsSeg → Nat),
      (l.map fun s => a s + b s + c s + d s).sum =
        (l.map a).sum + (l.map b).sum + (l.map c).sum + (l.map d).sum := by
    intro l a b c d
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  have hsplit2 : ∀ (l : List UpsSeg) (a b : UpsSeg → Nat),
      (l.map fun s => 2 * a s + b s).sum = 2 * (l.map a).sum + (l.map b).sum := by
    intro l a b
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [hsplit, hsplit2, hN, hV,
    hsum (fun τ => unfoldedBytesT (LinkImplicit.Fpre r τ)),
    hsum (fun τ => unfoldedBytesT (A7Native.Qrec tr r τ))] at hseg
  have hsum2 : ((List.range (K + 1)).map fun τ =>
      unfoldedBytesT (LinkImplicit.Fpre r τ) + unfoldedBytesT (A7Native.Qrec tr r τ)).sum =
      ((List.range (K + 1)).map fun τ => unfoldedBytesT (LinkImplicit.Fpre r τ)).sum +
      ((List.range (K + 1)).map fun τ => unfoldedBytesT (A7Native.Qrec tr r τ)).sum := by
    generalize List.range (K + 1) = l
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  have wn := weighted_add r.rplN (fun n => ((r.nodes.getD n default).v.ser false).length) r.nodes.length
  have wv := weighted_add r.rplV (fun t => (r.values.getD t default).len) r.values.length
  unfold recNode recVal at hB
  unfold nodeA7Sum valA7Sum
  rw [hsum2]
  omega

end

end A7Assemble

end ZkFormal.NearV3.Assembly
