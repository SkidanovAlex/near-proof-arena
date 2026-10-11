import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyTraffic
import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.Near.Extract.BusCount

/-!
# `acctV3` with the empty-chunk repair at the `nearAirV3` cap (`acctTableV3`, table 17)

`AccountEmptySound` proves the empty-or-old split for `AccountEmpty.table` at its definitional
cap 17.  The split never uses the height bound, so it holds at every cap; here it is restated
for `{AccountEmpty.table with maxLog := cap}` and for `acctTableV3` (cap 19):

* `acctV3_empty_or_old`: a locally legal table 17 is either **silent** (every bus count `0`:
  no account read, the empty-chunk case) or locally legal for the original `acctV3`
  constraints at cap 19 (first row active), to which the cap-parametric view
  `acctV3_view_at` applies;
* `old_local_at`: the original constraints imply the repaired ones (completeness transfer);
* `empty_local_at`: the all-zero trace (`emptyTrace`, height 2) is locally legal and silent;
* `AcctV3WfE cap as := as = [] ∨ AcctV3WfAt cap as` and `acctV3E_view_at`: the two-branch
  view (`[]` with the empty traffic, or the old view).
-/

namespace ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {cap : Nat}

theorem con_at (h : TableLocal {table with maxLog := cap} tr tt pub) {r : Nat}
    (hr : r < tr.height tt) {e : Expr} (he : e ∈ Acct.constraints) (hne : e ≠ oldFirst) :
    e.eval tr tt r pub = 0 := by
  have hh := h.constr r hr (replaceFirst e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  simpa only [replaceFirst, if_neg hne] using hh

theorem first_active_at (h : TableLocal {table with maxLog := cap} tr tt pub)
    (ha : tr.cell tt 0 Acct.act = 1) : TableLocal {AcctV3.table with maxLog := cap} tr tt pub := by
  refine ⟨h.log_ge, h.log_le, ?_, h.bits⟩
  intro r hr e he
  change e ∈ Acct.constraints at he
  by_cases heq : e = oldFirst
  · subst e
    by_cases hz : r = 0
    · subst r
      have hh := h.constr 0 hr newFirst (List.mem_map.mpr ⟨oldFirst,
        by simp [oldFirst, Acct.constraints], by simp [replaceFirst]⟩)
      simp only [newFirst, eval_mul, eval_isFirst, eval_sub, eval_c, if_pos rfl, ha] at hh
      simp only [oldFirst, eval_mul, eval_isFirst, eval_not, eval_c, if_pos rfl]
      grind
    · simp only [oldFirst, eval_mul, eval_isFirst, if_neg hz]
      grind
  · exact con_at h hr he heq

/-- The original `acctV3` constraints imply the repaired ones (at any cap). -/
theorem old_local_at (h : TableLocal {AcctV3.table with maxLog := cap} tr tt pub) :
    TableLocal {table with maxLog := cap} tr tt pub := by
  refine ⟨h.log_ge, h.log_le, ?_, h.bits⟩
  intro r hr e he
  obtain ⟨e, hold, rfl⟩ := List.mem_map.mp he
  by_cases heq : e = oldFirst
  · subst e
    change newFirst.eval tr tt r pub = 0
    by_cases hz : r = 0
    · subst r
      have hf := AcctV3Proof.row0 h hr
      have ha := ((AcctV3Proof.rowFacts h hr).1 hf).1
      simp only [newFirst, eval_mul, eval_isFirst, eval_sub, eval_c, if_pos rfl, ha, hf]
      grind
    · simp only [newFirst, eval_mul, eval_isFirst, if_neg hz]
      grind
  · simp only [replaceFirst, if_neg heq]
    exact h.constr r hr e hold

theorem inactive_all_at (h : TableLocal {table with maxLog := cap} tr tt pub)
    (ha : tr.cell tt 0 Acct.act = 0) : ∀ r, tr.cell tt r Acct.act = 0 ∨ tr.height tt ≤ r := by
  intro r
  induction r with
  | zero => exact Or.inl ha
  | succ r ih =>
    by_cases hr : r + 1 < tr.height tt
    · have hc : tr.cell tt r Acct.act = 0 := ih.resolve_right (by omega)
      have hh := con_at h (by omega : r < tr.height tt)
        (e := mul3 .isTransition (Dsl.not (c Acct.act)) (n Acct.act))
        (by simp [Acct.constraints]) (by decide +kernel)
      simp only [eval_mul3, eval_isTransition, eval_not, eval_c, eval_n,
        if_neg (by omega : ¬r + 1 = tr.height tt), Nat.mod_eq_of_lt hr, hc] at hh
      exact Or.inl (by grind)
    · exact Or.inr (by omega)

theorem inactive_gates_at (h : TableLocal {table with maxLog := cap} tr tt pub)
    (ha : tr.cell tt 0 Acct.act = 0) {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r Acct.act = 0 ∧ tr.cell tt r Acct.af = 0 ∧ tr.cell tt r Acct.gS = 0 := by
  have hc := (inactive_all_at h ha r).resolve_right (by omega)
  have hf := con_at h hr (e := .mul (c Acct.af) (Dsl.not (c Acct.act)))
    (by simp [Acct.constraints]) (by decide +kernel)
  have hg := con_at h hr (e := sub (c Acct.gS) (.mul (c Acct.act) (c Acct.lo8)))
    (by simp [Acct.constraints]) (by decide +kernel)
  simp only [eval_mul, eval_not, eval_c, eval_sub, hc] at hf hg
  exact ⟨hc, by grind, by grind⟩

/-- **Empty-or-old at any cap**: silent (every bus count `0`) or the original `acctV3` at the
same cap. -/
theorem empty_or_old_at (h : TableLocal {table with maxLog := cap} tr tt pub) :
    (∀ b sd m, tableBusCount table.interactions tr tt pub b sd m = 0) ∨
      TableLocal {AcctV3.table with maxLog := cap} tr tt pub := by
  have hp : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have hb := con_at h hp (e := Dsl.bool (c Acct.act)) (by simp [Acct.constraints]) (by decide +kernel)
  simp only [eval_bool, eval_c] at hb
  rcases bool_cases hb with hz | ho
  · left
    intro b sd m
    rw [tableBusCount_eq]
    have hnil : (List.range (tr.height tt)).flatMap
        (fun r => rowTraffic table.interactions tr tt r pub b sd) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      obtain ⟨h1, h2, h3⟩ := inactive_gates_at h hz (List.mem_range.mp hr)
      exact zero_gate_traffic h1 h2 h3 b sd
    rw [hnil]
    rfl
  · exact Or.inr (first_active_at h ho)

/-- The all-zero trace (height 2) is locally legal for the repaired table at every cap `≥ 1`. -/
theorem empty_local_at (hc : 1 ≤ cap) (tt : Nat) (pub : List Fp) :
    TableLocal {table with maxLog := cap} emptyTrace tt pub := by
  have h := empty_local tt pub
  exact ⟨h.log_ge, by change 1 ≤ cap; exact hc, h.constr, h.bits⟩

theorem acctV3Traffic_nil_sends (b : Nat) : (acctV3Traffic []).sends b = [] := by
  simp only [acctV3Traffic, acctV3Sends, List.flatMap_nil, List.map_nil, ite_self]

theorem acctV3Traffic_nil_recvs (b : Nat) : (acctV3Traffic []).recvs b = [] := by
  simp only [acctV3Traffic, acctRecvs, List.flatMap_nil, ite_self]

/-- The all-zero trace emits nothing (exact traffic: the empty traffic). -/
theorem empty_traffic_exact (tt : Nat) (pub : List Fp) :
    TableTraffic table.interactions emptyTrace tt pub (acctV3Traffic []) := by
  intro b m
  have hz : ∀ sd, tableBusCount table.interactions emptyTrace tt pub b sd m = 0 := by
    intro sd
    rw [tableBusCount_eq]
    have hnil : (List.range (emptyTrace.height tt)).flatMap
        (fun r => rowTraffic table.interactions emptyTrace tt r pub b sd) = [] :=
      List.flatMap_eq_nil_iff.mpr fun r _ => empty_traffic tt r pub b sd
    rw [hnil]
    rfl
  rw [hz true, hz false, acctV3Traffic_nil_sends, acctV3Traffic_nil_recvs]
  exact ⟨rfl, rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra
open ZkFormal.NearV3.Rcpt.Candidates

/-- The two-branch account view: no account (the empty chunk) or the original cap-`cap` view. -/
def AcctV3WfE (cap : Nat) (as : List AcctV) : Prop := as = [] ∨ AcctV3WfAt cap as

/-- **The repaired account view at a cap `≤ 22`**: `[]` with the empty traffic (silent table) or
the original records `AcctV3WfAt cap` with their exact traffic. -/
theorem acctV3E_view_at (cap : Nat) (hcap : cap ≤ 22) (tr : Trace Fp) (pub : List Fp) (tt : Nat)
    (hL : TableLocal {AccountEmpty.table with maxLog := cap} tr tt pub) :
    ∃ as, AcctV3WfE cap as ∧ TableTraffic AcctV3.interactions tr tt pub (acctV3Traffic as) := by
  rcases AccountEmpty.empty_or_old_at hL with hz | ho
  · refine ⟨[], Or.inl rfl, fun b m => ?_⟩
    have h1 := hz b true m
    have h0 := hz b false m
    change tableBusCount AcctV3.interactions tr tt pub b true m = 0 at h1
    change tableBusCount AcctV3.interactions tr tt pub b false m = 0 at h0
    rw [h1, h0, AccountEmpty.acctV3Traffic_nil_sends, AccountEmpty.acctV3Traffic_nil_recvs]
    exact ⟨rfl, rfl⟩
  · obtain ⟨as, hw, ht⟩ := ZkFormal.NearV3.acctV3_view_at cap hcap tr pub tt ho
    exact ⟨as, Or.inr hw, ht⟩

end ZkFormal.NearV3

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra
open ZkFormal.NearV3.Rcpt.Candidates

/-- **`acctV3` soundness split at the `nearAirV3` cap 19**: silent (no account read) or the
original `acctV3` table at cap 19. -/
theorem acctV3_empty_or_old (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal acctTableV3 tr t pub) :
    (∀ b sd m, tableBusCount acctTableV3.interactions tr t pub b sd m = 0) ∨
      TableLocal {ZkFormal.NearV3.AcctV3.table with maxLog := 19} tr t pub :=
  AccountEmpty.empty_or_old_at h

end ZkFormal.NearV3.Assembly
