import NearCompression.SHA384SharedCore

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
set_option maxRecDepth 65536

structure SharedPrefixLocal (count active tag table : Nat) (pub : List Fp) (tr : Trace Fp) : Prop where
  positive : 0<count
  countSmall : count<P
  heightSmall : tr.height table<P
  constr : ∀ r,r<tr.height table → ∀ e,e∈sharedPrefix active tag count → e.eval tr table r pub=0

variable {count active tag table : Nat} {pub : List Fp} {tr : Trace Fp}

theorem shared_prefix_boolean (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) : tr.cell table r active=0 ∨ tr.cell table r active=1 := by
  have hc := h.constr r hr (instructionBitConstraint active) (by simp [sharedPrefix])
  change tr.cell table r active*(tr.cell table r active + -(1:Fp))=0 at hc
  grind

theorem shared_prefix_first (h : SharedPrefixLocal count active tag table pub tr) :
    tr.cell table 0 active=1 ∧ tr.cell table 0 tag=0 := by
  have a := h.constr 0 (Nat.two_pow_pos _) (.mul .isFirst (sharedSub (.col active false) (.const 1))) (by simp [sharedPrefix])
  have t := h.constr 0 (Nat.two_pow_pos _) (.mul .isFirst (.col tag false)) (by simp [sharedPrefix])
  change (1:Fp)*(tr.cell table 0 active + -1)=0 at a
  change (1:Fp)*tr.cell table 0 tag=0 at t
  constructor <;> grind

theorem shared_prefix_no_restart (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r+1<tr.height table) (next : tr.cell table (r+1) active=1) :
    tr.cell table r active=1 := by
  have hc := h.constr r (by omega)
    (.mul .isTransition (.mul (.col active true) (sharedSub (.const 1) (.col active false)))) (by simp [sharedPrefix])
  simp only [sharedSub,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [next] at hc
  grind

theorem shared_prefix_tag_step (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r+1<tr.height table) (next : tr.cell table (r+1) active=1) :
    tr.cell table (r+1) tag=tr.cell table r tag+1 := by
  have hc := h.constr r (by omega)
    (.mul .isTransition (.mul (.col active true) (sharedSub (.col tag true) (.add (.col tag false) (.const 1))))) (by simp [sharedPrefix])
  simp only [sharedSub,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [next] at hc
  grind

theorem shared_prefix_tag (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) (on : tr.cell table r active=1) :
    tr.cell table r tag=Fp.ofNat r := by
  induction r with
  | zero => exact (shared_prefix_first h).2
  | succ r ih =>
    have prev := shared_prefix_no_restart h r hr on
    have old := ih (by omega) prev
    have step := shared_prefix_tag_step h r hr on
    rw [old] at step
    have cast : Fp.ofNat (r+1)=Fp.ofNat r+1 := Lean.Grind.Semiring.natCast_add _ _
    rw [cast]
    exact step

theorem shared_prefix_stop_last (r : Nat) (last : r+1=tr.height table)
    (on : tr.cell table r active=1) : (sharedStop active).eval tr table r pub=1 := by
  simp only [sharedStop,sharedSub,Expr.eval,Expr.evalWith,rowEnv,last,Bool.false_eq_true,ite_true,ite_false]
  rw [on]
  grind

theorem shared_prefix_stop_next (r : Nat) (next : r+1<tr.height table)
    (on : tr.cell table r active=1) (off : tr.cell table (r+1) active=0) :
    (sharedStop active).eval tr table r pub=1 := by
  simp only [sharedStop,sharedSub,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt next,
    Nat.ne_of_lt next,Bool.false_eq_true,ite_true,ite_false]
  rw [on,off]
  grind

theorem shared_prefix_stop_index (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) (on : tr.cell table r active=1)
    (stop : (sharedStop active).eval tr table r pub=1) : r+1=count := by
  have hc := h.constr r hr (.mul (sharedStop active) (sharedSub (.col tag false) (.const (count-1)))) (by simp [sharedPrefix])
  change (sharedStop active).eval tr table r pub*(tr.cell table r tag + -Fp.ofNat (count-1))=0 at hc
  rw [stop,shared_prefix_tag h r hr on] at hc
  have eq : Fp.ofNat r=Fp.ofNat (count-1) := by grind
  have natEq := congrArg Fp.toNat eq
  have bounds := h.heightSmall
  have bounds' := h.countSmall
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r<P),Nat.mod_eq_of_lt (by omega : count-1<P)] at natEq
  have pos := h.positive
  omega

theorem shared_prefix_required (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) (required : r<count) : tr.cell table r active=1 := by
  induction r with
  | zero => exact (shared_prefix_first h).1
  | succ r ih =>
    have on := ih (by omega) (by omega)
    rcases shared_prefix_boolean h (r+1) hr with off | result
    · have stop := shared_prefix_stop_next (pub:=pub) r hr on off
      have index := shared_prefix_stop_index h r (by omega) on stop
      omega
    · exact result

theorem shared_prefix_capacity (h : SharedPrefixLocal count active tag table pub tr) : count≤tr.height table := by
  by_cases fits : count≤tr.height table
  · exact fits
  · have pos : 0<tr.height table := Nat.two_pow_pos _
    have on := shared_prefix_required h (tr.height table-1) (by omega) (by omega)
    have stop := shared_prefix_stop_last (pub:=pub) (tr.height table-1) (by omega) on
    have index := shared_prefix_stop_index h (tr.height table-1) (by omega) on stop
    omega

theorem shared_prefix_bounded (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) (on : tr.cell table r active=1) : r<count := by
  have descend (k : Nat) : ∀ r,r<tr.height table → tr.height table-r≤k → tr.cell table r active=1 → r<count := by
    induction k with
    | zero => intro r hr distance on;omega
    | succ k ih =>
      intro r hr distance on
      by_cases last : r+1=tr.height table
      · have stop := shared_prefix_stop_last (pub:=pub) r last on
        have index := shared_prefix_stop_index h r hr on stop
        omega
      · have next : r+1<tr.height table := by omega
        rcases shared_prefix_boolean h (r+1) next with off | nextOn
        · have stop := shared_prefix_stop_next (pub:=pub) r next on off
          have index := shared_prefix_stop_index h r hr on stop
          omega
        · have result := ih (r+1) next (by omega) nextOn
          omega
  exact descend (tr.height table-r) r hr (by omega) on

theorem shared_prefix_exact (h : SharedPrefixLocal count active tag table pub tr)
    (r : Nat) (hr : r<tr.height table) : tr.cell table r active=1 ↔ r<count :=
  ⟨shared_prefix_bounded h r hr,shared_prefix_required h r hr⟩

theorem shared_prefix_unique (h : SharedPrefixLocal count active tag table pub tr)
    (r s : Nat) (hr : r<tr.height table) (hs : s<tr.height table)
    (onR : tr.cell table r active=1) (onS : tr.cell table s active=1)
    (eq : tr.cell table r tag=tr.cell table s tag) : r=s := by
  rw [shared_prefix_tag h r hr onR,shared_prefix_tag h s hs onS] at eq
  have natEq := congrArg Fp.toNat eq
  have bound := h.heightSmall
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r<P),Nat.mod_eq_of_lt (by omega : s<P)] using natEq

theorem sha384_shared_record_prefix (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) : SharedPrefixLocal 5 1 0 2 pub tr := by
  refine ⟨by decide,by decide,?_,?_⟩
  · have log := h.logBound 2 (by simp [sha384SharedAir])
    have upper : tr.log 2≤3 := log.2
    have power := Nat.pow_le_pow_right (by decide : 1≤2) upper
    change 2^tr.log 2<P
    unfold P
    omega
  · intro r hr e he
    exact h.constr 2 (by simp [sha384SharedAir]) r hr e (List.mem_append_left _ he)

theorem sha384_shared_endpoint_prefix (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) : SharedPrefixLocal 5 1665 1664 1 pub tr := by
  refine ⟨by decide,by decide,?_,?_⟩
  · have log := h.logBound 1 (by simp [sha384SharedAir])
    have upper : tr.log 1≤3 := log.2
    have power := Nat.pow_le_pow_right (by decide : 1≤2) upper
    change 2^tr.log 1<P
    unfold P
    omega
  · intro r hr e he
    exact h.constr 1 (by simp [sha384SharedAir]) r hr e (List.mem_append_right _ he)

end NearCompression
