import NearCompression.SHA384CommittedInput

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
set_option maxRecDepth 65536

theorem sha384_committed_pad_constraint (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 3) (e : Expr)
    (he : e∈(sha384CommittedPadTable n).constraints) : e.eval tr 3 r pub=0 :=
  h.constr 3 (by simp [sha384CommittedInputAir]) r hr e he

theorem sha384_committed_pad_first (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (b : Nat) (hb : b<sha384PaddedLength n/128) :
    tr.cell 3 0 (1024+b)=if b=0 then 1 else 0 := by
  have hc:=sha384_committed_pad_constraint n fixed pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add (sha384PadSelect b) (.neg (.const (if b=0 then 1 else 0)))))
    (by simp only [sha384CommittedPadTable,List.mem_append];exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨b,List.mem_range.mpr hb,rfl⟩))))
  by_cases zero : b=0
  · subst b;change (1:Fp)*(tr.cell 3 0 (1024+0)+ -1)=0 at hc;simp only [ite_true];grind
  · change (1:Fp)*(tr.cell 3 0 (1024+b)+ -Fp.ofNat (if b=0 then 1 else 0))=0 at hc
    rw [ite_eq_right zero] at hc ⊢
    change (1:Fp)*(tr.cell 3 0 (1024+b)+ -0)=0 at hc
    grind

theorem sha384_committed_pad_step (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r b : Nat) (hr : r+1<tr.height 3) (hb : b<sha384PaddedLength n/128) :
    tr.cell 3 (r+1) (1024+b)=if b=0 then 0 else tr.cell 3 r (1024+(b-1)) := by
  have hc:=sha384_committed_pad_constraint n fixed pub tr h r (by omega)
    (.mul .isTransition (.add (.col (1024+b) true) (.neg (if b=0 then .const 0 else sha384PadSelect (b-1)))))
    (by simp only [sha384CommittedPadTable,List.mem_append];exact Or.inl (Or.inr (List.mem_map.mpr ⟨b,List.mem_range.mpr hb,rfl⟩)))
  by_cases zero : b=0 <;>
    simp only [zero,ite_true,ite_false,Expr.eval,Expr.evalWith,rowEnv,sha384PadSelect,
      Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr] at hc ⊢ <;> grind

/-- The local first/shift equations identify every existing row's block.
This does not assert that the trace contains all message blocks: sufficient
capacity must be derived from global bus matching. -/
theorem sha384_committed_pad_selector (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 3) (b : Nat) (hb : b<sha384PaddedLength n/128) :
    tr.cell 3 r (1024+b)=if r=b then 1 else 0 := by
  induction r generalizing b with
  | zero => simpa [eq_comm] using sha384_committed_pad_first n fixed pub tr h b hb
  | succ r ih =>
    rw [sha384_committed_pad_step n fixed pub tr h r b hr hb]
    by_cases zero : b=0
    · subst b;simp
    · rw [ite_eq_right zero,ih (by omega) (b-1) (by omega)]
      have same : r=b-1 ↔ r+1=b := by omega
      simp only [same]

/-- After the final declared block every selector vanishes, even if the
power-of-two trace has additional rows. -/
theorem sha384_committed_pad_inactive (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 3) (after : sha384PaddedLength n/128≤r)
    (b : Nat) (hb : b<sha384PaddedLength n/128) : tr.cell 3 r (1024+b)=0 := by
  rw [sha384_committed_pad_selector n fixed pub tr h r hr b hb,ite_eq_right (by omega)]

/-- Actual padding-byte equations, selected by the proved row schedule. -/
theorem sha384_committed_pad_constant (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (b j : Nat) (hr : b<tr.height 3) (hb : b<sha384PaddedLength n/128)
    (hj : j<128) (padding : n≤128*b+j) :
    (instructionBitExpr (8*j) 8).eval tr 3 b pub=Fp.ofNat (sha384PadConstByte n (128*b+j)) := by
  have hc:=sha384_committed_pad_constraint n fixed pub tr h b hr
    (.mul (sha384PadSelect b) (.add (instructionBitExpr (8*j) 8)
      (.neg (.const (sha384PadConstByte n (128*b+j)))))) (by
      simp only [sha384CommittedPadTable,List.mem_append]
      right
      apply List.mem_flatMap.mpr
      refine ⟨b,List.mem_range.mpr hb,?_⟩
      apply List.mem_filterMap.mpr
      exact ⟨j,List.mem_range.mpr hj,by rw [ite_eq_right (by omega)]⟩)
  have selected:=sha384_committed_pad_selector n fixed pub tr h b hr b hb
  simp only [ite_true] at selected
  change tr.cell 3 b (1024+b)*((instructionBitExpr (8*j) 8).eval tr 3 b pub+
    -Fp.ofNat (sha384PadConstByte n (128*b+j)))=0 at hc
  rw [selected] at hc
  grind

/-- The message-bus multiplicity is one on declared blocks and zero on
padding rows; it follows from selectors, rather than a Boolean assumption. -/
theorem sha384_committed_pad_sum (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 3) (k : Nat) (hk : k≤sha384PaddedLength n/128) :
    (sha384PadSum false k).eval tr 3 r pub=if r<k then 1 else 0 := by
  induction k with
  | zero => simp [sha384PadSum,Expr.eval,Expr.evalWith,rowEnv]; rfl
  | succ k ih =>
    have prev:=ih (by omega)
    have selected:=sha384_committed_pad_selector n fixed pub tr h r hr k (by omega)
    change (sha384PadSum false k).eval tr 3 r pub+tr.cell 3 r (1024+k)=_
    rw [prev,selected]
    by_cases before : r<k
    · rw [ite_eq_left before,ite_eq_right (by omega),ite_eq_left (by omega)];grind
    · rw [ite_eq_right before]
      by_cases same : r=k
      · rw [ite_eq_left same,ite_eq_left (by omega)];grind
      · rw [ite_eq_right same,ite_eq_right (by omega)];grind

/-- The ordered bus tag is exactly the row index while active, and zero
when inactive. No injectivity of field casts is presumed here. -/
theorem sha384_committed_pad_tag (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 3) (k : Nat) (hk : k≤sha384PaddedLength n/128) :
    (sha384PadSum true k).eval tr 3 r pub=if r<k then Fp.ofNat r else 0 := by
  induction k with
  | zero => simp [sha384PadSum,Expr.eval,Expr.evalWith,rowEnv]; rfl
  | succ k ih =>
    have prev:=ih (by omega)
    have selected:=sha384_committed_pad_selector n fixed pub tr h r hr k (by omega)
    change (sha384PadSum true k).eval tr 3 r pub+Fp.ofNat k*tr.cell 3 r (1024+k)=_
    rw [prev,selected]
    by_cases before : r<k
    · rw [ite_eq_left before,ite_eq_right (by omega),ite_eq_left (by omega)];grind
    · rw [ite_eq_right before]
      by_cases same : r=k
      · rw [ite_eq_left same,ite_eq_left (by omega),same];grind
      · rw [ite_eq_right same,ite_eq_right (by omega)];grind

end NearCompression
