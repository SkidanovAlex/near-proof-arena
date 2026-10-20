import NearCompression.JointSourceBaseDescent
import NearCompression.TableLocalResidualWitness
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 ZkFormal.Udr NearSpecV3.Wasm

/-- Construct one base trace by projecting every decoded cell. Agreement with
original cells is proved only on the explicitly base-valued live columns. -/
def decodedBaseTrace (tr : Trace Fp8) : Trace Fp :=
  ⟨tr.log,fun t row column => (tr.cell t row column).c0⟩

theorem decoded_base_trace_cell (tr : Trace Fp8) (t row column : Nat)
    (base : Fp8.IsBase (tr.cell t row column)) :
    Fp8.ofBase ((decodedBaseTrace tr).cell t row column)=tr.cell t row column := by
  obtain ⟨value,equal⟩ := (Fp8.isBase_iff _).mp base
  change Fp8.ofBase (tr.cell t row column).c0=tr.cell t row column
  rw [equal]
  rfl

/-- Bounded source AIR expressions evaluate on the same base trace. Both
current and cyclic-next rows are covered; auxiliary columns may remain
extension-valued outside the source width. -/
theorem decoded_base_trace_source_eval (tr : Trace Fp8) (t r width : Nat) (pub : List Fp)
    (base : ∀ row column,column<width → Fp8.IsBase (tr.cell t row column))
    (e : Expr) (bound : e.colBound≤width) :
    e.eval tr t r (pub.map Fp8.ofBase)=Fp8.ofBase (e.eval (decodedBaseTrace tr) t r pub) := by
  have same : e.eval tr t r (pub.map Fp8.ofBase)=
      e.eval (airExt8Trace (decodedBaseTrace tr)) t r (pub.map Fp8.ofBase) := by
    induction e with
    | const n => rfl
    | pub i => rfl
    | isFirst => rfl
    | isLast => rfl
    | isTransition => rfl
    | col c next =>
      have hc : c<width := by change c+1≤width at bound;omega
      cases next
      · exact (decoded_base_trace_cell tr t r c (base r c hc)).symm
      · exact (decoded_base_trace_cell tr t ((r+1)%tr.height t) c (base _ c hc)).symm
    | add a b ha hb =>
      have ba : a.colBound≤width := Nat.le_trans (Nat.le_max_left _ _) bound
      have bb : b.colBound≤width := Nat.le_trans (Nat.le_max_right _ _) bound
      change _+_=_+_
      simp only [Expr.eval] at ha hb
      rw [ha ba,hb bb]
    | mul a b ha hb =>
      have ba : a.colBound≤width := Nat.le_trans (Nat.le_max_left _ _) bound
      have bb : b.colBound≤width := Nat.le_trans (Nat.le_max_right _ _) bound
      change _*_= _*_
      simp only [Expr.eval] at ha hb
      rw [ha ba,hb bb]
    | neg a ha => exact congrArg Neg.neg (ha bound)
  exact same.trans (air_expression_ext8_lift (decodedBaseTrace tr) t r pub e)

/-- Zero source residuals on the recovered extension trace imply actual
base-field TableLocal on its projection, including multiplicity bits. -/
theorem decoded_base_trace_table_local (table : Table) (tr : Trace Fp8) (t : Nat) (pub : List Fp)
    (base : ∀ row column,column<table.width → Fp8.IsBase (tr.cell t row column))
    (widths : ∀ e∈tableSourceResiduals table,e.colBound≤table.width)
    (lower : 1≤tr.log t) (upper : tr.log t≤table.maxLog)
    (zero : ∀ row,row<tr.height t → ∀ e∈tableSourceResiduals table,e.eval tr t row (pub.map Fp8.ofBase)=0) :
    TableLocal table (decodedBaseTrace tr) t pub := by
  apply table_source_residuals_local table (decodedBaseTrace tr) t pub lower upper
  intro row hr e he
  have h := zero row hr e he
  rw [decoded_base_trace_source_eval tr t row table.width pub base e (widths e he)] at h
  exact Fp8.ofBase_inj h

/-- A base-execution residual witness remains nonzero in the actual recovered
extension trace, ready for the local sumcheck soundness bound. -/
theorem decoded_base_residual_nonzero (tr : Trace Fp8) (t r width : Nat) (pub : List Fp)
    (base : ∀ row column,column<width → Fp8.IsBase (tr.cell t row column))
    (e : Expr) (bound : e.colBound≤width)
    (wrong : e.eval (decodedBaseTrace tr) t r pub≠0) :
    e.eval tr t r (pub.map Fp8.ofBase)≠0 := by
  rw [decoded_base_trace_source_eval tr t r width pub base e bound]
  intro zero
  exact wrong (Fp8.ofBase_inj zero)

/-- Wrong prepared execution on the constructed base trace yields a source
residual in the recovered extension trace or a base-trace bus imbalance.
Only live source columns need descent; auxiliary cells are unrestricted. -/
theorem decoded_wrong_output_residual_or_bus (codeCount : Nat) (tr : Trace Fp8) (pub : List Fp)
    (base : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),∀ row column,
      column<(preparedLiteralAir codeCount).tables[t].width → Fp8.IsBase (tr.cell t row column))
    (widths : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      ∀ e∈tableSourceResiduals (preparedLiteralAir codeCount).tables[t],
        e.colBound≤(preparedLiteralAir codeCount).tables[t].width)
    (logs : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      1≤tr.log t ∧ tr.log t≤(preparedLiteralAir codeCount).tables[t].maxLog)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error) :
    (∃ t,∃ ht : t<(preparedLiteralAir codeCount).tables.length,
      ∃ row,row<tr.height t ∧ ∃ e∈tableSourceResiduals (preparedLiteralAir codeCount).tables[t],
        e.eval tr t row (pub.map Fp8.ofBase)≠0) ∨
    (¬∀ b m,busCount (preparedLiteralAir codeCount).toAir (decodedBaseTrace tr) pub b true m+
      pubCount (preparedLiteralAir codeCount) pub b true m=
      busCount (preparedLiteralAir codeCount).toAir (decodedBaseTrace tr) pub b false m+
        pubCount (preparedLiteralAir codeCount) pub b false m) := by
  have alternative := prepared_wrong_output_residual_or_bus codeCount (decodedBaseTrace tr) pub logs fits
    cfg code method ctx blockLevel full eligible accepted fuel enoughFuel wrong
  rcases alternative with localFailure | busFailure
  · obtain ⟨t,ht,row,hr,e,he,nonzero⟩ := localFailure
    exact Or.inl ⟨t,ht,row,hr,e,he,decoded_base_residual_nonzero tr t row
      (preparedLiteralAir codeCount).tables[t].width pub (base t ht) e (widths t ht e he) nonzero⟩
  · exact Or.inr busFailure

end NearCompression
