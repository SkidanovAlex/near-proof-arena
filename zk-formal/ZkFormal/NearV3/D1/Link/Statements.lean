import ZkFormal.NearV3.D1.GoodD1Defs
import ZkFormal.NearV3.D1.Link.Records

/-!
# `ZkFormal.NearV3.D1.Link.Statements` — the D1 link split, with A7 isolated

Lane `v3-d1-phase2`, items L1/F1 (coordinator, 2026-10-15: keep the A7 step behind one
interface so that either outcome of plan §5 R-5 plugs in).

`ExtractD1StmtT` (`StmtsT`) follows from three statements:

* **`LinkD1CoreStmt`** (L1 without A7): the link inputs (`LinkInputsD1`: `prepD1`, the tape
  bound, `HoldsP`, records, SHA contracts, balance) give views `k x ts nts` with
  `GoodD1Core` (every condition of `checkD1a` except A7ᴰ¹) and `XFromRecords r x`;
* **`A7D1Step B`** (the A7 interface, the only part R-5 changes): under the same inputs, the
  `GoodD1Core` views satisfy the A7ᴰ¹ conjunct `a7D1 B cb (witnessOfD1 k x h)`.  Under
  option (A) the spec's A7ᴰ¹ is restated and this statement (and `FactorSoundD1`'s A7
  argument) names the new predicate; under (B) it stays as is and the AIR change proves it;
* **`FactorSoundD1 B`** (F1): `GoodD1Core` and the A7 conjunct give `RelD1a B`.

**`extractD1_of_parts`**: `LinkD1CoreStmt → A7D1Step B0 → FactorSoundD1 B0 → ExtractD1StmtT`
(proved here; mechanical: `linkInputsD1_of_holdsP`).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.Assembly

/-- **The D1 link without A7.** -/
def LinkD1CoreStmt : Prop :=
  ∀ (cb : Bytes) (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp) (r : D1Records),
    LinkInputsD1 cb h p tr r → ∃ k x ts nts, GoodD1Core cb k h p x ts nts ∧ XFromRecords r x

/-- **The A7 interface** (plan §5 R-5): the A7ᴰ¹ conjunct of the extracted witness. -/
def A7D1Step (B : Nat) : Prop :=
  ∀ (cb : Bytes) (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp) (r : D1Records),
    LinkInputsD1 cb h p tr r → ∀ k x ts nts, GoodD1Core cb k h p x ts nts → XFromRecords r x →
      a7D1 B cb (witnessOfD1 k x h) = true

/-- **F1**: the semantic views and the A7 conjunct give the relation. -/
def FactorSoundD1 (B : Nat) : Prop :=
  ∀ (cb : Bytes) (k : WalkD0) (h : HintD1) (p : Public.PrepD1) (x : ExtV3) (ts nts : List Tx),
    GoodD1Core cb k h p x ts nts → a7D1 B cb (witnessOfD1 k x h) = true →
      RelD1a B cb (witnessOfD1 k x h)

/-- **The soundness obligation from its three parts.** -/
theorem extractD1_of_parts (hL : LinkD1CoreStmt) (hA : A7D1Step B0) (hF : FactorSoundD1 B0) :
    ExtractD1StmtT := by
  intro cb h p tr hp hlen hH
  obtain ⟨r, I⟩ := linkInputsD1_of_holdsP hp hlen hH
  obtain ⟨k, x, ts, nts, g, hx⟩ := hL cb h p tr r I
  exact ⟨_, hF cb k h p x ts nts g (hA cb h p tr r I k x ts nts g hx)⟩

end ZkFormal.NearV3.D1.Link
