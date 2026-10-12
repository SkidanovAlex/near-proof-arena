import ZkFormal.NearV3.Assembly.FactorComplete
import ZkFormal.NearV3.Assembly.FactorSound

/-! Guarded axiom audit: `FactorComplete` (accepted witnesses admit `GoodV3`), closed with
A7 on the native post tries and A11 retired (user decision 2026-10-12), and the soundness factor. -/

/-- info: 'ZkFormal.NearV3.Assembly.factorComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.factorComplete

/-- info: 'ZkFormal.NearV3.Assembly.factorSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.factorSound

/-- info: 'ZkFormal.NearV3.Assembly.tries_reconstructed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.tries_reconstructed

/-- info: 'NearSpecV3.relD0a_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms NearSpecV3.relD0a_iff
