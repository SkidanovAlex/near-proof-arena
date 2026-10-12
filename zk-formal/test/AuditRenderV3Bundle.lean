import ZkFormal.NearV3.Assembly.RenderV3Bundle

/-! Guarded axiom audit: the v3 admission certificate from its two remaining obligations
(`ExtractV3Stmt`, `CompleteV3Stmt`) and the render-bundle composition. -/

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_admission_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.nearV3_admission_of

/-- info: 'ZkFormal.NearV3.Assembly.admission_complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.admission_complete_of

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.holdsP
