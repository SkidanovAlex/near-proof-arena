import ZkFormal.NearV3.Assembly.RenderV3Trace
import ZkFormal.NearV3.Assembly.NearAdmission
import ZkFormal.Size.PadHeader

/-!
# ZkFormal.NearV3.Assembly.RenderV3Bundle — completeness from per-table renders

The completeness half of the admission certificate (`hcomp` + `halign` of
`nearV3_admission_with_extract_b`) reduced to one per-witness obligation:

* `TableRenderV3 pub t` — one rendered table: a trace for table `t`, its exact traffic, local
  legality against `nearAirV3.tables[t]`, and the roll-aligned height (`log ≡ 1 mod 3`). The
  per-table `*_aligned_complete` theorems (`Render/Padded*.lean`) produce exactly these;
* `RenderBundleV3 pub` — one render per table index; `R.trace` assembles them (`traceSum`);
* `R.Balanced` — the bus balance of the bundle's traffic, with the public messages;
* `RenderWitnessV3 cb w` — an accepted witness has a hint, a prepared statement and a balanced
  bundle with an admissible header;
* `CompleteV3Stmt := ∀ cb w, checkD0a B0 cb w = .ok () → RenderWitnessV3 cb w`.

Proved here: `R.holdsP` (local legality, exact traffic, balance and the public fit give
`HoldsP nearAirV3`), `R.rollAligned`, and `admission_complete_of`: `CompleteV3Stmt` gives the
admission's `hcomp` and `halign` for a chosen hint selector and honest trace.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Size NearSpec NearSpecV3

/-- The certificate's auxiliary-group parameter (`g = 2`, as in `NearAdmission.lean`). -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- One rendered table of `nearAirV3`. -/
structure TableRenderV3 (pub : List Fp) (t : Nat) (ht : t < nearAirV3.tables.length) where
  tr : Trace Fp
  tf : ZkFormal.Near.Traffic
  loc : ZkFormal.Near.TableLocal nearAirV3.tables[t] tr t pub
  traffic : ZkFormal.Near.TableTraffic nearAirV3.tables[t].interactions tr t pub tf
  aligned : tr.log t % 3 = 1

/-- One render per table index. -/
abbrev RenderBundleV3 (pub : List Fp) :=
  (t : Fin nearAirV3.tables.length) → TableRenderV3 pub t.1 t.2

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- The assembled honest trace. -/
@[reducible] def trace : Trace Fp := traceSum (List.ofFn fun t => (R t).tr)

/-- The traffic of table `t` (empty past the last table). -/
def tf (t : Nat) : ZkFormal.Near.Traffic :=
  if h : t < nearAirV3.tables.length then (R ⟨t, h⟩).tf else ⟨fun _ => [], fun _ => []⟩

/-- The bus balance of the bundle (sends = receives on every bus, public messages included). -/
def Balanced : Prop :=
  ∀ b m,
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel true (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b true m =
      (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel false (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b false m

theorem trace_at (t : Nat) (ht : t < nearAirV3.tables.length) :
    AgreeAt R.trace (R ⟨t, ht⟩).tr t := by
  have h := agreeAt_traceSum (List.ofFn fun t => (R t).tr) (t := t) (by simpa using ht)
  simp only [List.getElem_ofFn] at h
  exact h

theorem local_at (t : Nat) (ht : t < nearAirV3.tables.length) :
    ZkFormal.Near.TableLocal nearAirV3.tables[t] R.trace t pub :=
  (tableLocal_agree (R.trace_at t ht)).2 (R ⟨t, ht⟩).loc

theorem traffic_at (t : Nat) (ht : t < nearAirV3.tables.length) :
    ZkFormal.Near.TableTraffic nearAirV3.tables[t].interactions R.trace t pub (R.tf t) := by
  have h := R.trace_at t ht
  have hT := (R ⟨t, ht⟩).traffic
  have htf : R.tf t = (R ⟨t, ht⟩).tf := by simp only [tf, ht, ↓reduceDIte]
  rw [htf]
  intro b m
  rw [h.tableBusCount, h.tableBusCount]
  exact hT b m

/-- **The assembled trace satisfies `HoldsP nearAirV3`.** -/
theorem holdsP (hfit : pubFit nearAirV3 pub = true) (hbal : R.Balanced) :
    HoldsP nearAirV3 pub R.trace :=
  holdsP_of_table_traffic R.tf R.local_at R.traffic_at hfit hbal

/-- **The assembled trace is roll-aligned** (every height `≡ 1 mod 3`). -/
theorem rollAligned (prm : ZkFormal.Stark.Params) (hm : prm.maxArityLog = 3) :
    RollAligned nearAirV3.toAir prm (ZkFormal.Prover.trHdr nearAirV3.toAir R.trace) := by
  apply ZkFormal.Size.rollAligned_of_trace_mod3 _ _ _ hm
  intro t ht
  rw [(R.trace_at t ht).1]
  exact (R ⟨t, ht⟩).aligned

end RenderBundleV3

/-- **Per-witness completeness obligation.** An accepted witness has a hint (in the codec's
range), a prepared statement whose packing fits the field, and a balanced render bundle over
its public vector with an admissible header. -/
def RenderWitnessV3 (cb : Bytes) : Prop :=
  ∃ (h : Hint) (p : Prep),
    prepD0 cb h = .ok p ∧ h.n < 256 ^ 4 ∧ h.body.length < 256 ^ 4 ∧
    (Hint.encode h).length ≤ v3MaxHintBytes ∧
    (ZkFormal.NearV3.Public.preparedBytes p 0).length < ZkFormal.Algebra.P ∧
    pubFit nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p 0)) = true ∧
    ∃ R : RenderBundleV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p 0)),
      R.Balanced ∧
      (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk (ZkFormal.Prover.trHdr nearAirV3.toAir R.trace) = true

/-- **The completeness obligation of the D0a certificate**: every witness the amended checker
accepts at the challenge bound `B0` has a balanced honest render. -/
def CompleteV3Stmt : Prop := ∀ cb w : Bytes, checkD0a B0 cb w = .ok () → RenderWitnessV3 cb

open Classical in
/-- The hint selector of the completeness proof. -/
noncomputable def hintSelV3 (hc : CompleteV3Stmt) (c : WfClaim) (w : List UInt8) : Hint :=
  if hr : checkD0a B0 (WfClaim.encode c) w = .ok () then Classical.choose (hc _ w hr) else Hint.empty

open Classical in
/-- The honest trace of the completeness proof. -/
noncomputable def traceOfV3 (hc : CompleteV3Stmt) (c : WfClaim) (w : List UInt8) : Trace Fp :=
  if hr : checkD0a B0 (WfClaim.encode c) w = .ok () then
    let hs := Classical.choose_spec (hc _ w hr)
    let hp := Classical.choose_spec hs
    (Classical.choose hp.2.2.2.2.2.2).trace
  else zeroTrace

/-- The canonical raw-hint codec on an honest hint and prepared statement. -/
theorem prepV3b_of {cb : Bytes} {h : Hint} {p : Prep} (hp : prepD0 cb h = .ok p)
    (hn : h.n < 256 ^ 4) (hb : h.body.length < 256 ^ 4)
    (hlen : (ZkFormal.NearV3.Public.preparedBytes p 0).length < ZkFormal.Algebra.P) :
    prepV3b cb (Hint.encode h) = some (ZkFormal.NearV3.Public.preparedBytes p 0) := by
  unfold prepV3b
  rw [Hint.decode_encode _ hn hb, Option.bind_some]
  unfold prepV3
  rw [hp]
  exact if_pos hlen

theorem hintSelV3_eq (hc : CompleteV3Stmt) {c : WfClaim} {w : List UInt8}
    (hk : checkD0a B0 (WfClaim.encode c) w = .ok ()) :
    hintSelV3 hc c w = Classical.choose (hc _ w hk) := by
  unfold hintSelV3; rw [dif_pos hk]

theorem traceOfV3_eq (hc : CompleteV3Stmt) {c : WfClaim} {w : List UInt8}
    (hk : checkD0a B0 (WfClaim.encode c) w = .ok ()) :
    traceOfV3 hc c w =
      (Classical.choose (Classical.choose_spec (Classical.choose_spec (hc _ w hk))).2.2.2.2.2.2).trace := by
  unfold traceOfV3; rw [dif_pos hk]

/-- **`CompleteV3Stmt` gives the admission's completeness premises** (`hcomp` and `halign` of
`nearV3_admission_with_extract_b`) for `hintSelV3` and `traceOfV3`. -/
theorem admission_complete_of (hc : CompleteV3Stmt) :
    (∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      ∃ cb', prepV3b (WfClaim.encode c) (Hint.encode (hintSelV3 hc c w)) = some cb' ∧
        HoldsP nearAirV3 (Udr.pubOf Fp cb') (traceOfV3 hc c w) ∧
        (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
          (ZkFormal.Prover.trHdr nearAirV3.toAir (traceOfV3 hc c w)) = true) ∧
    (∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
        (ZkFormal.Prover.trHdr nearAirV3.toAir (traceOfV3 hc c w))) := by
  have key : ∀ c w, challengeSpecD0a.Rel c w → checkD0a B0 (WfClaim.encode c) w = .ok () := by
    intro c w hr
    exact (relD0a_iff B0 _ w).mp hr
  constructor
  · intro c w _ hr
    have hk := key c w hr
    rw [hintSelV3_eq hc hk, traceOfV3_eq hc hk]
    obtain ⟨hp, hn, hb, _, hlen, hfit, hR⟩ := Classical.choose_spec (Classical.choose_spec (hc _ w hk))
    obtain ⟨hbal, hhdr⟩ := Classical.choose_spec hR
    exact ⟨_, prepV3b_of hp hn hb hlen, (Classical.choose hR).holdsP hfit hbal, hhdr⟩
  · intro c w _ hr
    have hk := key c w hr
    rw [traceOfV3_eq hc hk]
    exact RenderBundleV3.rollAligned _ _ rfl

theorem hintSelV3_spec (hc : CompleteV3Stmt) {c : WfClaim} {w : List UInt8}
    (hk : checkD0a B0 (WfClaim.encode c) w = .ok ()) :
    (Hint.encode (hintSelV3 hc c w)).length ≤ v3MaxHintBytes := by
  rw [hintSelV3_eq hc hk]
  exact (Classical.choose_spec (Classical.choose_spec (hc _ w hk))).2.2.2.1

theorem join_length (h π : Bytes) : (join h π).length = 4 + h.length + π.length := by
  simp only [join, borshBytes, List.length_append, u32, NearSpec.leN_length]

/-- **The v3 admission certificate from its two remaining obligations**: soundness
(`ExtractV3Stmt`) and completeness (`CompleteV3Stmt`), with the concrete hint codec
(`split`, `join`) and the canonical prepared-statement codec `prepV3b`. -/
theorem nearV3_admission_of (hext : ExtractV3Stmt) (hc : CompleteV3Stmt)
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art := by
  have key : ∀ (c : WfClaim) w, challengeSpecD0a.Rel c w → checkD0a B0 (WfClaim.encode c) w = .ok () :=
    fun c w hr => (relD0a_iff B0 _ w).mp hr
  obtain ⟨hcomp, halign⟩ := admission_complete_of hc
  refine nearV3_admission art pub hpub split prepV3b join himpl
    (fun c w => Hint.encode (hintSelV3 hc c w)) ?_ (traceOfV3 hc)
    (fun c h cb' tr hp hH => hsound_of_extract_b hext c h cb' tr hp hH) hcomp halign ?_
  · intro c w π _ hr
    apply split_join
    have := hintSelV3_spec hc (key c w hr)
    unfold v3MaxHintBytes at this
    omega
  · intro c w π _ hr hπ
    have h1 := hintSelV3_spec hc (key c w hr)
    have h2 := v3MaxHintBytes_fits
    rw [join_length]
    omega

end ZkFormal.NearV3.Assembly
