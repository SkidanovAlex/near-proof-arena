import ZkFormal.NearV3.D1.Extract.KibProof
import ZkFormal.NearV3.D1.Tables.KibUDefs

/-!
# `ZkFormal.NearV3.D1.Extract.KibD1Proof` — the `kibD1` view (`KibD1ViewStmt`, `kibD1_view`)

Lane `v3-d1-a7b` (plan §5, R-5 → (B)).  `kibD1` (table 27) replaces `kibV3`: it routes the
unread-key walks' records to `UKEYNIB`.  One `KibE` per active row (in row order, as
`kib_view`), now with `w₂ < 256` (the byte decomposition).  Traffic: receives
`PKEY (w₀, w₁, w₂, t, sym, last)` (every row); sends `KEYNIB (wid, t, sym, last)` for the rows
with `w₂ < 128` and `UKEYNIB (wid, t, sym, last)` for the rows with `w₂ ≥ 128`
(`wid = w₀ + 2⁸·w₁ + 2¹⁶·w₂`).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure KibD1Wf (es : List KibE) : Prop where
  canon : ∀ e ∈ es, e.w0 < P ∧ e.w1 < P ∧ e.w2 < P ∧ e.t < P ∧ e.sym < P ∧ e.last < P
  byte : ∀ e ∈ es, e.w2 < 256
  rows : es.length ≤ 2 ^ KibD1.maxLog

def kibMsg (e : KibE) : Msg := [e.wid, e.t, e.sym, e.last]

def kibD1Sends (es : List KibE) (b : Nat) : List Msg :=
  if b = B_KEYNIB then (es.filter fun e => decide (e.w2 < 128)).map kibMsg
  else if b = B_UKEYNIB then (es.filter fun e => decide (128 ≤ e.w2)).map kibMsg
  else []

def kibD1Traffic (es : List KibE) : Traffic := ⟨kibD1Sends es, kibRecvs es⟩

/-- **The `kibD1` view statement.** -/
def KibD1ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal KibD1.table tr t pub →
    ∃ es, KibD1Wf es ∧ TableTraffic KibD1.interactions tr t pub (kibD1Traffic es)

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1.KibD1Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.KibV3 ZkFormal.NearV3.D1.KibD1 KibProof

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal KibD1.table tr tt pub)
include hL

theorem wbBool {q : Nat} (hq : q < tr.height tt) (x : Nat) (hx : x < 8) :
    tr.cell tt q (wb x) = 0 ∨ tr.cell tt q (wb x) = 1 := by
  have := hL.constr q hq (bool (c (wb x))) (by
    unfold KibD1.table KibD1.constraints
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨x, hx, rfl⟩))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem actBool {q : Nat} (hq : q < tr.height tt) :
    tr.cell tt q act = 0 ∨ tr.cell tt q act = 1 := by
  have := hL.constr q hq (bool (c act)) (by
    unfold KibD1.table KibD1.constraints
    exact List.mem_append_left _ (List.mem_cons_self ..))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

/-- An active row's `w₂` is the natural value of its bits. -/
theorem w2_eq {q : Nat} (hq : q < tr.height tt) (ha : tr.cell tt q act = 1) :
    cv tr tt q w2 = bitsVal (fun x => cv tr tt q (wb x)) 0 8 := by
  have h := hL.constr q hq (.mul (c act) (sub (c w2) (bits (fun j => c (wb j)) 0 8))) (by
    unfold KibD1.table KibD1.constraints; simp)
  rw [eval_mul, eval_c, eval_sub, eval_c,
    eval_bits tr tt q pub wb 0 8 (fun x hx => by simpa using wbBool hL hq x hx), ha] at h
  have hlt := bitsVal_lt (fun x => cv tr tt q (wb x)) 0 8
    (fun x hx => cv_bool (by simpa using wbBool hL hq x hx))
  have h2 : tr.cell tt q w2 = ((bitsVal (fun x => cv tr tt q (wb x)) 0 8 : Nat) : Fp) := by grind
  unfold cv at h2 ⊢
  rw [h2, toNat_natCast]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))

theorem w2_lt {q : Nat} (hq : q < tr.height tt) (ha : tr.cell tt q act = 1) :
    cv tr tt q w2 < 256 := by
  rw [w2_eq hL hq ha]
  exact bitsVal_lt _ 0 8 (fun x hx => cv_bool (by simpa using wbBool hL hq x hx))

/-- The routing bit is bit 7 of `w₂`. -/
theorem u_iff {q : Nat} (hq : q < tr.height tt) (ha : tr.cell tt q act = 1) :
    tr.cell tt q (wb 7) = 1 ↔ 128 ≤ cv tr tt q w2 := by
  rw [w2_eq hL hq ha]
  have h7 : bitsVal (fun x => cv tr tt q (wb x)) 0 8 =
      bitsVal (fun x => cv tr tt q (wb x)) 0 7 + 128 * cv tr tt q (wb 7) := rfl
  have hlt := bitsVal_lt (fun x => cv tr tt q (wb x)) 0 7
    (fun x hx => cv_bool (by simpa using wbBool hL hq x (by omega)))
  rcases wbBool hL hq 7 (by omega) with h | h
  · have : cv tr tt q (wb 7) = 0 := by simp [cv, h, Fp.toNat_zero]
    rw [h7, this, h]
    exact ⟨fun e => absurd e fp_zero_ne_one, fun e => by omega⟩
  · have : cv tr tt q (wb 7) = 1 := by simp [cv, h, Fp.toNat_one]
    rw [h7, this, h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem rowT {q : Nat} (hq : q < tr.height tt) (bb : Nat) (sd : Bool) :
    rowTraffic KibD1.interactions tr tt q pub bb sd =
      if isA tr tt q then
        (if sd then kibD1Sends [rowOf tr tt q] bb else kibRecvs [rowOf tr tt q] bb).map Msg.toFp
      else [] := by
  unfold rowTraffic KibD1.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · have hw := wid_toFp (tr := tr) (tt := tt) q
    have hu := u_iff hL hq ha
    have hr : (rowOf tr tt q).w2 = cv tr tt q w2 := rfl
    simp only [eval_c, eval_mul, eval_sub, eval_k, ha, ite_true, isA, decide_true, uE, Dsl.not]
    rcases wbBool hL hq 7 (by omega) with h7 | h7
    · have hlt : (rowOf tr tt q).w2 < 128 := by
        rw [hr]; exact Nat.lt_of_not_le fun hc => absurd (hu.2 hc) (by rw [h7]; decide)
      have hm : ¬ (128 ≤ (rowOf tr tt q).w2) := by omega
      cases sd <;> by_cases h1 : bb = B_PKEY <;> by_cases h2 : bb = B_KEYNIB <;>
        by_cases h3 : bb = B_UKEYNIB <;>
        simp_all [kibD1Sends, kibRecvs, kibMsg, Msg.toFp, B_PKEY, B_KEYNIB, B_UKEYNIB, KibV3.wE,
          rowOf, cv, Fp.ofNat_toNat]
      all_goals first | rfl | grind
    · have hge : 128 ≤ (rowOf tr tt q).w2 := by rw [hr]; exact hu.1 h7
      have hm : ¬ ((rowOf tr tt q).w2 < 128) := by omega
      cases sd <;> by_cases h1 : bb = B_PKEY <;> by_cases h2 : bb = B_KEYNIB <;>
        by_cases h3 : bb = B_UKEYNIB <;>
        simp_all [kibD1Sends, kibRecvs, kibMsg, Msg.toFp, B_PKEY, B_KEYNIB, B_UKEYNIB, KibV3.wE,
          rowOf, cv, Fp.ofNat_toNat]
      all_goals first | rfl | grind
  · rcases actBool hL hq with h0 | h0
    · have hz : ∀ x : Fp, (0 : Fp) * x = 0 := fun x => by grind
      simp [eval_c, eval_mul, h0, isA, hz]
    · exact absurd h0 ha

end

theorem kibD1Sends_flat (es : List KibE) (b : Nat) :
    kibD1Sends es b = es.flatMap fun e => kibD1Sends [e] b := by
  induction es with
  | nil => unfold kibD1Sends; split <;> (try split) <;> rfl
  | cons e es ih =>
    rw [List.flatMap_cons, ← ih]
    unfold kibD1Sends
    split
    · rw [List.filter_cons]; split <;> simp_all
    · split
      · rw [List.filter_cons]; split <;> simp_all
      · rfl

end ZkFormal.NearV3.D1.KibD1Proof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near KibProof KibD1Proof

/-- **The `kibD1` view.** -/
theorem kibD1_view : KibD1ViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ b sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic KibD1.interactions tr tt q pub b sd) =
      (if sd then kibD1Sends (rows.map (rowOf tr tt)) b
       else kibRecvs (rows.map (rowOf tr tt)) b).map Msg.toFp := by
    intro b sd
    rw [flatMap_congr' (G := fun q => if isA tr tt q then
        (if sd then kibD1Sends [rowOf tr tt q] b else kibRecvs [rowOf tr tt q] b).map Msg.toFp
      else []) (fun q hq => KibD1Proof.rowT hL (List.mem_range.1 hq) b sd)]
    rw [flatMap_if]
    cases sd
    · simp only [Bool.false_eq_true, ite_false]
      rw [kibRecvs_flat, List.map_flatMap, List.flatMap_map]
    · simp only [ite_true]
      rw [kibD1Sends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    obtain ⟨hq, ha⟩ := List.mem_filter.1 hq
    exact w2_lt hL (List.mem_range.1 hq) (by simpa [isA] using ha)
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [kibD1Traffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [kibD1Traffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3.D1
