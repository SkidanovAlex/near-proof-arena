import ZkFormal.NearV3.D1.R.Base
import ZkFormal.Near.Extract.BusCount
import ZkFormal.Near.Extract.Segments

/-!
# `ZkFormal.NearV3.D1.R.Delta.Traffic` — the two replaced interactions of `rcptV3D1`

Lane `v3-d1-phase2`, item V4.  `rcptV3D1` (`tableQD1`) replaces two of D0a's receipt
interactions: the `MEM` write at time `r + 1` becomes `r + 1 + T0`, the `MPOS` leaf position
`r` becomes `r + M0`.  Each is the only send of the table on its bus, so the table's traffic
is D0a's with those two components shifted:

* `traffic_shift`: `TableTraffic RcptV3.interactions … tf` gives
  `TableTraffic tableQD1.interactions … (shiftT T0 M0 tf)` (the `MEM` / `MPOS` sends of `tf`
  with component `1` shifted; everything else unchanged);
* `traffic3G_shift`: `rcptTraffic3G o0 T0 M0 = shiftT T0 M0 (rcptTraffic3G o0 0 0)`.
-/

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.RcptV3

def oldMem : Interaction := send B_MEM (c sDEP) [c kslot, .add (c r) (k 1), c idx, aftE, c lk, c st]
def newMem : Interaction := send B_MEM (c sDEP) [c kslot, sum [c r, k 1, t0E], c idx, aftE, c lk, c st]
def oldMpos : Interaction := send B_MPOS (c rf) [k 0, c r, mid K_LEAF (c r), k 68]
def newMpos : Interaction := send B_MPOS (c rf) [k 0, .add (c r) m0E, mid K_LEAF (c r), k 68]

/-- `replI` with propositional equality. -/
def replI2 (i : Interaction) : Interaction :=
  if i = oldMem then newMem else if i = oldMpos then newMpos else i

set_option maxRecDepth 65536 in
theorem tableQD1_interactions2 : tableQD1.interactions = RcptV3.interactions.map replI2 := by
  decide

set_option maxRecDepth 65536 in
theorem mem_send_unique_b :
    (RcptV3.interactions.all fun i => !(decide (i.bus = B_MEM) && i.send) || decide (i = oldMem)) = true := by
  decide

set_option maxRecDepth 65536 in
theorem mpos_send_unique_b :
    (RcptV3.interactions.all fun i => !(decide (i.bus = B_MPOS) && i.send) || decide (i = oldMpos)) = true := by
  decide

theorem mem_send_unique {i : Interaction} (hi : i ∈ RcptV3.interactions) (hb : i.bus = B_MEM)
    (hs : i.send = true) : i = oldMem := by
  have h := List.all_eq_true.mp mem_send_unique_b i hi
  simp only [hb, hs, decide_true, Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact h

theorem mpos_send_unique {i : Interaction} (hi : i ∈ RcptV3.interactions) (hb : i.bus = B_MPOS)
    (hs : i.send = true) : i = oldMpos := by
  have h := List.all_eq_true.mp mpos_send_unique_b i hi
  simp only [hb, hs, decide_true, Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact h

/-- The field-level shift of a sent message on `MEM` / `MPOS`. -/
def fF (T M : Fp) (b : Nat) (s : Bool) (m : List Fp) : List Fp :=
  if s = true ∧ b = B_MEM then m.set 1 (m.getD 1 0 + T)
  else if s = true ∧ b = B_MPOS then m.set 1 (m.getD 1 0 + M) else m

/-- The natural-level shift. -/
def fN (t0 m0 b : Nat) (m : Msg) : Msg :=
  if b = B_MEM then m.set 1 (m.getD 1 0 + t0) else if b = B_MPOS then m.set 1 (m.getD 1 0 + m0) else m

/-- D0a's traffic with the `MEM` / `MPOS` sends shifted. -/
def shiftT (t0 m0 : Nat) (tf : Traffic) : Traffic := ⟨fun b => (tf.sends b).map (fN t0 m0 b), tf.recvs⟩

theorem getD_toFp (m : Msg) : (m.map Fp.ofNat).getD 1 0 = Fp.ofNat (m.getD 1 0) := by
  match m with
  | [] => rfl
  | [_] => rfl
  | _ :: b :: _ => rfl

theorem toFp_fN (t0 m0 b : Nat) (m : Msg) :
    Msg.toFp (fN t0 m0 b m) = fF (t0 : Fp) (m0 : Fp) b true (Msg.toFp m) := by
  unfold fN fF Msg.toFp
  by_cases h1 : b = B_MEM
  · subst h1
    simp only [ite_true, and_self, List.map_set]
    rw [getD_toFp, ← natCast_eq (List.getD m 1 0 + t0), natCast_add, natCast_eq]
  · by_cases h2 : b = B_MPOS
    · subst h2
      simp only [show B_MPOS ≠ B_MEM by decide, ite_false, and_false, ite_true, and_self, List.map_set]
      rw [getD_toFp, ← natCast_eq (List.getD m 1 0 + m0), natCast_add, natCast_eq]
    · simp only [h1, h2, ite_false, and_false]

variable {tr : Trace Fp} {t : Nat} {pub : List Fp} {r' : Nat}

theorem multNat_new_mem : newMem.multNat tr t r' pub = oldMem.multNat tr t r' pub := rfl
theorem multNat_new_mpos : newMpos.multNat tr t r' pub = oldMpos.multNat tr t r' pub := rfl

theorem msgVal_mem {q : Nat} {T : Fp} (hT : t0E.eval tr t q pub = T) :
    newMem.msgVal tr t q pub = fF T 0 B_MEM true (oldMem.msgVal tr t q pub) := by
  simp only [newMem, oldMem, send, Interaction.msgVal, fF, List.map_cons, List.map_nil, and_self,
    if_true, List.getD_cons_succ, List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero,
    eval_sum_cons, eval_sum_nil, eval_add, eval_c, eval_k, hT, List.cons.injEq, true_and, and_true]
  grind

theorem msgVal_mpos {q : Nat} {M : Fp} (hM : m0E.eval tr t q pub = M) :
    newMpos.msgVal tr t q pub = fF 0 M B_MPOS true (oldMpos.msgVal tr t q pub) := by
  simp only [newMpos, oldMpos, send, Interaction.msgVal, fF, List.map_cons, List.map_nil,
    show B_MPOS ≠ B_MEM by decide, and_false, if_false, and_self, if_true,
    List.getD_cons_succ, List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero,
    eval_add, eval_c, hM]

/-- **Row level**: `rcptV3D1`'s row traffic is D0a's, shifted. -/
theorem row_shift {q : Nat} {T M : Fp} (hT : t0E.eval tr t q pub = T) (hM : m0E.eval tr t q pub = M)
    (b : Nat) (s : Bool) :
    rowTraffic (RcptV3.interactions.map replI2) tr t q pub b s =
      (rowTraffic RcptV3.interactions tr t q pub b s).map (fF T M b s) := by
  unfold rowTraffic
  rw [List.flatMap_map, List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro i hi
  by_cases h1 : i = oldMem
  · subst h1
    simp only [replI2, if_true]
    have e1 : newMem.bus = B_MEM := rfl
    have e2 : newMem.send = true := rfl
    have e3 : oldMem.bus = B_MEM := rfl
    have e4 : oldMem.send = true := rfl
    simp only [e1, e2, e3, e4]
    by_cases hb : B_MEM = b ∧ true = s
    · obtain ⟨rfl, rfl⟩ := hb
      simp only [and_self, ite_true, List.map_replicate]
      rw [multNat_new_mem, msgVal_mem hT]
      simp only [fF, and_self, ite_true]
    · rw [if_neg hb, if_neg hb, List.map_nil]
  by_cases h2 : i = oldMpos
  · subst h2
    simp only [replI2, if_true, show oldMpos ≠ oldMem by decide, if_false]
    have e1 : newMpos.bus = B_MPOS := rfl
    have e2 : newMpos.send = true := rfl
    have e3 : oldMpos.bus = B_MPOS := rfl
    have e4 : oldMpos.send = true := rfl
    simp only [e1, e2, e3, e4]
    by_cases hb : B_MPOS = b ∧ true = s
    · obtain ⟨rfl, rfl⟩ := hb
      simp only [and_self, ite_true, List.map_replicate]
      rw [multNat_new_mpos, msgVal_mpos hM]
      have hne : B_MPOS ≠ B_MEM := by decide
      simp only [fF, hne, and_false, ite_false, and_self, ite_true]
    · rw [if_neg hb, if_neg hb, List.map_nil]
  · simp only [replI2, h1, h2, if_false]
    split
    · rename_i hbs
      have hid : ∀ m : List Fp, fF T M b s m = m := by
        intro m
        unfold fF
        rw [if_neg, if_neg]
        · rintro ⟨rfl, rfl⟩; exact h2 (mpos_send_unique hi hbs.1 hbs.2)
        · rintro ⟨rfl, rfl⟩; exact h1 (mem_send_unique hi hbs.1 hbs.2)
      simp [hid]
    · rfl

theorem count_map_perm {l l' : List (List Fp)} (f : List Fp → List Fp)
    (h : ∀ m, l.count m = l'.count m) (m : List Fp) : (l.map f).count m = (l'.map f).count m :=
  ((List.perm_iff_count.mpr h).map f).count_eq m

/-- **Traffic level**: D0a's receipt traffic, shifted, is `rcptV3D1`'s. -/
theorem traffic_shift (hx : ExtBytes pub) {tf : Traffic}
    (h : TableTraffic RcptV3.interactions tr t pub tf) :
    TableTraffic tableQD1.interactions tr t pub (shiftT (t0V pub) (m0V pub) tf) := by
  rw [tableQD1_interactions2]
  intro b m
  have hrow : ∀ s, (List.range (tr.height t)).flatMap
      (fun q => rowTraffic (RcptV3.interactions.map replI2) tr t q pub b s) =
      ((List.range (tr.height t)).flatMap (fun q => rowTraffic RcptV3.interactions tr t q pub b s)).map
        (fF ((t0V pub : Nat) : Fp) ((m0V pub : Nat) : Fp) b s) := by
    intro s
    rw [List.map_flatMap]
    apply ZkFormal.Near.flatMap_congr'
    intro q _
    exact row_shift (t0E_eval hx tr t q) (m0E_eval hx tr t q) b s
  constructor
  · rw [tableBusCount_eq, hrow]
    have hc := fun m' => (h b m').1
    simp only [tableBusCount_eq] at hc
    rw [count_map_perm _ hc m]
    simp only [shiftT, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [toFp_fN]
  · rw [tableBusCount_eq, hrow]
    have hid : fF ((t0V pub : Nat) : Fp) ((m0V pub : Nat) : Fp) b false = id := by
      funext m; unfold fF; rw [if_neg (by simp), if_neg (by simp)]; rfl
    rw [hid, List.map_id]
    rw [← tableBusCount_eq]
    exact (h b m).2

/-- The D1 sends are D0a's (`t0 = m0 = 0`), shifted. -/
theorem sends3G_shift (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) (b : Nat) :
    rcptSends3G o0 t0 m0 pub ls b = (rcptSends3G o0 0 0 pub ls b).map (fN t0 m0 b) := by
  unfold rcptSends3G
  by_cases h1 : b = B_MEM
  · subst h1
    rw [List.map_flatMap]
    apply ZkFormal.Near.flatMap_congr'
    intro j _
    simp only [show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_RCL by decide, ite_false,
      List.nil_append, List.map_flatMap]
    apply ZkFormal.Near.flatMap_congr'
    intro x _
    simp [rSendsG, fN, show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_KEYNIB by decide,
      List.map_map, Function.comp_def]
  by_cases h2 : b = B_MPOS
  · subst h2
    rw [List.map_flatMap]
    apply ZkFormal.Near.flatMap_congr'
    intro j _
    simp only [show B_MPOS ≠ B_BYTES by decide, show B_MPOS ≠ B_RCL by decide, ite_false,
      List.nil_append, List.map_flatMap]
    apply ZkFormal.Near.flatMap_congr'
    intro x _
    simp [rSendsG, fN, show B_MPOS ≠ B_BYTES by decide, show B_MPOS ≠ B_KEYNIB by decide,
      show B_MPOS ≠ B_MEM by decide, show B_MPOS ≠ B_RIDS by decide]
  · have hid : fN t0 m0 b = id := by funext m; simp [fN, h1, h2]
    rw [hid, List.map_id]
    apply ZkFormal.Near.flatMap_congr'
    intro j _
    congr 1
    apply ZkFormal.Near.flatMap_congr'
    intro x _
    simp [rSendsG, h1, h2]

theorem traffic3G_shift (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    rcptTraffic3G o0 t0 m0 pub ls = shiftT t0 m0 (rcptTraffic3G o0 0 0 pub ls) := by
  unfold rcptTraffic3G shiftT
  congr 1
  funext b
  exact sends3G_shift o0 t0 m0 pub ls b

end ZkFormal.NearV3.D1.RcptD1
