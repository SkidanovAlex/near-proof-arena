import ZkFormal.PQ.StatePort.Tape
open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.PQ.StatePort ZkFormal.Udr ZkFormal.Udr.Np
namespace ZkFormal.PQ.StatePort
theorem fsum_cons_head (a : Fp) (l : List Fp) : fsum (a :: l) = a + fsum l := rfl
/-- **The selector collapse.**  On a nodup key list, summing `cnt * sel` over paired keys picks
the one matching key; every other key contributes `cnt * 0 = 0` regardless of the message guard. -/
theorem sel_fsum_eq (keys : List (Nat × Nat)) (cnt : Fp) (b : Nat) (m : List Fp)
    (key : Nat × Nat) (hkey : key = (b, m.length)) (hnd : keys.Nodup) :
    fsum ((keys.zip (keys.map fun kk => if kk = key then (1:Fp) else 0)).map fun ks =>
      if ks.1.1 = b ∧ m.take ks.1.2 = m then cnt * ks.2 else 0)
      = if key ∈ keys then cnt else 0 := by
  induction keys with
  | nil => simp [fsum]
  | cons k ks ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hknotin, hnd'⟩ := hnd
    rw [List.map_cons, List.zip_cons_cons, List.map_cons, fsum_cons_head]
    by_cases hc : k = key
    · rw [if_pos hc]
      have hguard : (k.1 = b ∧ m.take k.2 = m) := by
        rw [hc, hkey]; exact ⟨rfl, List.take_length⟩
      rw [if_pos hguard, if_pos (by rw [← hc]; exact List.mem_cons_self ..)]
      have hnot : key ∉ ks := fun hmem => hknotin (by rw [hc]; exact hmem)
      have hzero : fsum ((ks.zip (ks.map fun kk => if kk = key then (1:Fp) else 0)).map fun ks =>
          if ks.1.1 = b ∧ m.take ks.1.2 = m then cnt * ks.2 else 0) = 0 := by
        have := ih hnd'; rw [if_neg hnot] at this; exact this
      rw [hzero]; grind
    · have hhead : (if (k, if k = key then (1:Fp) else 0).fst.fst = b ∧
            m.take (k, if k = key then (1:Fp) else 0).fst.snd = m
          then cnt * (k, if k = key then (1:Fp) else 0).snd else 0) = 0 := by
        rw [if_neg hc]; split <;> grind
      rw [hhead, ih hnd']
      by_cases hmem : key ∈ ks
      · rw [if_pos (List.mem_cons_of_mem _ hmem)]; grind
      · have hne : ¬(key ∈ k :: ks) := by
          intro h; rcases List.mem_cons.mp h with hh | hh
          · exact absurd hh.symm hc
          · exact hmem hh
        rw [if_neg hne]; grind
/-- A list with `count ≤ 1` everywhere is nodup. -/
theorem nodup_of_count_le_one {α : Type} [BEq α] [LawfulBEq α] (l : List α)
    (h : ∀ a, l.count a ≤ 1) : l.Nodup := by
  rw [List.nodup_iff_count_eq_ite]
  intro a
  have hle := h a
  by_cases ha : a ∈ l
  · rw [if_pos ha]
    have hpos : 0 < l.count a := List.count_pos_iff.mpr ha
    omega
  · rw [if_neg ha, List.count_eq_zero.mpr ha]
theorem canonKeys_nodup (off : Nat) (AP : AirP) (pub : List Fp) :
    (canonKeys off AP pub).Nodup :=
  nodup_of_count_le_one _ (fun k => canonKeys_count_le off AP pub k)
theorem canonMsgs_nodup (off : Nat) (AP : AirP) (pub : List Fp) :
    (canonMsgs off AP pub).Nodup :=
  nodup_of_count_le_one _ (fun k => canonMsgs_count_le off AP pub k)

/-- On a nodup list, a singleton indicator's `fsum` is that element's value. -/
theorem fsum_select {α : Type} [DecidableEq α] (l : List α) (f : α → Fp) (a : α)
    (hnd : l.Nodup) :
    fsum (l.map fun x => if x = a then f x else 0) = if a ∈ l then f a else 0 := by
  induction l with
  | nil => simp [fsum]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hxnot, hnd'⟩ := hnd
    rw [List.map_cons]
    show (if x = a then f x else 0) + fsum (xs.map fun x => if x = a then f x else 0) = _
    rw [ih hnd']
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl, if_pos (List.mem_cons_self ..)]
      grind
    · rw [if_neg hx]
      by_cases hmem : a ∈ xs
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
        grind
      · rw [if_neg hmem, if_neg (by
          intro h; rcases List.mem_cons.mp h with h' | h'
          · exact hx h'.symm
          · exact hmem h')]
        grind

/-- The canonical selector is the one-hot indicator of `key`. -/
theorem zip_sel_one_hot (keys : List (Nat × Nat)) (key : Nat × Nat) :
    keys.zip (keys.map fun kk => if kk = key then (1:Fp) else 0)
      = keys.map fun kk => (kk, if kk = key then (1:Fp) else 0) := by
  induction keys with
  | nil => rfl
  | cons k ks ih => simp [List.zip_cons_cons, ih]

/-- A canonical row contributes `cnt` at its own `(bus, msg)` and `0` elsewhere. -/
theorem fsum_own_key (keys : List (Nat × Nat)) (key : Nat × Nat) (rowMsg : List Fp)
    (cnt : Fp) (b : Nat) (m : List Fp) (hnd : keys.Nodup)
    (hlen : key.2 = rowMsg.length) :
    fsum ((keys.zip (keys.map fun kk => if kk = key then (1:Fp) else 0)).map fun ks =>
      if ks.1.1 = b ∧ rowMsg.take ks.1.2 = m then cnt * ks.2 else 0)
      = if (key ∈ keys ∧ b = key.1 ∧ m = rowMsg) then cnt else 0 := by
  rw [zip_sel_one_hot]
  have hpoint : ∀ kk ∈ keys,
      ((if kk.1 = b ∧ rowMsg.take kk.2 = m then cnt * (if kk = key then (1:Fp) else 0) else 0) : Fp)
        = (if kk = key then (if b = key.1 ∧ m = rowMsg then cnt else 0) else 0) := by
    intro kk _
    by_cases hk : kk = key
    · rw [hk]
      have htake : rowMsg.take key.2 = rowMsg := by rw [hlen]; exact List.take_length
      by_cases hg : (b = key.1 ∧ m = rowMsg)
      · rw [if_pos hg, if_pos ⟨hg.1.symm, by rw [hg.2]; exact htake⟩]
        grind
      · rw [if_neg hg]
        rw [if_neg (by intro hc; exact hg ⟨hc.1.symm, by rw [← hc.2, htake]⟩)]
        grind
    · rw [if_neg hk]
      simp only [if_neg hk]
      split <;> grind
  rw [show (keys.map fun kk => (kk, if kk = key then (1:Fp) else 0)).map (fun ks =>
        if ks.1.1 = b ∧ rowMsg.take ks.1.2 = m then cnt * ks.2 else 0)
      = keys.map (fun kk => if kk = key then (if b = key.1 ∧ m = rowMsg then cnt else 0) else 0) from by
    rw [List.map_map]
    exact List.map_congr_left hpoint]
  rw [fsum_select keys (fun _ => if b = key.1 ∧ m = rowMsg then cnt else 0) key hnd]
  by_cases h : (b = key.1 ∧ m = rowMsg) <;> simp [h]

/-- **The canonical row's contribution** at the row's own message. -/
theorem canonRow_sum_apply (off : Nat) (AP : AirP) (pub : List Fp) (k : Nat × List Fp)
    (hk : k ∈ canonMsgs off AP pub) (b : Nat) (m : List Fp) :
    TapeRow.sum (canonKeys off AP pub)
      { msg := k.2
        cnt := ((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
          - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)
        sel := (canonKeys off AP pub).map fun kk =>
          if kk = (k.1, k.2.length) then 1 else 0 } b m
      = if (b = k.1 ∧ m = k.2) then
          (((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
            - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)) else 0 := by
  show fsum ((canonKeys off AP pub).zip ((canonKeys off AP pub).map fun kk =>
      if kk = (k.1, k.2.length) then (1:Fp) else 0) |>.map fun ks =>
        if ks.1.1 = b ∧ k.2.take ks.1.2 = m then
          (((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
            - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)) * ks.2 else 0) = _
  rw [fsum_own_key (canonKeys off AP pub) (k.1, k.2.length) k.2
    (((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
      - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)) b m
    (canonKeys_nodup off AP pub) (by rfl)]
  by_cases hg : (b = k.1 ∧ m = k.2)
  · rw [if_pos hg, if_pos ⟨canonKey_mem off AP pub k hk, hg.1, hg.2⟩]
  · rw [if_neg hg, if_neg (by intro hc; exact hg ⟨hc.2.1, hc.2.2⟩)]

/-- A canonical message is a public message. -/
theorem canonMsgs_spec (off : Nat) (AP : AirP) (pub : List Fp) (b : Nat) (m : List Fp) :
    (off + b, m) ∈ canonMsgs off AP pub ↔
      ∃ s ∈ AP.pubSegs, ∃ r ∈ s.msgs pub, s.bus = b ∧ r = m := by
  unfold canonMsgs
  rw [List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨x, hx, hkx⟩
    rw [pubMsgs, List.mem_flatMap] at hx
    obtain ⟨s, hs, hms⟩ := hx
    rw [List.mem_map] at hms
    obtain ⟨r, hr, rfl⟩ := hms
    have hb : s.bus = b := by
      have := congrArg Prod.fst hkx; simpa using this
    have hm : r = m := by
      have := congrArg Prod.snd hkx; simpa using this
    exact ⟨s, hs, r, hr, hb, hm⟩
  · rintro ⟨s, hs, r, hr, hb, rfl⟩
    refine ⟨(s.bus, s.send, r), ?_, ?_⟩
    · rw [pubMsgs, List.mem_flatMap]
      exact ⟨s, hs, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
    · simp [hb]

/-- If no public message is `(b, m)`, its two public counts are zero. -/
theorem pubCount_eq_zero_of_not_canon (off : Nat) (AP : AirP) (pub : List Fp) (b : Nat)
    (m : List Fp) (h : (off + b, m) ∉ canonMsgs off AP pub) (send : Bool) :
    pubCount AP pub b send m = 0 := by
  apply List.length_eq_zero_iff.mpr
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq]
  intro hxeq
  apply h
  obtain ⟨bus, sd, msg⟩ := x
  have hb : bus = b := by simpa using congrArg Prod.fst hxeq
  have hm : msg = m := by simpa using congrArg (fun y => y.2.2) hxeq
  rw [pubMsgs, List.mem_flatMap] at hx
  obtain ⟨s, hs, hms⟩ := hx
  rw [List.mem_map] at hms
  obtain ⟨r, hr, hrm⟩ := hms
  have hsb : s.bus = b := by
    rw [← hb]; exact congrArg (fun y => y.1) hrm
  have hrm' : r = m := by
    rw [← hm]; exact congrArg (fun y => y.2.2) hrm
  exact (canonMsgs_spec off AP pub b m).mpr ⟨s, hs, r, hr, hsb, hrm'⟩

/-- **P4: the canonical TAPE carries exactly the net public multiplicity.** -/
theorem tapeNet_canon (off : Nat) (AP : AirP) (pub : List Fp) :
    TapeNet off AP pub (tapeCanon off AP pub) := by
  intro b m
  let rowOf : Nat × List Fp → TapeRow := fun k =>
    { msg := k.2
      cnt := ((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
        - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)
      sel := (canonKeys off AP pub).map fun kk =>
        if kk = (k.1, k.2.length) then 1 else 0 }
  have hrows : (tapeCanon off AP pub).rows = (canonMsgs off AP pub).map rowOf := rfl
  have hkeys : (tapeCanon off AP pub).keys = canonKeys off AP pub := rfl
  have hstep : ∀ k ∈ canonMsgs off AP pub,
      TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m
        = if k = (off + b, m) then
            (((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
              - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)) else 0 := by
    intro k hk
    rw [show TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m
        = TapeRow.sum (canonKeys off AP pub)
          { msg := k.2
            cnt := ((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
              - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)
            sel := (canonKeys off AP pub).map fun kk =>
              if kk = (k.1, k.2.length) then 1 else 0 } (off + b) m from rfl]
    rw [canonRow_sum_apply off AP pub k hk (off + b) m]
    by_cases h : k = (off + b, m)
    · have h1 : off + b = k.1 := by rw [h]
      have h2 : m = k.2 := by rw [h]
      rw [if_pos ⟨h1, h2⟩, if_pos h]
    · rw [if_neg (by intro hc; exact h (Prod.ext hc.1.symm hc.2.symm))]
      rw [if_neg h]
  show tapeSum (tapeCanon off AP pub) (off + b) m = netF AP pub b m
  unfold tapeSum
  rw [hrows, hkeys, List.map_map]
  rw [show ((fun row => TapeRow.sum (canonKeys off AP pub) row (off + b) m) ∘ rowOf)
      = (fun k => TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m) from rfl]
  rw [show ((canonMsgs off AP pub).map (fun k =>
        TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m))
      = ((canonMsgs off AP pub).map (fun k =>
        if k = (off + b, m) then TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m else 0)) from by
    apply List.map_congr_left
    intro k hk
    by_cases hkm : k = (off + b, m)
    · rw [if_pos hkm]
    · rw [if_neg hkm, hstep k hk, if_neg hkm]]
  rw [fsum_select (canonMsgs off AP pub)
      (fun k => TapeRow.sum (canonKeys off AP pub) (rowOf k) (off + b) m)
      (off + b, m) (canonMsgs_nodup off AP pub)]
  by_cases hq : (off + b, m) ∈ canonMsgs off AP pub
  · rw [if_pos hq]
    rw [hstep (off + b, m) hq, if_pos rfl]
    have hbo : (off + b) - off = b := Nat.add_sub_cancel_left ..
    rw [hbo]
    rfl
  · rw [if_neg hq]
    have hz : pubCount AP pub b true m = 0 ∧ pubCount AP pub b false m = 0 :=
      ⟨pubCount_eq_zero_of_not_canon off AP pub b m hq true,
       pubCount_eq_zero_of_not_canon off AP pub b m hq false⟩
    unfold netF
    rw [hz.1, hz.2]
    rfl

end ZkFormal.PQ.StatePort
