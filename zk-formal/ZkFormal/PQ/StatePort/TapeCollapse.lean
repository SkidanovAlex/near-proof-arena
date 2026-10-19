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
theorem canonKeys_nodup (AP : AirP) (pub : List Fp) :
    (canonKeys AP pub).Nodup :=
  nodup_of_count_le_one _ (fun k => canonKeys_count_le AP pub k)
theorem canonMsgs_nodup (AP : AirP) (pub : List Fp) :
    (canonMsgs AP pub).Nodup :=
  nodup_of_count_le_one _ (fun k => canonMsgs_count_le AP pub k)
end ZkFormal.PQ.StatePort
