import NearCompression.HostBoundary

/-! Storage congruence for arbitrary related states, including states produced
by earlier host calls. This is stronger than one-time map normalization. -/
namespace NearCompression
open NearSpecV3.Wasm

local instance : LawfulBEq ByteArray where
  eq_of_beq := byte_array_beq_eq _ _
  rfl := by intro a; change (a.data == a.data) = true; exact BEq.rfl

theorem storage_read_equiv (a b : TTN.RealStore) (h : RealEquivalent a b)
    (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.storageRead a key gs) (TTN.storageRead b key gs) := by
  have ha := h.acct
  have hr := h.recd
  have ht := acct_touch_equiv _ _ ha
  have hn := recorder_record_nodes_equiv _ _ hr b.store
  have hv := fun keys k len => recorder_record_equiv _ _ (hn keys) k len
  have he : a.overlay.get? key = b.overlay.get? key := h.overlay.getElem?_eq
  simp only [TTN.storageRead, he, TTN.deref, h.store, h.root]
  unfold OutEquivalent
  repeat' (split <;> (try simp_all only []))
  all_goals grind only

theorem storage_write_like_equiv (cost : Cost) (a b : TTN.RealStore)
    (h : RealEquivalent a b) (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.writeLike cost a key gs) (TTN.writeLike cost b key gs) := by
  have ha := h.acct
  have hr := h.recd
  have ht := acct_touch_all_equiv _ _ ha
  have htv := fun keys k => acct_touch_equiv _ _ (ht keys) k
  have hn := recorder_record_nodes_equiv _ _ hr b.store
  have hv := fun keys k len => recorder_record_equiv _ _ (hn keys) k len
  have hc := fun gas keys => accounting_commit_equiv gas _ _ _ _ ha (ht keys)
  have hcv := fun gas keys k => accounting_commit_equiv gas _ _ _ _ ha (htv keys k)
  have he : a.overlay.get? key = b.overlay.get? key := h.overlay.getElem?_eq
  simp only [TTN.writeLike, he, TTN.deref, h.store, h.root, hc, hcv]
  unfold OutEquivalent
  repeat' (split <;> (try simp_all only []))
  all_goals grind only

theorem storage_has_key_equiv (a b : TTN.RealStore) (h : RealEquivalent a b)
    (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.storageHasKey a key gs) (TTN.storageHasKey b key gs) := by
  have ha := h.acct
  have hr := h.recd
  have hn := recorder_record_nodes_equiv _ _ hr b.store
  have he : a.overlay.get? key = b.overlay.get? key := h.overlay.getElem?_eq
  simp only [TTN.storageHasKey, he, h.store, h.root]
  unfold OutEquivalent
  repeat' (split <;> (try simp_all only []))
  all_goals grind only

/-- No normalized-input restriction: this applies after arbitrary prior
operations as long as they preserve the same relation. -/
theorem storage_read_host_equiv (s t : St) (hs : StateEquivalent s t)
    (a b : TTN.RealStore) (hr : RealEquivalent a b) (key : ByteArray) :
    HostResultEquivalent ((realOpH a TTN.storageRead key).run s)
      ((realOpH b TTN.storageRead key).run t) := by
  apply real_op_host_equiv s t hs a b hr
  rw [state_equiv_gas s t hs, hr.pfx]
  exact storage_read_equiv a b hr _ _

theorem storage_write_host_equiv (s t : St) (hs : StateEquivalent s t)
    (a b : TTN.RealStore) (hr : RealEquivalent a b) (key : ByteArray) (cost : Cost) :
    HostResultEquivalent ((realOpH a (TTN.writeLike cost) key).run s)
      ((realOpH b (TTN.writeLike cost) key).run t) := by
  apply real_op_host_equiv s t hs a b hr
  rw [state_equiv_gas s t hs, hr.pfx]
  exact storage_write_like_equiv cost a b hr _ _

theorem storage_has_key_host_equiv (s t : St) (hs : StateEquivalent s t)
    (a b : TTN.RealStore) (hr : RealEquivalent a b) (key : ByteArray) :
    HostResultEquivalent ((realOpH a TTN.storageHasKey key).run s)
      ((realOpH b TTN.storageHasKey key).run t) := by
  apply real_op_host_equiv s t hs a b hr
  rw [state_equiv_gas s t hs, hr.pfx]
  exact storage_has_key_equiv a b hr _ _

theorem real_equiv_remove_record (a b : TTN.RealStore) (h : RealEquivalent a b) :
    RealEquivalent (TTN.removeRecord a) (TTN.removeRecord b) :=
  ⟨h.store, h.root, h.overlay, h.acct, h.pfx,
    ⟨h.recd.1, congrArg (· + 2000) h.recd.2⟩, h.recBefore, h.writes⟩

theorem real_equiv_over_limit (a b : TTN.RealStore) (h : RealEquivalent a b) :
    TTN.overLimit a = TTN.overLimit b := by
  simp only [TTN.overLimit, h.recd.2, h.recBefore]

theorem host_get_bind_run {A : Type} (f : St → HM A) (s : St) :
    (get >>= f).run s = (f s).run s := rfl

/-- Direct trie reads used by the real External, including missing-node errors.
These reads do not alter the state or the accounting cache. -/
theorem real_get_host_equiv (s t : St) (hs : StateEquivalent s t) (key : ByteArray) :
    HostResultEquivalent ((realGetH key).run s) ((realGetH key).run t) := by
  unfold realGetH
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · exact ⟨rfl, hs⟩
  · rename_i a b
    have he : a.overlay.get? key = b.overlay.get? key := hr.overlay.getElem?_eq
    simp only [he, hr.store, hr.root]
    repeat' (split <;> (try simp_all only []))
    all_goals exact ⟨rfl, hs⟩

theorem real_has_host_equiv (s t : St) (hs : StateEquivalent s t) (key : ByteArray) :
    HostResultEquivalent ((realHasH key).run s) ((realHasH key).run t) := by
  unfold realHasH
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · exact ⟨rfl, hs⟩
  · rename_i a b
    have he : a.overlay.get? key = b.overlay.get? key := hr.overlay.getElem?_eq
    simp only [he, hr.store, hr.root]
    repeat' (split <;> (try simp_all only []))
    all_goals exact ⟨rfl, hs⟩

/-- The receipt proof-size failure is preserved, including its error state. -/
theorem observe_host_equiv (s t : St) (hs : StateEquivalent s t) :
    HostResultEquivalent (observeH.run s) (observeH.run t) := by
  unfold observeH
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · exact ⟨rfl, hs⟩
  · simp only
    rw [real_equiv_over_limit _ _ hr]
    split <;> exact ⟨rfl, hs⟩

end NearCompression
