import ZkFormal.NearV3.Assembly.SourceShaBytes

/-! Declarations of `ZkFormal.NearV3.Candidates.ShaFourPhysical` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

namespace ZkFormal.NearV3.Candidates.ShaFourPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Assembly

/-- Byte and length validity survive allocation because whole jobs are retained. -/
theorem bins_ok (bins : List (List Gen.Msg)) (ms : List Gen.Msg)
    (hp : bins.flatten.Perm ms) (hr : ∀bin∈bins,(Gen.honestRows bin).length≤2^22)
    (hb : ∀M∈ms,∀x∈M.bytes,x<256) :
    ∀bin∈bins,MsgsOk bin := by
  intro bin hbin
  have hm : ∀M∈bin,M∈ms := by
    intro M hM
    exact hp.mem_iff.mp (List.mem_flatten.mpr ⟨bin,hbin,hM⟩)
  exact ⟨fun M hM=>hb M (hm M hM),fun M hM=>sha_message_len_of_rows (hr bin hbin) hM,hr bin hbin⟩

end ZkFormal.NearV3.Candidates.ShaFourPhysical
