import ZkFormal.NearV3.D1.Link.PlfIds
import ZkFormal.NearV3.Assembly.LinkSha

/-!
# `ZkFormal.NearV3.D1.Link.ShaExtra` — the extra `BYTES` senders of `nearAirV3D1` (L1)

Lane `v3-d1-phase2`, item L1.  D0a's `bytes_balance` (`Assembly/LinkSha`) lists every `BYTES`
sender of `nearAirV3`.  `nearAirV3D1` has two more:

* `akmV3` (table 26) sends the post-state access-key value bytes `(VPOST(vid), j, byte)`;
* the public body-prefix segment sends `(2, 8 + j, body[8 + j])` for `8 + j < O0` (it cancels
  the D0a body segment's receive at those positions).

`extraBytes` lists both (the akm rows' raw messages and the public sends); `extraBytes_count`
counts them.  The generated `LinkSha` copy adds `extraBytes` to D0a's `otherBytes`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1

/-- The `BYTES` messages of the raw `akmV3` table, row by row. -/
def akmBytes (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height T_AKM)).flatMap fun r => rowTraffic AkmV3.interactions tr T_AKM r pub B_BYTES true

/-- The public messages of `nearAirV3D1` on `(b, s)`, as a list. -/
def pubListD1 (pub : List Fp) (b : Nat) (s : Bool) : List (List Fp) :=
  (pubMsgs nearAirV3D1 pub).filterMap fun x => if x.1 = b ∧ x.2.1 = s then some x.2.2 else none

theorem count_pubListD1 (pub : List Fp) (b : Nat) (s : Bool) (M : List Fp) :
    (pubListD1 pub b s).count M = pubCount nearAirV3D1 pub b s M :=
  ZkFormal.NearV3.Assembly.count_filterMap_pub b s M _

/-- **The `BYTES` senders `nearAirV3D1` adds**: `akmV3` and the public body-prefix sends. -/
def extraBytes (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  akmBytes tr pub ++ pubListD1 pub B_BYTES true

theorem extraBytes_count (tr : Trace Fp) (pub : List Fp) (m : List Fp) :
    (extraBytes tr pub).count m =
      tableBusCount AkmV3.interactions tr T_AKM pub B_BYTES true m +
        pubCount nearAirV3D1 pub B_BYTES true m := by
  unfold extraBytes akmBytes
  rw [List.count_append, count_pubListD1, tableBusCount_eq]

end ZkFormal.NearV3.D1.Link
