import ZkFormal.Near.Extract.Common
import ZkFormal.Near.Extract.RcptView
import ZkFormal.NearV3.D1.Tables.AkmDefs
import NearSpecV3.TxD1

/-!
# `ZkFormal.NearV3.D1.Extract.AkmView` — what `akmV3` holds (`AkmViewStmt`)

Lane `v3-d1-phase2` (milestone V3).  One `AkmE` per value segment (in row order): the value
record `vid`, the FullAccess bit `fa` (`t₁`), the final nonce time `tlast`, the gas-refund use
count `U`, the value bytes and the 8 post-nonce bytes `pb`.

Facts (`AkmSegWf`): the bytes decode (`decodeAccessKey`) to a key whose nonce is the first 8
bytes and whose permission is FullAccess exactly when `fa = 1`; a FullAccess value is the 9
bytes `nonce ‖ 1`; a non-FullAccess key is never written (`pb` = the nonce bytes).

Traffic: sends `VBYTES (vid, j, bⱼ)` for every byte, `AKMEM (vid, 0, j, bⱼ, fa)` (`j < 8`);
receives `AKMEM (vid, tlast, j, pbⱼ, fa)` (`j < 8`); a FullAccess key also sends `VSLOT (vid)`,
the post value `BYTES (VPOST(vid), j, pbⱼ)` (`j < 8`) and `BYTES (VPOST(vid), 8, 1)`, and
`AKC (vid, 0)`, and receives `AKC (vid, U)`.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure AkmE where
  vid : Nat
  fa : Nat
  tlast : Nat
  U : Nat
  bytes : List Nat
  pb : List Nat
  deriving Repr, Inhabited

/-- `VPOST(vid)`. -/
def AkmE.vpost (e : AkmE) : Nat := K_VPOST + 16 * e.vid

structure AkmSegWf (e : AkmE) : Prop where
  len : 9 ≤ e.bytes.length ∧ e.pb.length = 8
  bytes8 : ∀ x ∈ e.bytes, x < 256
  decode : ∃ k, NearSpecV3.decodeAccessKey (e.bytes.map UInt8.ofNat) = some k ∧
    k.nonce = NearSpec.leNat ((e.bytes.take 8).map UInt8.ofNat) ∧
    (k.perm = .fullAccess ↔ e.fa = 1)
  fullAccess : e.fa = 1 → e.bytes.length = 9 ∧ e.bytes.getD 8 0 = 1
  faBool : e.fa ≤ 1
  keep : e.fa = 0 → ∀ j, j < 8 → e.pb.getD j 0 = e.bytes.getD j 0
  canon : e.vid < P ∧ e.tlast < P ∧ e.U < P ∧ ∀ x ∈ e.pb, x < P

structure AkmWf (es : List AkmE) : Prop where
  segs : ∀ e ∈ es, AkmSegWf e
  rows : (es.map fun e => e.bytes.length).sum ≤ 2 ^ AkmV3.maxLog

def akmSends (es : List AkmE) (b : Nat) : List Msg :=
  if b = B_VBYTES then es.flatMap fun e => (List.range e.bytes.length).map fun j => [e.vid, j, e.bytes.getD j 0]
  else if b = B_AKMEM then es.flatMap fun e => (List.range 8).map fun j => [e.vid, 0, j, e.bytes.getD j 0, e.fa]
  else if b = B_VSLOT then es.flatMap fun e => if e.fa = 1 then [[e.vid]] else []
  else if b = B_BYTES then es.flatMap fun e => if e.fa = 1 then
      (List.range 8).map (fun j => [e.vpost, j, e.pb.getD j 0]) ++ [[e.vpost, 8, e.bytes.getD 8 0]] else []
  else if b = B_AKC then es.flatMap fun e => if e.fa = 1 then [[e.vid, 0]] else []
  else []

def akmRecvs (es : List AkmE) (b : Nat) : List Msg :=
  if b = B_AKMEM then es.flatMap fun e => (List.range 8).map fun j => [e.vid, e.tlast, j, e.pb.getD j 0, e.fa]
  else if b = B_AKC then es.flatMap fun e => if e.fa = 1 then [[e.vid, e.U]] else []
  else []

def akmTraffic (es : List AkmE) : Traffic := ⟨akmSends es, akmRecvs es⟩

/-- **The `akmV3` view statement.** -/
def AkmViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal AkmV3.table tr t pub →
    ∃ es, AkmWf es ∧ TableTraffic AkmV3.interactions tr t pub (akmTraffic es)

end ZkFormal.NearV3.D1
