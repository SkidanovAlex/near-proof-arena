import ZkFormal.NearV3.Rcpt.Extract.RcptView
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.R.ViewDefs` — what `rcptV3D1` holds (definitions)

Lane `v3-d1-phase2`, item V4.  `RcptV3ViewStmt`'s view (`RcptE`, `ListV3`, `flatR`, the
receipt facts `RcptE.Wf`) with the D1 offsets of `rcptV3D1` (`D1/Tables/RcptD1Defs`): the
public extension `M0, T0, O0, TOK0` (`E_M0 … E_TOK0`, little-endian bytes) moves

* the first running-token value from `0` to `TOK0`,
* the refund-body positions from `8 + …` to `O0 + …` (`bOffsG`),
* the receipt count: `|receipts| + M0 = PH_N`,
* the `MEM` write time from `r + 1` to `r + 1 + T0`, and the "read not from the future"
  bound from `tprev ≤ r` to `tprev ≤ r + T0` (`RcptE.Wf` at index `r + T0`),
* the `MPOS` leaf position from `r` to `r + M0`.

With `M0 = T0 = TOK0 = 0` and `O0 = 8` every definition is D0a's (`rSendsG 8 0 0 = rSends`).
Definitions only.
-/

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 NearSpec

/-- The public extension `M0, T0, O0, TOK0` consists of bytes. -/
def ExtBytes (pub : List Fp) : Prop := ∀ i, i < EXT_LEN → pubNat pub (E_M0 + i) < 256

def m0V (pub : List Fp) : Nat := leN' (pubBytes pub E_M0 4)
def t0V (pub : List Fp) : Nat := leN' (pubBytes pub E_T0 4)
def o0V (pub : List Fp) : Nat := leN' (pubBytes pub E_O0 4)
def tok0V (pub : List Fp) : Nat := leN' (pubBytes pub E_TOK0 16)

/-- The extension is bytes, and `M0, T0 < 2^24`, `O0 < 2^30` (no field wrap of the shifted
counters; at the D1a bounds `M0 ≤ 8192 + 4481`, `T0 ≤ 8192`, `O0 ≤ 2^24`). -/
def ExtOk (pub : List Fp) : Prop :=
  ExtBytes pub ∧ m0V pub < 2 ^ 24 ∧ t0V pub < 2 ^ 24 ∧ o0V pub < 2 ^ 30

/-- Body position of receipt `r`'s refund, from `o0`. -/
def bOffsG (o0 : Nat) (xs : List RcptE) (r : Nat) : Nat := o0 + ((xs.take r).map rfLen).sum

/-- `rSends` with the body offset `o0`, the `MEM` time offset `t0` and the leaf offset `m0`. -/
def rSendsG (o0 t0 m0 : Nat) (pub : List Fp) (xs : List RcptE) (j r o : Nat) (x : RcptE) (b : Nat) :
    List Msg :=
  if b = B_BYTES then
    emitAt (msgId K_RC j) o x.enc ++
    (if x.hr then emitAt K_RF (bOffsG o0 xs r) x.encRefund else []) ++
    emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
    (if x.hr then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0)
     else [])
  else if b = B_KEYNIB then
    RcptE.keyMsgs r x.keySyms ++ (if x.ee then RcptE.keyMsgs (W_AK + r) x.akSyms else [])
  else if b = B_MEM then
    (List.range 16).map fun i => [x.kslot, r + 1 + t0, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]
  else if b = B_RIDS then (List.range 32).map fun i => [r, i, x.rid.getD i 0]
  else if b = B_MPOS then [[0, r + m0, msgId K_LEAF r, 68]]
  else if b = B_SREC then
    ((List.range x.v.length).filter fun i => x.gv.getD i false).map fun i => [r, i, x.v.getD i 0]
  else if b = B_AKC then (if x.ee ∧ x.akf = 0 then [[x.akk, x.aku + 1]] else [])
  else if b = B_BND then
    x.rlk.map fun (p, l, h, hn, u) => [BND_STRIDE * x.q + p, l, h, hn, u + 1]
  else []

def rcptSends3G (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) (b : Nat) : List Msg :=
  (List.range ls.length).flatMap fun j =>
    (if b = B_BYTES then emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)) else []) ++
    (if b = B_RCL then [[j, lOffs (ls.getD j default).rs (ls.getD j default).rs.length]] else []) ++
    (located ls j).flatMap fun (r, o, x) => rSendsG o0 t0 m0 pub (flatR ls) j r o x b

def rcptTraffic3G (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) : Traffic :=
  ⟨rcptSends3G o0 t0 m0 pub ls, rcptRecvs3 ls⟩

/-- **The traffic of `rcptV3D1`.** -/
def rcptTraffic3D1 (pub : List Fp) (ls : RcptV3Vs) : Traffic :=
  rcptTraffic3G (o0V pub) (t0V pub) (m0V pub) pub ls

/-- **Table-level facts of `rcptV3D1`** (`RcptV3Wf` with the D1 offsets; the extension is
assumed to be bytes, `ExtBytes`, where it is used). -/
structure RcptV3WfD1 (pub : List Fp) (ls : RcptV3Vs) : Prop where
  nonempty : ls ≠ []
  toks : ∃ toks : List Nat, toks.length = (flatR ls).length + 1 ∧ toks.head? = some (tok0V pub) ∧
    (∀ r (h : r < (flatR ls).length),
      (flatR ls)[r].Wf (r + t0V pub) (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r + 1) 0)) ∧
    ((∀ i, i < 16 → pubNat pub (PH_BURNT + i) < 256) →
      toks.getD (flatR ls).length 0 = leN' (pubBytes pub PH_BURNT 16))
  count : (∀ i, i < 4 → pubNat pub (PH_N + i) < 256) →
    (flatR ls).length + m0V pub = leN' (pubBytes pub PH_N 4)
  nj : ∀ L ∈ ls, Fp.ofNat (L.n0 + 256 * L.n1) = Fp.ofNat L.rs.length
  body : (∀ i, i < 4 → pubNat pub (PH_BLEN + i) < 256) →
    bOffsG (o0V pub) (flatR ls) (flatR ls).length = leN' (pubBytes pub PH_BLEN 4)
  canon : (∀ L ∈ ls, L.n0 < P ∧ L.n1 < P) ∧ ∀ x ∈ flatR ls, ∀ y ∈ x.raw3, y < P

end ZkFormal.NearV3.D1.RcptD1
