import NearCompression.RealSegments
import NearSpecV3.ClaimV3Props

/-! Concrete versioned result envelope. State payloads remain opaque bytes until
all StateBoundary fields have a proved codec. Bounds are explicit, not truncation. -/
namespace NearCompression
open NearSpec NearSpecV3

inductive BoundaryEnvelope where
  | cont (state : Bytes)
  | fin (state : Bytes)
  | abort (state error : Bytes)
  | unmodeled (error : Bytes)
  deriving DecidableEq, Repr

def boundaryWireDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 98, 111, 117, 110, 100, 97, 114, 121, 45, 118, 49]

def BoundaryEnvelope.wf : BoundaryEnvelope → Prop
  | .cont s | .fin s => s.length < 4294967296
  | .abort s e => s.length < 4294967296 ∧ e.length < 4294967296
  | .unmodeled e => e.length < 4294967296

def BoundaryEnvelope.body : BoundaryEnvelope → Bytes
  | .cont s => u8 0 ++ borshBytes s
  | .fin s => u8 1 ++ borshBytes s
  | .abort s e => u8 2 ++ borshBytes s ++ borshBytes e
  | .unmodeled e => u8 3 ++ borshBytes e

def BoundaryEnvelope.encode (e : BoundaryEnvelope) : Bytes :=
  borshBytes boundaryWireDomain ++ e.body

def parseBoundaryBody : P BoundaryEnvelope := fun bs => do
  let (tag, bs) ← pU8 "boundary result" bs
  match tag with
  | 0 => let (s, bs) ← pBytes "state" bs; pure (.cont s, bs)
  | 1 => let (s, bs) ← pBytes "state" bs; pure (.fin s, bs)
  | 2 =>
    let (s, bs) ← pBytes "state" bs
    let (e, bs) ← pBytes "error" bs
    pure (.abort s e, bs)
  | 3 => let (e, bs) ← pBytes "error" bs; pure (.unmodeled e, bs)
  | _ => throw "invalid boundary result tag"

def parseBoundaryEnvelope : P BoundaryEnvelope := fun bs => do
  let (_, bs) ← dTag boundaryWireDomain "boundary domain" bs
  parseBoundaryBody bs

def decodeBoundaryEnvelope (bs : Bytes) : Except String BoundaryEnvelope := do
  let (e, rest) ← parseBoundaryEnvelope bs
  if rest.isEmpty then pure e else throw "trailing boundary bytes"

theorem boundary_body_roundtrip (e : BoundaryEnvelope) (wf : e.wf) (rest : Bytes) :
    parseBoundaryBody (e.body ++ rest) = .ok (e, rest) := by
  cases e <;> simp only [BoundaryEnvelope.wf] at wf
  all_goals simp only [BoundaryEnvelope.body, List.append_assoc, parseBoundaryBody]
  all_goals rw [pU8_ok _ _ _ (by decide)]
  all_goals simp only [bind, Except.bind]
  all_goals first
    | (rw [pBytes_ok _ _ _ wf]; rfl)
    | (rw [pBytes_ok _ _ _ wf.1]; simp only [bind, Except.bind]
       rw [pBytes_ok _ _ _ wf.2]; rfl)

theorem boundary_envelope_roundtrip (e : BoundaryEnvelope) (wf : e.wf) (rest : Bytes) :
    parseBoundaryEnvelope (e.encode ++ rest) = .ok (e, rest) := by
  simp only [BoundaryEnvelope.encode, List.append_assoc, parseBoundaryEnvelope]
  rw [dTag_ok _ _ _ (by decide)]
  exact boundary_body_roundtrip e wf rest

theorem boundary_envelope_decode_encode (e : BoundaryEnvelope) (wf : e.wf) :
    decodeBoundaryEnvelope e.encode = .ok e := by
  have h := boundary_envelope_roundtrip e wf []
  simp only [List.append_nil] at h
  simp only [decodeBoundaryEnvelope, h, bind, Except.bind]
  rfl

theorem boundary_envelope_injective (a b : BoundaryEnvelope) (ha : a.wf) (hb : b.wf)
    (same : a.encode = b.encode) : a = b := by
  have h := congrArg decodeBoundaryEnvelope same
  rw [boundary_envelope_decode_encode a ha, boundary_envelope_decode_encode b hb] at h
  exact Except.ok.inj h

theorem boundary_envelope_rejects_suffix (e : BoundaryEnvelope) (wf : e.wf)
    (suffix : Bytes) (hne : suffix ≠ []) :
    decodeBoundaryEnvelope (e.encode ++ suffix) = .error "trailing boundary bytes" := by
  simp only [decodeBoundaryEnvelope, boundary_envelope_roundtrip e wf suffix, bind, Except.bind]
  cases suffix with
  | nil => contradiction
  | cons b bs => rfl

theorem boundary_envelope_cont_fin_distinct (s t : Bytes)
    (hs : s.length < 4294967296) (ht : t.length < 4294967296) :
    (BoundaryEnvelope.cont s).encode ≠ (BoundaryEnvelope.fin t).encode := by
  intro h
  have he := boundary_envelope_injective (.cont s) (.fin t) hs ht h
  cases he

-- Decoder rejection examples exercise the executable byte parser in the kernel.
example : (decodeBoundaryEnvelope []).toOption.isNone = true := by decide +kernel
example : (decodeBoundaryEnvelope (borshBytes boundaryWireDomain ++ u8 4)).toOption.isNone = true := by
  decide +kernel
example : (decodeBoundaryEnvelope (borshBytes [0] ++ u8 0 ++ borshBytes [])).toOption.isNone = true := by
  decide +kernel
example : (decodeBoundaryEnvelope (borshBytes boundaryWireDomain ++ u8 2 ++ borshBytes [])).toOption.isNone = true := by
  decide +kernel

end NearCompression
