import ZkFormal.NearV3.D1.Public.PreparedD1Defs
import ZkFormal.NearV3.Public.HeaderBinding
import ZkFormal.NearV3.Spec.Codec
import ZkFormal.NearV3.D1.R.ViewDefs

/-!
# `ZkFormal.NearV3.D1.Public.Ext` — the D1 header and the public extension (P0, part 1)

Lane `v3-d1-phase2`, item P0.  For the D1 tape `preparedBytesD1 p ov`:

* `headerBytesD1` has D0a's layout: it is `headerBytes p.base ov` with the tag
  `near-arena-prep-d1a-v0` (the same length as D0a's) in place of D0a's. Every header field
  after the tag is at the same position with the same bytes (`headerD1_getD`), and the tape
  has the header at positions `< 202` (`preparedD1_header`).
* The extension `u32 M0 ‖ u32 T0 ‖ u32 O0 ‖ u128 TOK0` is at `E0 = 322 = 202 + 8·15`
  (`preparedD1_ext`). Hence `m0V`, `t0V`, `o0V`, `tok0V` of the public input are `p.m0`,
  `p.t0`, `p.o0`, `p.tok0` (below `2^32`, resp. `2^128`), and `ExtOk` holds under the
  bounds (`extOk_prepared`).
* Every public input of a byte tape is a byte (`pubNat_pubOf_lt`), so `ExtBytes` holds for
  every tape.
-/

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 ZkFormal.Algebra NearSpec NearSpecV3 ZkFormal.NearV3.Public ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.RcptD1

private theorem byteArray_loop_length' (bs : ByteArray) (i : Nat) (r : List UInt8) :
    (ByteArray.toList.loop bs i r).length = bs.size - i + r.length := by
  rw [ByteArray.toList.loop]
  split
  · rw [byteArray_loop_length' bs (i + 1) _]
    simp only [List.length_cons]
    omega
  · simp only [List.length_reverse]
    omega
termination_by bs.size - i

theorem prepTagD1_length : prepTagD1.length = prepTag.length := by
  simp only [prepTagD1, prepTag, String.toUTF8, ByteArray.toList]
  rw [byteArray_loop_length', byteArray_loop_length']
  simp only [String.size_toByteArray]
  decide

theorem headerD1_eq (p : PrepD1) (ov : Nat) :
    headerBytesD1 p ov = borshBytes prepTagD1 ++ (p.base.hdr.encode ++ u32 p.base.body.length ++ u32 ov) := by
  simp [headerBytesD1, List.append_assoc]

theorem header_eq (p : Prep) (ov : Nat) :
    headerBytes p ov = borshBytes prepTag ++ (p.hdr.encode ++ u32 p.body.length ++ u32 ov) := by
  simp [headerBytes, List.append_assoc]

theorem borshBytes_tag_length : (borshBytes prepTagD1).length = (borshBytes prepTag).length := by
  simp [borshBytes, prepTagD1_length, u32, leN_length]

theorem headerBytesD1_length (p : PrepD1) (ov : Nat) (hr : RootsSized p.base) :
    (headerBytesD1 p ov).length = 202 := by
  rw [headerD1_eq, List.length_append, borshBytes_tag_length, ← List.length_append, ← header_eq]
  exact headerBytes_length p.base ov hr

/-- After the tag, the D1 header is D0a's. -/
theorem headerD1_getD (p : PrepD1) (ov : Nat) {j : Nat} (hj : (borshBytes prepTag).length ≤ j) :
    (headerBytesD1 p ov).getD j 0 = (headerBytes p.base ov).getD j 0 := by
  rw [headerD1_eq, header_eq]
  obtain ⟨i, rfl⟩ : ∃ i, j = (borshBytes prepTag).length + i := ⟨j - (borshBytes prepTag).length, by omega⟩
  rw [getD_right, ← borshBytes_tag_length, getD_right]

theorem encodeD1_header (header ext : ByteString) (blocks : List Payload) {j : Nat}
    (hj : j < header.length) : (encodeD1 header ext blocks).getD j 0 = header.getD j 0 := by
  unfold encodeD1
  simp only [List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem encodeD1_ext (header ext : ByteString) (blocks : List Payload) {i : Nat}
    (hi : i < ext.length) :
    (encodeD1 header ext blocks).getD (header.length + 8 * blocks.length + i) 0 = ext.getD i 0 := by
  unfold encodeD1
  have hm := metadata_length (header.length + 8 * blocks.length + ext.length) blocks
  rw [show header.length + 8 * blocks.length + i =
      (header ++ metadata (header.length + 8 * blocks.length + ext.length) blocks).length + i by
    simp [hm]]
  exact getD_middle _ _ _ hi

theorem preparedBlocksD1_length (p : PrepD1) : (preparedBlocksD1 p).length = 15 := rfl

theorem extBytes_length (p : PrepD1) : (extBytes p).length = EXT_LEN := by
  simp [extBytes, u32, u128, leN_length, EXT_LEN]

theorem preparedD1_header (p : PrepD1) (ov : Nat) (hr : RootsSized p.base) {j : Nat} (hj : j < 202) :
    (preparedBytesD1 p ov).getD j 0 = (headerBytesD1 p ov).getD j 0 :=
  encodeD1_header _ _ _ (by rw [headerBytesD1_length p ov hr]; exact hj)

theorem preparedD1_ext (p : PrepD1) (ov : Nat) (hr : RootsSized p.base) {i : Nat} (hi : i < EXT_LEN) :
    (preparedBytesD1 p ov).getD (E_M0 + i) 0 = (extBytes p).getD i 0 := by
  have h := encodeD1_ext (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p)
    (i := i) (by rw [extBytes_length]; exact hi)
  rw [headerBytesD1_length p ov hr, preparedBlocksD1_length] at h
  exact h

/-! ## Public inputs of a byte tape -/

theorem pubNat_pubOf (bs : List UInt8) (i : Nat) :
    ZkFormal.Near.pubNat (ZkFormal.Udr.pubOf Fp bs) i = (bs.getD i 0).toNat := by
  unfold ZkFormal.Near.pubNat
  rw [pub_getD, byteF, Fp.toNat_ofNat, Nat.mod_eq_of_lt (by have := (bs.getD i 0).toNat_lt; unfold ZkFormal.Algebra.P; omega)]

theorem pubNat_pubOf_lt (bs : List UInt8) (i : Nat) : ZkFormal.Near.pubNat (ZkFormal.Udr.pubOf Fp bs) i < 256 := by
  rw [pubNat_pubOf]; exact (bs.getD i 0).toNat_lt

theorem extBytes_pubOf (bs : List UInt8) : ExtBytes (ZkFormal.Udr.pubOf Fp bs) :=
  fun i _ => pubNat_pubOf_lt bs _

/-- `pubBytes` of a tape window is the window. -/
theorem pubBytes_pubOf (bs : List UInt8) (off len : Nat) :
    ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp bs) off len =
      (List.range len).map fun j => (bs.getD (off + j) 0).toNat := by
  simp only [ZkFormal.Near.pubBytes, pubNat_pubOf]

theorem leN'_window (bs : List UInt8) (off w : Nat) (x : Nat) (hx : x < 256 ^ w)
    (hb : ∀ j, j < w → bs.getD (off + j) 0 = (leN w x).getD j 0) :
    ZkFormal.Near.leN' (ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp bs) off w) = x := by
  rw [pubBytes_pubOf]
  have hm : ((List.range w).map fun j => (bs.getD (off + j) 0).toNat).map UInt8.ofNat = leN w x := by
    apply List.ext_getElem (by simp [leN_length])
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range]
    rw [hb j (by simpa using hj), UInt8.ofNat_toNat, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj', Option.getD_some]
  unfold ZkFormal.Near.leN'
  rw [hm]
  exact ZkFormal.NearV3.leNat_leN' w x hx

theorem getD_append_left' (l l' : List UInt8) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

variable (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
include hr

theorem ext_window {off w x : Nat} (hoff : E_M0 ≤ off) (hend : off + w ≤ E_M0 + EXT_LEN)
    (hx : ∀ j, j < w → (extBytes p).getD (off - E_M0 + j) 0 = (leN w x).getD j 0) :
    ∀ j, j < w → (preparedBytesD1 p ov).getD (off + j) 0 = (leN w x).getD j 0 := by
  intro j hj
  rw [show off + j = E_M0 + (off - E_M0 + j) by omega, preparedD1_ext p ov hr (by omega)]
  exact hx j hj

theorem m0V_prepared (hm : p.m0 < 2 ^ 32) :
    m0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) = p.m0 :=
  leN'_window _ _ 4 _ (by simpa using hm) (ext_window p ov hr (Nat.le_refl _) (by simp [E_M0, EXT_LEN]) (by
    intro j hj
    simp only [Nat.sub_self, Nat.zero_add, extBytes, List.append_assoc]
    rw [getD_append_left' _ _ (by simp [u32, leN_length]; omega)]; rfl))

theorem t0V_prepared (ht : p.t0 < 2 ^ 32) :
    t0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) = p.t0 :=
  leN'_window _ _ 4 _ (by simpa using ht) (ext_window p ov hr (by simp [E_M0, E_T0]) (by simp [E_M0, E_T0, EXT_LEN]) (by
    intro j hj
    rw [show E_T0 - E_M0 + j = (u32 p.m0).length + j by simp [E_T0, E_M0, u32, leN_length]]
    simp only [extBytes, List.append_assoc]
    rw [getD_right, getD_append_left' _ _ (by simp [u32, leN_length]; omega)]; rfl))

theorem o0V_prepared (ho : p.o0 < 2 ^ 32) :
    o0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) = p.o0 :=
  leN'_window _ _ 4 _ (by simpa using ho) (ext_window p ov hr (by simp [E_M0, E_O0]) (by simp [E_M0, E_O0, EXT_LEN]) (by
    intro j hj
    rw [show E_O0 - E_M0 + j = (u32 p.m0 ++ u32 p.t0).length + j by simp [E_O0, E_M0, u32, leN_length]]
    simp only [extBytes, List.append_assoc]
    rw [← List.append_assoc, getD_right, getD_append_left' _ _ (by simp [u32, leN_length]; omega)]; rfl))

theorem tok0V_prepared (hk : p.tok0 < 2 ^ 128) :
    tok0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) = p.tok0 :=
  leN'_window _ _ 16 _ (by simpa using hk) (ext_window p ov hr (by simp [E_M0, E_TOK0]) (by simp [E_M0, E_TOK0, EXT_LEN]) (by
    intro j hj
    rw [show E_TOK0 - E_M0 + j = (u32 p.m0 ++ u32 p.t0 ++ u32 p.o0).length + j by
      simp [E_TOK0, E_M0, u32, leN_length]]
    simp only [extBytes]
    rw [getD_right]; rfl))

/-- **`ExtOk` of the D1 tape** under the native bounds (P2 provides them). -/
theorem extOk_prepared (hm : p.m0 < 2 ^ 24) (ht : p.t0 < 2 ^ 24) (ho : p.o0 < 2 ^ 30) :
    ExtOk (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) := by
  refine ⟨extBytes_pubOf _, ?_, ?_, ?_⟩
  · rw [m0V_prepared p ov hr (by omega)]; exact hm
  · rw [t0V_prepared p ov hr (by omega)]; exact ht
  · rw [o0V_prepared p ov hr (by omega)]; exact ho

end ZkFormal.NearV3.D1.Public
