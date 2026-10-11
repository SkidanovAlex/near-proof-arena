import ArenaCore.Bytes

/-!
The public tape: `public.bin` written by `prepare` = the challenge's approved
`params.bin` (`near-arena-params-v3`, `spec/claim-v3.md` §4), verbatim. Its
SHA-256 is the `publicDigest` of the admission statement. The verifier model
ignores it.

The draft `near-chunk-validation-d0-stark` (`challenges/drafts/`) fixes the
statement `near/pv86/chunk-validation/v0` (protocol version 86) and the runtime
configuration digest `runtime_config_digest_v3` =
`b7dce203…062f` of `spec/challenge-inputs/runtime-config-pv86-v3.json`; the D0a
challenge is the bounded D0 tier of `near-chunk-v3` (`NearSpecV3.Tier.d0a`), so
the domain id is `"D0a"` (4 bytes). The wiring is `spec/tools/params_bin_v3.py`
plus the 32-byte runtime-config digest; the current tool has no `D0a` key in its
`CONFIGS` map (it still emits `D0` for the D0 draft), so this literal was
constructed by the same codec at `D0a` and its SHA-256 recorded below. If the
signed D0a challenge instead reuses the `D0` domain id, replace these bytes with
`spec/tools/params_bin_v3.py <out> D0` (the 99-byte literal, sha256
`88812d19…5330`, which is what `examples/reexec-v3-d0/formal/ReexecV3D0/PublicBin.lean`
pins).

100 bytes, sha256 `ab13c19970996ebe01bc3d9234f64a1a6a989715f8da8dd7f92e5ab5eac8957f`
(the kernel check is `NpUdrStarkV2.publicDigest_eq` in `Certificate.lean`).
-/

namespace NpUdrStarkV2

def publicBin : ArenaCore.Bytes :=
  [
   0x14, 0x00, 0x00, 0x00, 0x6e, 0x65, 0x61, 0x72, 0x2d, 0x61, 0x72, 0x65, 0x6e, 0x61, 0x2d, 0x70,
   0x61, 0x72, 0x61, 0x6d, 0x73, 0x2d, 0x76, 0x33, 0x1d, 0x00, 0x00, 0x00, 0x6e, 0x65, 0x61, 0x72,
   0x2f, 0x70, 0x76, 0x38, 0x36, 0x2f, 0x63, 0x68, 0x75, 0x6e, 0x6b, 0x2d, 0x76, 0x61, 0x6c, 0x69,
   0x64, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x2f, 0x76, 0x30, 0x56, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00,
   0x00, 0x44, 0x30, 0x61, 0xb7, 0xdc, 0xe2, 0x03, 0x4a, 0xea, 0xcd, 0x47, 0x0a, 0x0c, 0x4d, 0xbc,
   0x2d, 0x56, 0x6e, 0x48, 0x0f, 0xf9, 0xf0, 0xf1, 0x40, 0xa0, 0x7b, 0x50, 0x88, 0x99, 0x4e, 0x07,
   0x87, 0xed, 0x06, 0x2f]

end NpUdrStarkV2
