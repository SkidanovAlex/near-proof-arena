//! `prepare --params <approved_params.bin> --out <public_dir>` — the v3 (D0a) entry point
//! (installed as `out/prepare` by build-recipe/build.sh; docs/CONTRACTS.md §4).
//!
//! The judge runs it with the challenge's approved parameters (`near-arena-params-v3`,
//! spec/claim-v3.md §4: `str format ‖ str statement ‖ u32 pv ‖ str domain_id ‖ hash
//! runtime_config_digest_v3`). It checks that they are EXACTLY the public tape the certificate
//! is about — `NpUdrStarkV2.publicBin` (formal/NpUdrStarkV2/PublicBin.lean, 100 bytes, sha256
//! `ab13c199…957f`, kernel-checked by `NpUdrStarkV2.publicDigest_eq`): statement
//! `near/pv86/chunk-validation/v0`, protocol version 86, domain `D0a`, runtime-config digest
//! `b7dce203…062f` (challenges/drafts/near-chunk-validation-d0-stark.draft.json) — and writes
//! them unchanged as `public_dir/public.bin`. The prover absorbs that file into the STARK
//! transcript and the verifier recomputes it, so any other tape gives rejected proofs; refusing
//! it here turns a challenge/candidate mismatch into a visible `prepare` failure instead.
//!
//! std only (no dependency on the prover library), so prover-only changes can never change
//! this artifact.

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

/// `runtime_config_digest_v3` of the D0a draft (`sha256:b7dce203…062f`).
const RUNTIME_CONFIG_DIGEST: [u8; 32] = [
    0xb7, 0xdc, 0xe2, 0x03, 0x4a, 0xea, 0xcd, 0x47, 0x0a, 0x0c, 0x4d, 0xbc, 0x2d, 0x56, 0x6e, 0x48,
    0x0f, 0xf9, 0xf0, 0xf1, 0x40, 0xa0, 0x7b, 0x50, 0x88, 0x99, 0x4e, 0x07, 0x87, 0xed, 0x06, 0x2f,
];

fn put_str(v: &mut Vec<u8>, s: &str) {
    v.extend_from_slice(&(s.len() as u32).to_le_bytes());
    v.extend_from_slice(s.as_bytes());
}

/// `NpUdrStarkV2.publicBin`, re-encoded with the `near-arena-params-v3` codec.
fn expected() -> Vec<u8> {
    let mut v = Vec::with_capacity(100);
    put_str(&mut v, "near-arena-params-v3");
    put_str(&mut v, "near/pv86/chunk-validation/v0");
    v.extend_from_slice(&86u32.to_le_bytes());
    put_str(&mut v, "D0a");
    v.extend_from_slice(&RUNTIME_CONFIG_DIGEST);
    v
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (params, out) = match args.as_slice() {
        [a, p, b, o] if a == "--params" && b == "--out" => (p, o),
        [b, o, a, p] if a == "--params" && b == "--out" => (p, o),
        _ => die("usage: prepare --params <params.bin> --out <public_dir>"),
    };
    let bytes = std::fs::read(params).unwrap_or_else(|e| die(&format!("params: {e}")));
    if bytes != expected() {
        die(
            "params: not the near-arena-params-v3 tape this candidate is certified for \
             (near/pv86/chunk-validation/v0, pv 86, domain D0a, runtime config sha256:b7dce203…062f; \
             NpUdrStarkV2.publicBin)",
        );
    }
    let out = std::path::Path::new(out);
    std::fs::create_dir_all(out).unwrap_or_else(|e| die(&format!("out: {e}")));
    std::fs::write(out.join("public.bin"), &bytes).unwrap_or_else(|e| die(&format!("write: {e}")));
}
