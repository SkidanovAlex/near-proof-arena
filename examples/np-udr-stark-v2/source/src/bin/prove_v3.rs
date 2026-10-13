//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>` — the v3 (D0a) entry point
//! (installed as `out/prove` by build-recipe/build.sh; docs/CONTRACTS.md §4).
//!
//! `near-arena-claim-v3`: the request IS the claim (the judge's arena layout has
//! `request = expected_claim = claim.bin`, runners/worker/src/oracle.rs `NearV3Oracle`), so
//! `claim.bin` is written as the request bytes, unchanged. The proof is exactly what
//! `npudr v3prove` produces (and what `conformance/run-v2.d/prove.sh` checks against the
//! deployed Lean verifier):
//!
//! 1. `v3::prove::case_inputs`: hint `h = hintOf cb w`, prepared statement
//!    `cb' = Public.preparedBytes (prepD0 cb h) 0`, the honest entries of all 25 `nearAirV3`
//!    tables, natively from claim + witness (an out-of-domain / rejected claim is an `Err`);
//! 2. render the 25 tables into compact columns (shape checked against the AIR);
//! 3. the STARK at `auxGroup = 2` over (`public.bin`, `cb'`); proof `= join (Hint.encode h) π`
//!    (`ZkFormal.NearV3.Assembly.split`/`join`);
//! 4. the Rust verifier re-checks `π` (every constraint, every bus incl. the public messages)
//!    before anything is written.
//!
//! The AIR is the committed Lean export `source/near-air-v3.json`
//! (`np-lean-export-v3` = `ZkFormal.V2.AirP.exportJson nearAirV3`, sha256 `fa599b3b…b452`),
//! compiled in. Any failure exits 2 and writes nothing (an error is never an accept); panics are
//! caught (release profile `panic = "unwind"`) on a big-stack thread; the outputs are written
//! only after success, each to a temporary file renamed into place.
//! `NPUDR_VERBOSE=1` prints per-phase timings on stderr; `NPUDR_MEM_GB` is the prover's memory
//! budget (`npudr::prover`, default 11; the judge passes no environment, so the default holds).
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// `ZkFormal.NearV3.Assembly.nearAirV3`, exported by `np-lean-export-v3`.
const NEAR_AIR_V3_JSON: &str = include_str!("../../near-air-v3.json");
/// The `ZkFormal.V2.G.pg g` instance of the deployed model (`NpUdrStarkV2.Model.verifier`).
const AUX_GROUP: usize = 2;

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

/// `--flag value` pairs; every expected flag exactly once, nothing else.
fn parse_args(expected: &[&str]) -> BTreeMap<String, PathBuf> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = BTreeMap::new();
    let mut it = args.into_iter();
    while let Some(flag) = it.next() {
        let Some(name) = flag.strip_prefix("--") else {
            die(&format!("unexpected argument {flag}"))
        };
        if !expected.contains(&name) {
            die(&format!("unknown flag --{name}"));
        }
        let Some(v) = it.next() else {
            die(&format!("--{name} needs a value"))
        };
        if out.insert(name.to_string(), PathBuf::from(v)).is_some() {
            die(&format!("duplicate flag --{name}"));
        }
    }
    for e in expected {
        if !out.contains_key(*e) {
            die(&format!("missing --{e}"));
        }
    }
    out
}

/// Write `bytes` to `<path>.tmp-<pid>`; returns the temporary path.
fn write_tmp(path: &Path, bytes: &[u8]) -> Result<PathBuf, String> {
    let mut name = path
        .file_name()
        .ok_or_else(|| format!("{}: not a file path", path.display()))?
        .to_os_string();
    name.push(format!(".tmp-{}", std::process::id()));
    let tmp = path.with_file_name(name);
    std::fs::write(&tmp, bytes).map_err(|e| {
        let _ = std::fs::remove_file(&tmp);
        format!("{}: {e}", path.display())
    })?;
    Ok(tmp)
}

/// Write both outputs or neither.
fn write_outputs(outs: &[(&Path, &[u8])]) -> Result<(), String> {
    let mut tmps: Vec<PathBuf> = vec![];
    let cleanup = |tmps: &[PathBuf]| tmps.iter().for_each(|t| drop(std::fs::remove_file(t)));
    for (p, b) in outs {
        match write_tmp(p, b) {
            Ok(t) => tmps.push(t),
            Err(e) => {
                cleanup(&tmps);
                return Err(e);
            }
        }
    }
    for (k, ((p, _), t)) in outs.iter().zip(&tmps).enumerate() {
        if let Err(e) = std::fs::rename(t, p) {
            cleanup(&tmps[k..]);
            for (q, _) in &outs[..k] {
                let _ = std::fs::remove_file(q);
            }
            return Err(format!("{}: {e}", p.display()));
        }
    }
    Ok(())
}

fn main() {
    let a = parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    let pub_tape = std::fs::read(a["public"].join("public.bin"))
        .unwrap_or_else(|e| die(&format!("public: {e}")));
    let claim = std::fs::read(&a["request"]).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| die(&format!("witness: {e}")));
    let verbose = std::env::var("NPUDR_VERBOSE").is_ok_and(|v| v == "1");
    let cb = claim.clone();
    let work = move || -> Result<Vec<u8>, String> {
        use npudr::v3::prove as vp;
        let t0 = std::time::Instant::now();
        let air = npudr::air::Air::from_json(NEAR_AIR_V3_JSON)?.with_aux_group(AUX_GROUP);
        let ci = vp::case_inputs(&cb, &wit, None)?;
        let hb = ci.hint.encode();
        if verbose {
            eprintln!(
                "[prove] entries {:.2} s; hint {} B, prepared {} B",
                t0.elapsed().as_secs_f64(),
                hb.len(),
                ci.tape.len()
            );
        }
        if air.tables.len() != vp::ORDER.len() {
            return Err(format!(
                "AIR has {} tables, prover renders {}",
                air.tables.len(),
                vp::ORDER.len()
            ));
        }
        let mut traces = Vec::with_capacity(vp::ORDER.len());
        for (t, name) in vp::ORDER.iter().enumerate() {
            let e = ci
                .entries
                .get(*name)
                .ok_or_else(|| format!("table {t} {name}: no entries"))?;
            let tc = vp::render_cols(name, e)?;
            let tab = &air.tables[t];
            if tc.width() != tab.width || tc.log_h < 1 || tc.log_h > tab.max_log {
                return Err(format!(
                    "table {t} {name}: shape log {} width {} vs nearAirV3 width {} maxLog {}",
                    tc.log_h,
                    tc.width(),
                    tab.width,
                    tab.max_log
                ));
            }
            traces.push(tc);
        }
        if verbose {
            eprintln!("[prove] traces {:.2} s", t0.elapsed().as_secs_f64());
        }
        let opts = npudr::prover::ProveOptions { verbose };
        let pi = npudr::prover::prove_cols_bytes(&air, traces, &pub_tape, &ci.tape, &opts)?;
        npudr::verifier::verify(&air, &pub_tape, &ci.tape, &pi)
            .map_err(|e| format!("self-check: the Rust verifier rejects the proof: {e}"))?;
        let proof = vp::join(&hb, &pi);
        if verbose {
            eprintln!(
                "[prove] total {:.2} s; proof {} B (stark {} B, hint {} B)",
                t0.elapsed().as_secs_f64(),
                proof.len(),
                pi.len(),
                hb.len()
            );
        }
        Ok(proof)
    };
    let proof = npudr::near::with_big_stack(work).unwrap_or_else(|e| die(&e));
    write_outputs(&[(&a["claim-out"], &claim), (&a["proof-out"], &proof)])
        .unwrap_or_else(|e| die(&e));
}
