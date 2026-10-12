//! Developer CLI.
//!
//! * `npudr bench <width> <log_height> [tables] [--out <dir>]` — prove/verify a
//!   synthetic AIR (cube constraints, degree 4) and report time and proof
//!   size; with `--out`, also write `air.json`, `pub.bin`, `claim.bin`,
//!   `proof.bin` (for `np-lean-verify` timings).
//! * `npudr toy <fib|multi> <log> <outdir>` — write `air.json`, `claim.bin`,
//!   `proof.bin`, `pub.bin` for differential tests against the Lean
//!   verifier.
//! * `npudr verify [--aux-group g] <air.json> <pub.bin> <claim.bin> <proof.bin>` —
//!   Rust reference verifier; exit 0 iff accepted (`g` defaults to 1; v2 AIRs only).
//! * `npudr toy <pubseg1|pubseg2|pubseg3> <log> <outdir>` — the v2 toy
//!   (`toy::pubseg_air`, public segments) at `auxGroup` 1/2/3.
//! * `npudr layout <air.json> <g>` — per-table layout at `auxGroup = g`
//!   (compare with `np-lean-export-v3 --layout g`).
//! * `npudr export <fib|multi|sha>` — print the toy AIR in `np-air-v1`.
//! * `npudr toy sha <log> <outdir> [len ...]` — SHA-256 toy (src/sha.rs):
//!   messages of the given lengths (default: 1000-byte messages filling a
//!   SHA table of `2^log` rows), proved and written as for the other toys.
//! * `npudr shatrace <out.bin> <len>...` — dump the honest SHA table in the
//!   `np-lean-shatrace` format (cross-check against the Lean generator).
//! * `npudr shacheck <len>...` — evaluate every constraint of the SHA toy on
//!   every row of the honest traces and check bus balance.
//! * `npudr nearrender <request.bin> <witness.bin> <out.bin>` — the NEAR honest
//!   tables 1..6 and SHA messages in the `np-lean-render` format.
//! * `npudr nearcheck <request.bin> <witness.bin>` — evaluate every nearAir
//!   constraint on the honest traces (incl. sha) and check bus balance.
//! * `npudr nearcols <request.bin> <witness.bin>` — the compact honest traces
//!   (`near::prepare_cols`): heights and storage per table.
//! * `npudr nearcolscheck <request.bin> <witness.bin>` — `nearcheck` on the
//!   compact traces (`prepare_cols`; constraints + bus balance by message hash),
//!   for cases too large for the row-major traces.
//! * `npudr gen-max <out_dir> [--target-bytes N] [--n N] [--kids K] [--eps 0|1]`
//!   — synthesize a maximum-size in-domain case (`npudr::near::genmax`):
//!   `request.bin`, `witness.bin`, `expected_claim.bin`.
//! * `npudr prep-encode <prep.json> <out.bin>` — parse a Lean `np-lean-prep-v3`
//!   `prep_json` dump and write `v3::prep::Prep.encode` (part 3 differential).
//! * `npudr prep-hint <hint.bin> <out.bin>` — decode+re-encode the clear `Hint`
//!   (`v3::prep::Hint`); `npudr prep-body <refunds_enc.bin> <out.bin>` — the
//!   `decodeBody`/`bodyOf` refund codec round trip.
//! * `npudr d0-prep <claim.bin> <hint.bin> <out.json>` — the native D0
//!   preprocessing (`v3::d0::prep` = Lean `NearSpecV3.prepD0`) on a real
//!   `claim.bin` + hint; writes the `prep_json` dump for the Lean differential.
//! * `npudr v3prepare <claim.bin> <witness.bin> <out_dir> [--hint <hint.bin>]` —
//!   the prover's native preprocessing: `hintOf` (`v3::hint`) then `prepD0`
//!   (`v3::d0::prep`); writes `hint.bin` and, on acceptance, `prep.bin` +
//!   `prep.json` (exit 0), else `reject.txt` (exit 1).
use std::time::Instant;

use npudr::air::Air;
use npudr::prover::{ProveOptions, prove_bytes};
use npudr::verifier::verify;
use npudr::{check, near, sha, toy};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

fn die(m: &str) -> ! {
    eprintln!("npudr: {m}");
    std::process::exit(2)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("bench") => {
            let (pos, out): (Vec<&String>, Option<&String>) =
                match a.iter().position(|x| x == "--out") {
                    Some(i) => (a[2..i].iter().chain(&a[i + 2..]).collect(), a.get(i + 1)),
                    None => (a[2..].iter().collect(), None),
                };
            let w: usize = pos[0].parse().unwrap();
            let h: usize = pos[1].parse().unwrap();
            let nt: usize = pos.get(2).map(|s| s.parse().unwrap()).unwrap_or(1);
            let air = Air::v1((0..nt).map(|_| toy::cube_table(w, 22)).collect(), 0, 0);
            let traces: Vec<_> = (0..nt)
                .map(|i| toy::cube_trace(w, h.saturating_sub(i).max(1)))
                .collect();
            let pd = b"bench".to_vec();
            let t = Instant::now();
            let b = prove_bytes(&air, traces, &pd, &[], &ProveOptions { verbose: true })
                .unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
            let t = Instant::now();
            verify(&air, &pd, &[], &b).unwrap_or_else(|e| die(&e));
            let tv = t.elapsed().as_secs_f64();
            if let Some(dir) = out {
                let dir = std::path::Path::new(dir);
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
                std::fs::write(dir.join("pub.bin"), &pd).unwrap();
                std::fs::write(dir.join("claim.bin"), []).unwrap();
                std::fs::write(dir.join("proof.bin"), &b).unwrap();
            }
            println!(
                "tables={nt} width={w} log_h={h} prove={tp:.3}s proof={} B ({:.3} MiB) verify_rust={tv:.3}s threads={}",
                b.len(),
                b.len() as f64 / (1u64 << 20) as f64,
                rayon::current_num_threads()
            );
        }
        Some("toy") => {
            let t0 = Instant::now();
            let (air, traces, cb) = if a[2] == "sha" {
                let msgs = sha_msgs(a[3].parse().unwrap(), &a[5..]);
                (sha::sha_air(), sha::sha_traces(&msgs), vec![])
            } else {
                toy_instance(&a[2], a[3].parse().unwrap())
            };
            let tg = t0.elapsed().as_secs_f64();
            let dir = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(dir).unwrap();
            let pd = b"np-udr-stark toy public tape".to_vec();
            let shapes: Vec<String> = traces
                .iter()
                .map(|m| format!("{}x2^{}", m.width(), m.height().trailing_zeros()))
                .collect();
            let t = Instant::now();
            let b = prove_bytes(&air, traces, &pd, &cb, &ProveOptions { verbose: false })
                .unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
            let t = Instant::now();
            let ok = verify(&air, &pd, &cb, &b);
            let tv = t.elapsed().as_secs_f64();
            eprintln!(
                "toy {} tables=[{}] tracegen={tg:.3}s prove={tp:.3}s proof={} B verify_rust={tv:.3}s ({}) threads={}",
                a[2],
                shapes.join(","),
                b.len(),
                if ok.is_ok() {
                    "accept".to_string()
                } else {
                    format!("{ok:?}")
                },
                rayon::current_num_threads()
            );
            std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
            std::fs::write(dir.join("claim.bin"), &cb).unwrap();
            std::fs::write(dir.join("pub.bin"), &pd).unwrap();
            std::fs::write(dir.join("proof.bin"), b).unwrap();
        }
        Some("layout") => {
            // per table: t width aux degree quot sendG recvG maxLog (`np-lean-export-v3 --layout g`)
            let g: usize = a
                .get(3)
                .and_then(|x| x.parse().ok())
                .unwrap_or_else(|| die("usage: npudr layout <air.json> <g>"));
            let txt =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let air = Air::from_json(&txt)
                .unwrap_or_else(|e| die(&e))
                .with_aux_group(g);
            air.validate()
                .unwrap_or_else(|e| die(&format!("validate: {e}")));
            for (t, tab) in air.tables.iter().enumerate() {
                let lay = npudr::aux::AuxLayout::new(tab, g);
                println!(
                    "{t} {} {} {} {} {} {} {}",
                    tab.width,
                    lay.width(),
                    tab.degree(g),
                    tab.num_quot_chunks(g),
                    lay.send_groups,
                    lay.recv_groups,
                    tab.max_log
                );
            }
        }
        Some("v3sample") => {
            // seeded random honest entries of one nearAirV3 table (JSON on stdout)
            let usage = "usage: npudr v3sample <table> <seed> <n>";
            let seed: u64 = a
                .get(3)
                .and_then(|x| x.parse().ok())
                .unwrap_or_else(|| die(usage));
            let n: usize = a
                .get(4)
                .and_then(|x| x.parse().ok())
                .unwrap_or_else(|| die(usage));
            let j = npudr::v3::sample::sample_json(&a[2], seed, n).unwrap_or_else(|e| die(&e));
            println!("{j}");
        }
        Some("v3entries") => {
            // parse a Lean `np-lean-entries-v3` dump (part 2c) and report its shape
            if a.len() != 4 {
                die("usage: npudr v3entries <table> <entries.json>");
            }
            let j =
                std::fs::read_to_string(&a[3]).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            println!(
                "{}",
                npudr::v3::entries::describe(&a[2], &j).unwrap_or_else(|e| die(&e))
            );
        }
        Some("v3sha") => {
            // `npudr v3sha <entries-dir> <sha_t.json> <sha_r.json>`: collect the
            // SHA messages of the per-table entry files in <dir> and split them
            // into the two instances by the §12 kind registry.
            if a.len() != 5 {
                die("usage: npudr v3sha <entries-dir> <sha_t.json> <sha_r.json>");
            }
            let dir = &a[2];
            let mut entries = std::collections::HashMap::new();
            for (name, _) in npudr::v3::TABLES {
                let f = format!("{dir}/{name}.json");
                if let Ok(j) = std::fs::read_to_string(&f) {
                    entries.insert((*name).to_string(), j);
                }
            }
            let (t, r) =
                npudr::v3::collect::instances_from_entries(&entries).unwrap_or_else(|e| die(&e));
            std::fs::write(&a[3], t).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            std::fs::write(&a[4], r).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
        }
        Some("v3render") => {
            // aligned trace of one table (`np-lean-render-v3` format)
            if a.len() != 5 {
                die("usage: npudr v3render <table> <entries.json> <out.bin>");
            }
            let j =
                std::fs::read_to_string(&a[3]).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            let tab = npudr::v3::render(&a[2], &j).unwrap_or_else(|e| die(&e));
            std::fs::write(&a[4], tab.dump()).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
        }
        Some("prep-encode") => {
            // `npudr prep-encode <prep.json> <out.bin>`: parse the Lean-dumped
            // `Prep` (`prep_json`, or a bare object) and write `Prep.encode`.
            if a.len() != 4 {
                die("usage: npudr prep-encode <prep.json> <out.bin>");
            }
            let txt =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let val: serde_json::Value =
                serde_json::from_str(&txt).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let pj = val.get("prep_json").cloned().unwrap_or(val);
            let p: npudr::v3::prep::Prep =
                serde_json::from_value(pj).unwrap_or_else(|e| die(&format!("prep_json: {e}")));
            std::fs::write(&a[3], p.encode()).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
        }
        Some("prep-hint") => {
            // `npudr prep-hint <hint.bin> <out.bin>`: decode then re-encode the
            // clear `Hint` (`ZkFormal.NearV3.Assembly.Hint`).  The bytes must
            // equal the input.
            if a.len() != 4 {
                die("usage: npudr prep-hint <hint.bin> <out.bin>");
            }
            let raw = std::fs::read(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let h = npudr::v3::prep::Hint::decode(&raw).unwrap_or_else(|e| die(&e));
            std::fs::write(&a[3], h.encode()).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
        }
        Some("prep-body") => {
            // `npudr prep-body <refunds_enc.bin> <out.bin>`: decode `encodeReceipts rs`,
            // rebuild `bodyOf rs = u32 0 ‖ encodeReceipts rs`, then check
            // `decodeBody (bodyOf rs) = rs` and write `encodeReceipts rs` back.
            if a.len() != 4 {
                die("usage: npudr prep-body <refunds_enc.bin> <out.bin>");
            }
            use npudr::v3::prep::{body_of, decode_body, decode_receipts};
            let raw = std::fs::read(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let (rs, used) = decode_receipts(&raw).unwrap_or_else(|e| die(&e));
            if used != raw.len() {
                die("prep-body: trailing bytes in refunds");
            }
            let body = body_of(&rs);
            let back = decode_body(&body).unwrap_or_else(|e| die(&e));
            if back != rs {
                die("prep-body: decodeBody(bodyOf rs) != rs");
            }
            std::fs::write(&a[3], npudr::near::spec::encode_receipts(&rs))
                .unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
        }
        Some("v3check") => {
            // local constraints of the rendered table against its nearAirV3 table
            if a.len() != 5 {
                die("usage: npudr v3check <air.json> <table> <entries.json>");
            }
            let txt =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let air = Air::from_json(&txt).unwrap_or_else(|e| die(&e));
            let idx = npudr::v3::TABLES
                .iter()
                .find(|(n, _)| *n == a[3])
                .map(|p| p.1)
                .unwrap_or_else(|| die("unknown table"));
            let j =
                std::fs::read_to_string(&a[4]).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
            let tab = npudr::v3::render(&a[3], &j).unwrap_or_else(|e| die(&e));
            let t = &air.tables[idx];
            if t.width != tab.width {
                die(&format!(
                    "width {} != nearAirV3 table {idx} width {}",
                    tab.width, t.width
                ));
            }
            if tab.log < 1 || tab.log > t.max_log {
                die(&format!(
                    "log {} outside 1..={} (table {idx})",
                    tab.log, t.max_log
                ));
            }
            let pubs = vec![npudr::field::F::ZERO; air.num_pub];
            let bad = npudr::check::failing_constraints(t, &tab.to_matrix(), &pubs, 20);
            if bad.is_empty() {
                println!(
                    "ok  {} (table {idx}): log {} width {}, all constraints hold",
                    a[3], tab.log, tab.width
                );
            } else {
                for (c, r) in &bad {
                    println!("FAIL constraint {c} row {r}");
                }
                std::process::exit(1);
            }
        }
        Some("v3prove") => {
            // `npudr v3prove <nearAirV3.json> <prep.json> <entries-dir> <pub.bin> <cb.bin> <proof-out>
            // Build the 25-table trace from per-table entries (files `<dir>/<table>.json`),
            // the prepared public tape from <prep.json>, and prove at aux_group=2.
            if a.len() != 8 {
                die(
                    "usage: npudr v3prove <air.json> <prep.json> <entries-dir> <pub.bin> <cb.bin> <proof-out>",
                );
            }
            let atxt =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let air = Air::from_json(&atxt)
                .unwrap_or_else(|e| die(&e))
                .with_aux_group(2);
            let pj =
                std::fs::read_to_string(&a[3]).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            let prep = npudr::v3::prep::Prep::from_json(&pj).unwrap_or_else(|e| die(&e));
            let dir = &a[4];
            let mut entries = std::collections::HashMap::new();
            for (name, _) in npudr::v3::TABLES {
                let f = format!("{dir}/{name}.json");
                if let Ok(j) = std::fs::read_to_string(&f) {
                    entries.insert((*name).to_string(), j);
                }
            }
            // The two SHA instances need the union of all table messages; the
            // collector builds them from the other tables unless an explicit
            // `sha_t.json`/`sha_r.json` was supplied.
            let entries =
                npudr::v3::prove::with_collected_sha(&entries).unwrap_or_else(|e| die(&e));
            let work = move || -> Result<Vec<u8>, String> {
                let traces = npudr::v3::prove::traces_from_entries(&air, &entries)?;
                let pub_tape = npudr::v3::public::prepared_bytes(&prep, 0);
                std::fs::write(&a[5], &pub_tape).map_err(|e| e.to_string())?;
                let cb = std::fs::read(&a[6]).unwrap_or_default();
                let proof = npudr::prover::prove_cols_bytes(
                    &air,
                    traces,
                    &pub_tape,
                    &cb,
                    &ProveOptions { verbose: true },
                )?;
                std::fs::write(&a[7], &proof).map_err(|e| e.to_string())?;
                Ok(proof)
            };
            match work() {
                Ok(p) => println!("proof {} B", p.len()),
                Err(e) => die(&e),
            }
        }
        Some("v3public") => {
            // `npudr v3public <prep.json> <out.bin>`: the prepared public tape.
            if a.len() != 4 {
                die("usage: npudr v3public <prep.json> <out.bin>");
            }
            let pj =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let prep = npudr::v3::prep::Prep::from_json(&pj).unwrap_or_else(|e| die(&e));
            let b = npudr::v3::public::prepared_bytes(&prep, 0);
            std::fs::write(&a[3], &b).unwrap_or_else(|e| die(&format!("{e}")));
            println!("public {} B", b.len());
        }
        Some("d0-prep") => {
            // `npudr d0-prep <claim.bin> <hint.bin> <out.json>`: run the native D0
            // preprocessing (`v3::d0::prep`) and write the `prep_json` dump (with
            // the Lean `np-lean-prep-v3` field names), for the differential below.
            if a.len() != 5 {
                die("usage: npudr d0-prep <claim.bin> <hint.bin> <out.json>");
            }
            let cb = std::fs::read(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let hb = std::fs::read(&a[3]).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            let hint = npudr::v3::prep::Hint::decode(&hb).unwrap_or_else(|e| die(&e));
            let p = npudr::v3::d0::prep(&cb, &hint).unwrap_or_else(|e| die(&e));
            let j = npudr::v3::d0::to_json(&p);
            std::fs::write(
                &a[4],
                serde_json::to_vec(&j).unwrap_or_else(|e| die(&e.to_string())),
            )
            .unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
            println!("prep {} B", p.encode().len());
        }
        Some("v3prepare") => {
            // `npudr v3prepare <claim.bin> <witness.bin> <out_dir> [--hint <hint.bin>]`:
            // the prover's native preprocessing.  `h := hintOf cb w` (`v3::hint`, or
            // the given hint bytes), then `prepD0 cb h` (`v3::d0::prep`).  Always
            // writes `hint.bin` (`Hint.encode h`); on acceptance also `prep.bin`
            // (`Prep.encode`) and `prep.json`, exit 0; on rejection `reject.txt`,
            // exit 1.
            let (hint_path, a) = match a.iter().position(|x| x == "--hint") {
                Some(i) => (
                    Some(a.get(i + 1).cloned().unwrap_or_else(|| die("--hint"))),
                    a[..i]
                        .iter()
                        .chain(&a[i + 2..])
                        .cloned()
                        .collect::<Vec<_>>(),
                ),
                None => (None, a.clone()),
            };
            if a.len() != 5 {
                die(
                    "usage: npudr v3prepare <claim.bin> <witness.bin> <out_dir> [--hint <hint.bin>]",
                );
            }
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let cb = rd(&a[2]);
            let wb = rd(&a[3]);
            let hint = match &hint_path {
                Some(p) => npudr::v3::prep::Hint::decode(&rd(p)).unwrap_or_else(|e| die(&e)),
                None => npudr::v3::hint::hint_of(&cb, &wb),
            };
            let od = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(od).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
            let wr = |name: &str, b: &[u8]| {
                std::fs::write(od.join(name), b).unwrap_or_else(|e| die(&format!("{name}: {e}")))
            };
            wr("hint.bin", &hint.encode());
            match npudr::v3::d0::prep(&cb, &hint) {
                Ok(p) => {
                    let pb = p.encode();
                    wr("prep.bin", &pb);
                    let j = npudr::v3::d0::to_json(&p);
                    wr(
                        "prep.json",
                        &serde_json::to_vec(&j).unwrap_or_else(|e| die(&e.to_string())),
                    );
                    println!(
                        "accept: n {} hint {} B prep {} B",
                        hint.n,
                        hint.encode().len(),
                        pb.len()
                    );
                }
                Err(e) => {
                    wr("reject.txt", e.as_bytes());
                    println!("reject: {e}");
                    std::process::exit(1);
                }
            }
        }
        Some("verify") => {
            // optional `--aux-group g` (a proof parameter, not part of the AIR JSON)
            let (g, a) = match a.iter().position(|x| x == "--aux-group") {
                Some(i) => {
                    let g: usize = a
                        .get(i + 1)
                        .and_then(|x| x.parse().ok())
                        .unwrap_or_else(|| die("--aux-group"));
                    (
                        g,
                        a[..i]
                            .iter()
                            .chain(&a[i + 2..])
                            .cloned()
                            .collect::<Vec<_>>(),
                    )
                }
                None => (1, a.clone()),
            };
            let rd = |p: &String| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let air =
                Air::from_json(&String::from_utf8(rd(&a[2])).unwrap()).unwrap_or_else(|e| die(&e));
            if !(1..=3).contains(&g) || (!air.v2 && g != 1) {
                die("--aux-group: 1..=3, and only for np-air-v2");
            }
            let air = air.with_aux_group(g);
            let pd = rd(&a[3]);
            match verify(&air, &pd, &rd(&a[4]), &rd(&a[5])) {
                Ok(()) => println!("accept"),
                Err(e) => {
                    println!("reject: {e}");
                    std::process::exit(1)
                }
            }
        }
        Some("eval-random") => {
            use npudr::field::{EF, decode_chal};
            use p3_field::PrimeField32;
            let air = Air::from_json(&std::fs::read_to_string(&a[2]).unwrap())
                .unwrap_or_else(|e| die(&e));
            let seed: u32 = a[3].parse().unwrap();
            let rnd = |kind: u8, t: usize, i: usize| -> EF {
                let mut m = b"np-eval".to_vec();
                m.extend_from_slice(&seed.to_le_bytes());
                m.push(kind);
                m.extend_from_slice(&(t as u32).to_le_bytes());
                m.extend_from_slice(&(i as u32).to_le_bytes());
                decode_chal(&npudr::hash::sha256(&m))
            };
            for (t, tab) in air.tables.iter().enumerate() {
                let tape = npudr::air::Tape::compile(&tab.constraints);
                // pub(i) values are extension elements here: evaluate with a tape over EF
                let mut regs = vec![];
                tape.eval_ext(
                    &mut regs,
                    |c, n| rnd(n as u8, t, c),
                    |i| rnd(2, t, i),
                    [rnd(3, t, 0), rnd(4, t, 0), rnd(5, t, 0)],
                );
                for (i, &o) in tape.outputs.iter().enumerate() {
                    let ls: Vec<String> = npudr::field::ef_coeffs(&regs[o as usize])
                        .iter()
                        .map(|x| x.as_canonical_u32().to_string())
                        .collect();
                    println!("{t} {i} {}", ls.join(" "));
                }
            }
        }
        Some("shatrace") => {
            let lens: Vec<usize> = a[3..].iter().map(|s| s.parse().unwrap()).collect();
            std::fs::write(&a[2], sha::dump_trace(&sha::toy_msgs(&lens))).unwrap();
        }
        Some("shacheck") => {
            let lens: Vec<usize> = a[2..].iter().map(|s| s.parse().unwrap()).collect();
            let msgs = sha::toy_msgs(&lens);
            let air = sha::sha_air();
            let trs = sha::sha_traces(&msgs);
            let mut bad = false;
            for (ti, (t, tr)) in air.tables.iter().zip(&trs).enumerate() {
                let f = check::failing_constraints(t, tr, &[], 20);
                println!(
                    "table {ti} ({}): {} constraints, failing (constraint, row): {:?}",
                    t.name,
                    t.constraints.len(),
                    f
                );
                bad |= !f.is_empty();
            }
            let im = check::bus_imbalance(&air, &trs, &[]);
            println!(
                "bus imbalance: {} message(s) {:?}",
                im.len(),
                im.iter().take(5).collect::<Vec<_>>()
            );
            if bad || !im.is_empty() {
                std::process::exit(1)
            }
        }
        Some("export") => {
            if a[2] == "sha" {
                println!("{}", sha::sha_air().to_json());
                return;
            }
            let (air, _, _) = toy_instance(&a[2], 3);
            println!("{}", air.to_json());
        }
        Some("nearrender") => {
            let t = Instant::now();
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let (c, e) = near::load(&req, &wit).unwrap_or_else(|e| die(&e));
            let b = near::trace::bundle(&c, &e);
            if !b.errors.is_empty() {
                eprintln!("npudr nearrender: walk errors {:?}", b.errors);
            }
            std::fs::write(&a[4], near::dump(&c.encode(), &b)).unwrap();
            let rows: Vec<usize> = b.parts().iter().map(|p| p.2.len()).collect();
            eprintln!(
                "npudr nearrender: {} nodes, {} receipts, {} msgs, rows {rows:?}, {} ms",
                e.ns.len(),
                e.rs.len(),
                b.msgs.len(),
                t.elapsed().as_millis()
            );
        }
        Some("nearcheck") => {
            // every constraint of every nearAir table on the honest traces, and bus balance
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let t = Instant::now();
            // with an empty (stub) rcpt table, its traffic is simulated (RcptSim):
            // sha also hashes `rcpt_msgs_sim`, and the remaining imbalance must be
            // exactly `rcpt_bus_sim ++ bytes_sends rcpt_msgs_sim`.
            let (c, e) = near::load(&req, &wit).unwrap_or_else(|e| die(&e));
            let mut b = near::trace::bundle(&c, &e);
            let sim = b.rcpt.is_empty();
            let mut simbus = vec![];
            if sim {
                let rm = near::sim::rcpt_msgs_sim(&b.info);
                simbus = near::sim::rcpt_bus_sim(&b.info);
                simbus.extend(near::sim::bytes_sends(&rm));
                b.msgs.extend(rm);
                println!(
                    "rcpt table is the stub: simulating its traffic ({} bus messages)",
                    simbus.len()
                );
            }
            let (cb, air, trs) = (c.encode(), near::near_air(), near::trace::bundle_traces(&b));
            let tg = t.elapsed().as_millis();
            let pubs = near::public_of(&cb);
            let names = ["sha", "node", "walk", "rcpt", "acct", "mrk", "sort"];
            let mut bad = false;
            for (k, (tab, tr)) in air.tables.iter().zip(&trs).enumerate() {
                let f = check::failing_constraints(tab, tr, &pubs, 20);
                println!(
                    "table {k} {:5} {:>8} x {:3}: {} failing (constraint,row) {:?}",
                    names[k],
                    tr.height(),
                    tr.width(),
                    f.len(),
                    f
                );
                bad |= !f.is_empty() && !(sim && k == 3);
            }
            let mut imb = check::bus_imbalance(&air, &trs, &pubs);
            if sim {
                // add the simulated rcpt traffic; keys not reported were balanced
                let mut m: std::collections::BTreeMap<(usize, Vec<u32>), (i64, i64)> =
                    std::collections::BTreeMap::new();
                for (bus, msg, s, r) in &imb {
                    m.insert((*bus, msg.clone()), (*s as i64, *r as i64));
                }
                let mut delta: std::collections::BTreeMap<(usize, Vec<u32>), i64> =
                    std::collections::BTreeMap::new();
                for x in &simbus {
                    *delta.entry((x.bus, x.msg.clone())).or_default() +=
                        if x.send { 1 } else { -1 };
                }
                for (k, d) in delta {
                    let ent = m.entry(k).or_insert((0, 0));
                    if d > 0 { ent.0 += d } else { ent.1 -= d }
                }
                imb = m
                    .into_iter()
                    .filter(|(_, (s, r))| s != r)
                    .map(|((b, msg), (s, r))| (b, msg, s as u64, r as u64))
                    .collect();
            }
            let mut per_bus = std::collections::BTreeMap::new();
            for (bus, _, _, _) in &imb {
                *per_bus.entry(*bus).or_insert(0usize) += 1;
            }
            println!("bus imbalance: {} messages, per bus {per_bus:?}", imb.len());
            for (bus, msg, s, r) in imb.iter().take(10) {
                println!(
                    "  bus {bus} msg {:?} sent {s} received {r}",
                    &msg[..msg.len().min(12)]
                );
            }
            println!("render {tg} ms, check {} ms", t.elapsed().as_millis() - tg);
            if bad || !imb.is_empty() {
                std::process::exit(1);
            }
        }
        Some("nearcols") => {
            // compact honest traces (prepare_cols): heights, storage, time
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let t = Instant::now();
            let (_, _, trs) = near::with_big_stack(move || near::prepare_cols(&req, &wit))
                .unwrap_or_else(|e| die(&e));
            let names = ["sha", "node", "walk", "rcpt", "acct", "mrk", "sort"];
            for (k, tr) in trs.iter().enumerate() {
                println!(
                    "table {k} {:5} 2^{:2} x {:3}: {:.1} MiB",
                    names[k],
                    tr.log_h,
                    tr.width(),
                    tr.bytes() as f64 / (1 << 20) as f64
                );
            }
            println!(
                "total {:.1} MiB, {} ms",
                trs.iter().map(|t| t.bytes()).sum::<usize>() as f64 / (1 << 20) as f64,
                t.elapsed().as_millis()
            );
        }
        Some("nearcolscheck") => {
            // nearcheck on the compact traces (prepare_cols): for cases (the max case)
            // whose row-major u64 traces do not fit in memory
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let t = Instant::now();
            let (cb, air, trs) = near::with_big_stack(move || near::prepare_cols(&req, &wit))
                .unwrap_or_else(|e| die(&e));
            let tg = t.elapsed().as_millis();
            let pubs = near::public_of(&cb);
            let names = ["sha", "node", "walk", "rcpt", "acct", "mrk", "sort"];
            let mut bad = false;
            for (k, (tab, tr)) in air.tables.iter().zip(&trs).enumerate() {
                let f = check::failing_constraints_cols(tab, tr, &pubs, 20);
                println!(
                    "table {k} {:5} 2^{:2} x {:3}: {} failing (constraint,row) {:?}",
                    names[k],
                    tr.log_h,
                    tr.width(),
                    f.len(),
                    f
                );
                bad |= !f.is_empty();
            }
            let (per_bus, total) = check::bus_imbalance_cols(&air, &trs, &pubs);
            println!("bus traffic: {total} sends; imbalanced messages per bus {per_bus:?}");
            println!(
                "render_cols {tg} ms, check {} ms",
                t.elapsed().as_millis() - tg
            );
            if bad || !per_bus.is_empty() {
                std::process::exit(1);
            }
        }
        Some("gen-max") => {
            let out = a.get(2).unwrap_or_else(|| {
                die("gen-max <out_dir> [--target-bytes N] [--n N] [--kids K] [--eps 0|1]")
            });
            let mut o = near::genmax::Opts::default();
            let mut it = a[3..].iter();
            while let Some(f) = it.next() {
                let v = it
                    .next()
                    .unwrap_or_else(|| die(&format!("{f} needs a value")));
                let num = || -> u64 {
                    v.parse()
                        .unwrap_or_else(|_| die(&format!("{f}: not a number")))
                };
                match f.as_str() {
                    "--target-bytes" => o.target_bytes = num(),
                    "--n" => o.n = Some(num() as usize),
                    "--kids" => o.kids = num() as usize,
                    "--eps" => o.eps = num() != 0,
                    _ => die(&format!("unknown flag {f}")),
                }
            }
            let t = Instant::now();
            let c =
                near::with_big_stack(move || near::genmax::gen_max(&o)).unwrap_or_else(|e| die(&e));
            let dir = std::path::Path::new(out);
            std::fs::create_dir_all(dir).unwrap_or_else(|e| die(&format!("{out}: {e}")));
            for (f, b) in [
                ("request.bin", &c.request),
                ("witness.bin", &c.witness),
                ("expected_claim.bin", &c.claim),
            ] {
                std::fs::write(dir.join(f), b).unwrap_or_else(|e| die(&format!("{f}: {e}")));
            }
            println!(
                "gen-max {out}: n={} revealedBytes={} branches={} empty-key exts={} leaves={} request={} B witness={} B ({} ms; claim = reexec deriveClaim)",
                c.n,
                c.revealed,
                c.branches,
                c.exts,
                c.leaves,
                c.request.len(),
                c.witness.len(),
                t.elapsed().as_millis()
            );
        }
        _ => die(
            "usage: npudr bench|toy|verify|export|nearrender|nearcheck|nearcols|nearcolscheck|gen-max ...",
        ),
    }
}

fn toy_instance(
    which: &str,
    log: usize,
) -> (
    Air,
    Vec<p3_matrix::dense::RowMajorMatrix<npudr::field::F>>,
    Vec<u8>,
) {
    let (tr, last) = toy::fib_trace(log, 1, 1);
    let cb = toy::fib_claim(1, 1, last);
    match which {
        "fib" => (toy::fib_air(), vec![tr], cb),
        "multi" => (
            toy::multi_air(),
            vec![
                tr,
                toy::cube_trace(3, log.saturating_sub(2).max(1)),
                toy::cube_trace(1, 1),
            ],
            cb,
        ),
        "bus" => {
            let lr = 4.max(log.saturating_sub(2));
            let xs: Vec<u32> = (0..(1u32 << log)).map(|i| (i * 7) % (1 << lr)).collect();
            (toy::bus_air(), toy::bus_traces(lr, log, &xs), vec![])
        }
        "wide" => {
            let w = 64;
            let air = Air::v1(vec![toy::cube_table(w, 22)], 0, 0);
            (air, vec![toy::cube_trace(w, log)], vec![])
        }
        "pubseg1" | "pubseg2" | "pubseg3" => {
            // v2 toy (public segments) at auxGroup 1/2/3; `log` sizes every table
            let g: usize = which[6..].parse().unwrap();
            let lr = 4.max(log.saturating_sub(2));
            let xs: Vec<u32> = (0..(1u32 << log)).map(|i| (i * 7) % (1 << lr)).collect();
            let n_in = (1usize << log) - 3;
            let recs: Vec<(u8, u8)> = (0..n_in)
                .map(|j| ((j * 37) as u8, (255 - j) as u8))
                .collect();
            let vals: Vec<u8> = (0..(1usize << (log - 1)) - 1)
                .map(|j| (j * 51) as u8)
                .collect();
            let cb = toy::pubseg_claim(&recs, &vals, 5);
            (
                toy::pubseg_air(g),
                toy::pubseg_traces(lr, log, &xs, log, &recs, log - 1, &vals),
                cb,
            )
        }
        _ => die("toy: fib|multi|bus|wide|pubseg1|pubseg2|pubseg3"),
    }
}

/// SHA toy messages: explicit lengths, or 1000-byte messages filling `2^log`
/// SHA rows (each takes 1 + 17·16 = 273 rows).
fn sha_msgs(log: usize, lens: &[String]) -> Vec<sha::Msg> {
    let lens: Vec<usize> = if lens.is_empty() {
        vec![1000; ((1usize << log) / 273).max(1)]
    } else {
        lens.iter().map(|s| s.parse().unwrap()).collect()
    };
    sha::toy_msgs(&lens)
}
