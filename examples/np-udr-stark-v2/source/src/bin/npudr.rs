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
            // `npudr v3sha <entries-dir> <sha_t.json> <sha_r.json> [<full.json>]`:
            // build the four SHA job families (scheduler, native, receipt, source)
            // from the per-table entry files `<dir>/<table>.json` (plus the external
            // family lists `sha_scheduler.json` / `sha_receipt.json` when the
            // tables are absent) and write the two bins `twoShaJobBins = [b0, b1]`
            // (`sha_t`, `sha_r`).  `<full.json>`: bins, families, notes and the
            // bus check (`np-lean-shabins-v3` layout).
            // `--native <claim.bin> <witness.bin>`: the receipt-side entries (`rcpt`,
            // `acct`, `srcp`, `mrk`) are computed from the claim + witness
            // (`v3::rcptfam`) instead of read from the directory, and an external
            // `sha_receipt.json` is ignored: the receipt family is then built in Rust.
            let (native, a) = match a.iter().position(|x| x == "--native") {
                Some(i) => (
                    Some((
                        a.get(i + 1).cloned().unwrap_or_else(|| die("--native")),
                        a.get(i + 2).cloned().unwrap_or_else(|| die("--native")),
                    )),
                    a[..i]
                        .iter()
                        .chain(a.get(i + 3..).unwrap_or(&[]))
                        .cloned()
                        .collect::<Vec<_>>(),
                ),
                None => (None, a.clone()),
            };
            if a.len() != 5 && a.len() != 6 {
                die(
                    "usage: npudr v3sha <entries-dir> <sha_t.json> <sha_r.json> [<full.json>] [--native <claim.bin> <witness.bin>]",
                );
            }
            let dir = &a[2];
            let mut entries = std::collections::HashMap::new();
            let names = npudr::v3::TABLES
                .iter()
                .map(|(n, _)| *n)
                .chain(npudr::v3::collect::EXTRA_INPUTS.iter().copied());
            for name in names {
                let f = format!("{dir}/{name}.json");
                if let Ok(j) = std::fs::read_to_string(&f) {
                    entries.insert(name.to_string(), j);
                }
            }
            if let Some((c, w)) = &native {
                let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
                let f = npudr::v3::rcptfam::rcpt_family(&rd(c), &rd(w)).unwrap_or_else(|e| die(&e));
                let js = |v: serde_json::Result<String>| v.unwrap_or_else(|e| die(&e.to_string()));
                entries.insert("rcpt".into(), js(serde_json::to_string(&f.rcpt)));
                entries.insert("acct".into(), js(serde_json::to_string(&f.acct)));
                entries.insert("srcp".into(), js(serde_json::to_string(&f.srcp)));
                entries.insert("mrk".into(), js(serde_json::to_string(&f.mrk)));
                entries.remove("sha_receipt");
                eprintln!("v3sha: receipt side (rcpt, acct, srcp, mrk) from the claim + witness");
            }
            use npudr::v3::collect as cl;
            let bundle = cl::bundle_from_entries(&entries).unwrap_or_else(|e| die(&e));
            let c = cl::collect(&bundle);
            for n in &c.notes {
                eprintln!("v3sha: {n}");
            }
            let t = cl::jobs_json(&c.b0).unwrap_or_else(|e| die(&e));
            let r = cl::jobs_json(&c.b1).unwrap_or_else(|e| die(&e));
            std::fs::write(&a[3], t).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            std::fs::write(&a[4], r).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
            let jobs: Vec<cl::Job> = c.b0.iter().chain(c.b1.iter()).cloned().collect();
            let rep = cl::bus_check(&cl::bundle_raws(&bundle), &jobs);
            eprintln!(
                "v3sha: b0 {} jobs, b1 {} jobs (cap {}); bus check: {} sends ({} unmatched), {} receives ({} unmatched); {} expected bytes / {} digests not covered by the supplied tables",
                c.b0.len(),
                c.b1.len(),
                c.cap,
                rep.sends,
                rep.bad_sends.len(),
                rep.recvs,
                rep.bad_recvs.len(),
                rep.unsent,
                rep.unreceived
            );
            if let Some(f) = a.get(5) {
                let mut v: serde_json::Value =
                    serde_json::from_str(&cl::collected_json(&c).unwrap_or_else(|e| die(&e)))
                        .unwrap_or_else(|e| die(&e.to_string()));
                v["bus"] = serde_json::json!({
                    "sends": rep.sends, "bad_sends": rep.bad_sends.len(),
                    "recvs": rep.recvs, "bad_recvs": rep.bad_recvs,
                    "unsent": rep.unsent, "unreceived": rep.unreceived,
                });
                std::fs::write(f, v.to_string()).unwrap_or_else(|e| die(&format!("{f}: {e}")));
            }
            if !rep.ok() {
                die(
                    "v3sha: a supplied table's BYTES send / DIGEST receive is not a job of the bins",
                );
            }
        }
        Some("v3rcpt-prefix") => {
            // first <n> rows of the aligned rcpt trace (`np-lean-render-v3-rcpt` prefix format)
            if a.len() != 5 {
                die("usage: npudr v3rcpt-prefix <rcpt.json> <n> <out.bin>");
            }
            let j =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let n: usize = a[3].parse().unwrap_or_else(|_| die("n"));
            let b = npudr::v3::rcpt::render_prefix(&j, n).unwrap_or_else(|e| die(&e));
            std::fs::write(&a[4], b).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
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
            if a.len() != 5 && a.len() != 6 {
                die("usage: npudr v3check <air.json> <table> <entries.json> [<pubs.json>]");
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
            // rcpt: compact height + its honest public values (`v3::rcpt::check_render`)
            let (tab, rcpt_pubs) = if a[3] == "rcpt" {
                let (t, p) =
                    npudr::v3::rcpt::check_render(&j, air.num_pub).unwrap_or_else(|e| die(&e));
                (t, Some(p))
            } else {
                (
                    npudr::v3::render(&a[3], &j).unwrap_or_else(|e| die(&e)),
                    None,
                )
            };
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
            // optional public prefix (JSON list of field values; the rest is zero)
            let mut pubs = rcpt_pubs.unwrap_or_else(|| vec![npudr::field::F::ZERO; air.num_pub]);
            if let Some(pf) = a.get(5) {
                let pt = std::fs::read_to_string(pf).unwrap_or_else(|e| die(&format!("{pf}: {e}")));
                let pv: Vec<u64> =
                    serde_json::from_str(&pt).unwrap_or_else(|e| die(&format!("{pf}: {e}")));
                for (i, x) in pv.into_iter().enumerate().take(air.num_pub) {
                    pubs[i] = npudr::field::F::from_u64(x);
                }
            }
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
        Some("v3bus") => {
            // `npudr v3bus <air.json> <pub.bin> <bus> <table>=<entries.json>...`: render the
            // given tables and check that their interactions on `<bus>` balance against the
            // public messages of the prepared tape on that bus (`pubMsgs`).  Exit 1 on an
            // imbalance or a tape that does not fit (`pubFit`).
            if a.len() < 6 {
                die(
                    "usage: npudr v3bus <air.json> <pub.bin> <bus>[,<bus>…] <table>=<entries.json>...",
                );
            }
            let txt =
                std::fs::read_to_string(&a[2]).unwrap_or_else(|e| die(&format!("{}: {e}", a[2])));
            let air = Air::from_json(&txt).unwrap_or_else(|e| die(&e));
            let tape = std::fs::read(&a[3]).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            // `<bus>` may be a comma-separated list: the tables are rendered once and every
            // listed bus is checked (exit 1 if any is unbalanced).
            let buses: Vec<usize> = a[4]
                .split(',')
                .map(|x| x.parse().unwrap_or_else(|_| die("bus")))
                .collect();
            let mut mats = vec![];
            for spec in &a[5..] {
                let (name, f) = spec
                    .split_once('=')
                    .unwrap_or_else(|| die("<table>=<entries.json>"));
                let idx = npudr::v3::TABLES
                    .iter()
                    .find(|(n, _)| *n == name)
                    .map(|p| p.1)
                    .unwrap_or_else(|| die("unknown table"));
                let j = std::fs::read_to_string(f).unwrap_or_else(|e| die(&format!("{f}: {e}")));
                let tab = npudr::v3::render(name, &j).unwrap_or_else(|e| die(&e));
                mats.push((idx, tab.to_matrix()));
            }
            let refs: Vec<(usize, &_)> = mats.iter().map(|(i, m)| (*i, m)).collect();
            let pubs = vec![npudr::field::F::ZERO; air.num_pub];
            let mut failed = false;
            for bus in buses {
                match npudr::check::bus_imbalance_with_pub(&air, &refs, &pubs, &tape, bus) {
                    None => die("public tape does not fit (pubFit)"),
                    Some(bad) if bad.is_empty() => println!("ok  bus {bus} balanced"),
                    Some(bad) => {
                        for (b, msg, s, r) in bad.iter().take(20) {
                            println!("IMBALANCE bus {b} sent {s} received {r} msg {msg:?}");
                        }
                        println!("FAIL bus {bus}: {} unbalanced messages", bad.len());
                        failed = true;
                    }
                }
            }
            if failed {
                std::process::exit(1);
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
        Some("v3rcptfam") => {
            // `npudr v3rcptfam <claim.bin> <witness.bin> <out_dir> [--no-prefix]`: the
            // honest entries of the receipt-side tables from a real claim + witness
            // (`v3::rcptfam`, the twin of the accepted renders): `rcpt.json` (16),
            // `acct.json` (17), `akey.json` (18), `bnd.json` (19), `srcp.json` (20),
            // `mrk.json` (23, `MrkV` with its level table), `sort.json` (24), the
            // receipt SHA family `sha_receipt.json` (`collect::receipt_family`), and
            // `rcpt.prefix.bin`, the first `planned + 8` rows of table 16
            // (`rcpt::render_prefix`, the `np-lean-rcptfam-v3` layout).
            let no_prefix = a.iter().any(|x| x == "--no-prefix");
            let a: Vec<String> = a.iter().filter(|x| *x != "--no-prefix").cloned().collect();
            if a.len() != 5 {
                die("usage: npudr v3rcptfam <claim.bin> <witness.bin> <out_dir> [--no-prefix]");
            }
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let (cb, wb) = (rd(&a[2]), rd(&a[3]));
            let f = npudr::v3::rcptfam::rcpt_family(&cb, &wb).unwrap_or_else(|e| die(&e));
            let od = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(od).unwrap_or_else(|e| die(&format!("{}: {e}", a[4])));
            let wr = |name: &str, b: &[u8]| {
                std::fs::write(od.join(name), b).unwrap_or_else(|e| die(&format!("{name}: {e}")))
            };
            let js = |v: serde_json::Result<String>| v.unwrap_or_else(|e| die(&e.to_string()));
            let rcpt_json = js(serde_json::to_string(&f.rcpt));
            wr("rcpt.json", rcpt_json.as_bytes());
            wr("acct.json", js(serde_json::to_string(&f.acct)).as_bytes());
            wr("akey.json", js(serde_json::to_string(&f.akey)).as_bytes());
            wr("bnd.json", js(serde_json::to_string(&f.bnd)).as_bytes());
            wr("srcp.json", js(serde_json::to_string(&f.srcp)).as_bytes());
            wr("mrk.json", js(serde_json::to_string(&f.mrk)).as_bytes());
            wr("sort.json", js(serde_json::to_string(&f.sort)).as_bytes());
            use npudr::v3::collect as cl;
            let dup = |j: usize| f.srcp.iter().any(|b| b.j == j as u64 && b.dup);
            let fam = cl::receipt_family(&f.rcpt, &dup, &f.acct);
            wr(
                "sha_receipt.json",
                cl::jobs_json(&fam).unwrap_or_else(|e| die(&e)).as_bytes(),
            );
            let rows = npudr::v3::rcpt::planned_rows(&f.rcpt);
            if !no_prefix {
                let b = npudr::v3::rcpt::render_prefix(&rcpt_json, rows + 8)
                    .unwrap_or_else(|e| die(&e));
                wr("rcpt.prefix.bin", &b);
            }
            println!(
                "rcptfam: {} receipts in {} lists, {} planned rows; acct {} akey {} bnd {} srcp {} mrk n={} sort {}; receipt family {} jobs",
                f.rcpt.lists.iter().map(|l| l.rs.len()).sum::<usize>(),
                f.rcpt.lists.len(),
                rows,
                f.acct.len(),
                f.akey.len(),
                f.bnd.len(),
                f.srcp.len(),
                f.mrk.n,
                f.sort.len(),
                fam.len()
            );
        }
        Some("v3native") => {
            // `npudr v3native <case_dir>`: the native objects (`v3::native::native_of`) as the
            // `np-lean-trie-v3 <case> native` JSON (native part); `npudr v3native --parse
            // <native.json>` re-emits a Lean dump through the Rust parser (round trip).
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let n = match a.get(2).map(|s| s.as_str()) {
                Some("--parse") if a.len() == 4 => {
                    let v: serde_json::Value =
                        serde_json::from_slice(&rd(&a[3])).unwrap_or_else(|e| die(&e.to_string()));
                    npudr::v3::native::Native::from_json(&v).unwrap_or_else(|e| die(&e))
                }
                Some(d) if a.len() == 3 => npudr::v3::native::native_of(
                    &rd(&format!("{d}/claim.bin")),
                    &rd(&format!("{d}/witness.bin")),
                )
                .unwrap_or_else(|e| die(&e)),
                _ => die("usage: npudr v3native <case_dir> | --parse <native.json>"),
            };
            println!("{}", n.to_json());
        }
        Some("v3forest") => {
            // `npudr v3forest <native.json>`: node/val/head/uniq entries (`v3::forest`) from a
            // `np-lean-trie-v3 native` dump and its use requests `q` (head keys `q.edges`).
            if a.len() != 3 {
                die("usage: npudr v3forest <native.json>");
            }
            let s = std::fs::read(&a[2]).unwrap_or_else(|e| die(&e.to_string()));
            let v: serde_json::Value =
                serde_json::from_slice(&s).unwrap_or_else(|e| die(&e.to_string()));
            let n = npudr::v3::native::Native::from_json(&v).unwrap_or_else(|e| die(&e));
            let q: npudr::v3::forest::UseRequests =
                serde_json::from_value(v["q"].clone()).unwrap_or_else(|e| die(&e.to_string()));
            use npudr::v3::forest;
            let out = serde_json::json!({
                "node": forest::nodes(&n, &q).unwrap_or_else(|e| die(&e)),
                "val": forest::vals(&n).unwrap_or_else(|e| die(&e)),
                "head": forest::heads(&n, &q.edges).unwrap_or_else(|e| die(&e)),
                "uniq": forest::uniq(&n).unwrap_or_else(|e| die(&e)),
            });
            println!("{out}");
        }
        Some("v3walks") => {
            // `npudr v3walks <case_dir> <native.json>`: main values, lookup queries, walks,
            // honest ups instances (unranked/ranked), the use requests and the ranked walks
            // (`v3::walks`, `v3::upsnat`), from a `np-lean-trie-v3 native` dump (receipts from
            // the case's claim/witness).
            if a.len() != 4 {
                die("usage: npudr v3walks <case_dir> <native.json>");
            }
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let v: serde_json::Value =
                serde_json::from_slice(&rd(&a[3])).unwrap_or_else(|e| die(&e.to_string()));
            let mut n = npudr::v3::native::Native::from_json(&v).unwrap_or_else(|e| die(&e));
            let cb = rd(&format!("{}/claim.bin", a[2]));
            let wb = rd(&format!("{}/witness.bin", a[2]));
            let k = npudr::v3::d0::walk_d0(&cb).unwrap_or_else(|e| die(&e));
            let w = npudr::v3::hint::decode_w(&wb).unwrap_or_else(|e| die(&e));
            n.receipts = npudr::v3::hint::applied_receipts(&k, &w);
            use npudr::v3::{upsnat, walks};
            let iso = std::env::var_os("NPUDR_WS_FROM_DUMP").is_some();
            let mv = if iso {
                npudr::v3::native::MainValues::from_json(&v["mainValues"])
                    .unwrap_or_else(|e| die(&e))
            } else {
                walks::main_values(&n).unwrap_or_else(|e| die(&e))
            };
            let qs = if iso {
                vec![]
            } else {
                walks::queries(&n, &mv).unwrap_or_else(|e| die(&e))
            };
            // `NPUDR_WS_FROM_DUMP=1`: take the unranked walks from the dump's `ws` (stage
            // isolation for the ups differential)
            let ws: Vec<npudr::v3::WalkR> = if std::env::var_os("NPUDR_WS_FROM_DUMP").is_some() {
                serde_json::from_value(v["ws"].clone()).unwrap_or_else(|e| die(&e.to_string()))
            } else {
                walks::query_walks(&n, &qs).unwrap_or_else(|e| die(&e))
            };
            let insts = upsnat::honest_insts(&n.us).unwrap_or_else(|e| die(&e));
            let js = upsnat::ups_ranked(&ws, &insts);
            let wk = upsnat::window_keys(&js);
            let q = upsnat::use_req(&ws, &insts, wk);
            let out = serde_json::json!({
                "mainValues": mv.to_json(),
                "queries": qs.iter().map(|x| serde_json::json!({"wid": x.wid, "tau": x.tau, "key": x.key})).collect::<Vec<_>>(),
                "ws": ws, "insts": insts, "ups": js, "q": q,
                "walk": if iso { serde_json::Value::Null } else { serde_json::json!(walks::rank_walks(&ws)) },
            });
            println!("{out}");
        }
        Some("v3trie") => {
            // `npudr v3trie <case_dir> [<table>]`: the honest trie-side entries (`v3::trie`), the
            // Rust twin of `np-lean-trie-v3`.
            if a.len() != 3 && a.len() != 4 {
                die("usage: npudr v3trie <case_dir> [<table>]");
            }
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let cb = rd(&format!("{}/claim.bin", a[2]));
            let wb = rd(&format!("{}/witness.bin", a[2]));
            let v = npudr::v3::trie::entries(&cb, &wb).unwrap_or_else(|e| die(&e));
            match a.get(3) {
                Some(t) => match v.get(t.as_str()) {
                    Some(x) => println!("{x}"),
                    None => die(&format!("no table {t}")),
                },
                None => println!("{v}"),
            }
        }
        Some("v3sched") => {
            // `npudr v3sched <case_dir> <out_dir>`: the honest entries of tables 8–15 and 22
            // (`v3::schedqv`, the Rust twin of `np-lean-sched-v3`): `codec/scandist/proc/mem/
            // cmp.json` (the scheduler block list), `chacha/rng/shuf.json` (the runs' lane
            // entries, `chacha::lane`), `qv.json` (`qv::QvIn`).
            if a.len() == 4 && a[2] == "--rerun" {
                // `npudr v3sched --rerun <sched.json>`: re-derive every block's run and
                // grants from its inputs (`schedqv::rerun`) and print the block list.
                let j = std::fs::read_to_string(&a[3]).unwrap_or_else(|e| die(&e.to_string()));
                let bs = npudr::v3::sched::parse_all(&j).unwrap_or_else(|e| die(&e));
                let out: Vec<_> = bs
                    .iter()
                    .map(|b| npudr::v3::schedqv::rerun(b).unwrap_or_else(|e| die(&e)))
                    .collect();
                println!(
                    "{}",
                    serde_json::to_string(&out).unwrap_or_else(|e| die(&e.to_string()))
                );
                return;
            }
            if a.len() != 4 {
                die("usage: npudr v3sched <case_dir> <out_dir> | --rerun <sched.json>");
            }
            let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let cb = rd(&format!("{}/claim.bin", a[2]));
            let wb = rd(&format!("{}/witness.bin", a[2]));
            let e = npudr::v3::schedqv::derive(&cb, &wb).unwrap_or_else(|e| die(&e));
            let od = std::path::Path::new(&a[3]);
            std::fs::create_dir_all(od).unwrap_or_else(|e| die(&format!("{}: {e}", a[3])));
            let wr = |name: &str, s: String| {
                std::fs::write(od.join(name), s).unwrap_or_else(|e| die(&format!("{name}: {e}")))
            };
            let js = |v: serde_json::Result<String>| v.unwrap_or_else(|e| die(&e.to_string()));
            let blocks = js(serde_json::to_string(&e.blocks));
            for t in ["codec", "scandist", "proc", "mem", "cmp"] {
                wr(&format!("{t}.json"), blocks.clone());
            }
            let rs: Vec<&npudr::v3::sched::Run> = e.blocks.iter().map(|b| &b.run).collect();
            let (reqs, calls, insts) = npudr::v3::chacha::lane(&rs);
            wr("chacha.json", js(serde_json::to_string(&reqs)));
            wr("rng.json", js(serde_json::to_string(&calls)));
            wr("shuf.json", js(serde_json::to_string(&insts)));
            wr("qv.json", js(serde_json::to_string(&e.qv)));
            println!(
                "{} blocks, {} requests, qv {} walks / {} records",
                e.blocks.len(),
                rs.iter().map(|r| r.conv.len()).sum::<usize>(),
                e.qv.walks.len(),
                e.qv.records.len()
            );
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
