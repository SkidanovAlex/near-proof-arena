//! `cargo run --release --example statedump -- <d0a|d1> <air.json> <case_dir> <out_dir> [<table>...]`
//!
//! Lane pq-state-port (research only, not shipped; a cargo *example*, so the package is unchanged):
//! render the honest traces of the classical `nearAirV3` (D0a, 25 tables, the same generators as
//! `npudr v3prove`) or `nearAirV3D1` (30 tables, as `npudr v3d1prove`) for a real case, re-check
//! every classical constraint with the classical checker, and write them for the PQ (SWIRL) port.
//!
//! **Height normalisation** (`pad_pattern`, `recut`).  The classical renders use fixed heights
//! (`2^22` for the scheduler and receipt tables, `padLog22` rounding elsewhere), an artefact of the
//! classical FRI roll-in; `HoldsP` accepts any `1 ≤ log ≤ maxLog`.  Every render is "rows, then
//! padding rows", where the padding is a constant row or (`shuf`) a row counter, i.e. an arithmetic
//! progression `row(r) = row(u) + (r − u)·δ`.  With `u` = the first row from which the rows follow
//! that progression up to the last row, the table is re-cut at `log' = max(2, ⌈log₂(u + 1)⌉)` rows
//! (rows `< u` unchanged, then the progression).  This is a *generator* choice only: the re-cut
//! table is re-checked here against every classical constraint, and the PQ driver re-checks every
//! constraint and the balance of every bus (including the public messages), so the result is an
//! honest `HoldsP` trace by check, not by assumption.  The floor of 4 rows is NV's minimum height.
//! `--no-compact` keeps the classical heights.
//!
//! Output (`out_dir`): `<table>.bin` (u32 LE `log_h`, `width`, then the row-major canonical
//! cells), `pubs.bin` (the public vector, u32 LE), `pubmsgs.json` (`[[bus, send, [felts]], …]`),
//! `prepared.bin` (the prepared public tape `cb'`), `claim.bin`, `hint.bin`, `heights.json`
//! (classical log, used rows, normalised log per table).
use npudr::air::Air;
use npudr::cols::TraceCols;
use npudr::field::F;
use npudr::v3::d1;
use npudr::v3::prove as vp;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use std::io::Write;

/// The padding pattern of a render: `delta` = last row − second-to-last row (zero for a constant
/// padding row; the row counter of `shuf`'s padding), and `u` = the first row from which every row
/// `r` equals `last + (r − (h−1))·delta` (an arithmetic progression up to the last row).
fn pad_pattern(tc: &TraceCols) -> (usize, Vec<F>) {
    let (h, w) = (tc.height(), tc.width());
    let mut last = vec![F::new(0); w];
    tc.row_into(h - 1, &mut last);
    let mut delta = vec![F::new(0); w];
    if h >= 2 {
        let mut prev = vec![F::new(0); w];
        tc.row_into(h - 2, &mut prev);
        for c in 0..w {
            delta[c] = last[c] - prev[c];
        }
    }
    let mut row = vec![F::new(0); w];
    let mut want = last.clone();
    let mut u = h;
    while u > 0 {
        tc.row_into(u - 1, &mut row);
        if row != want {
            break;
        }
        for c in 0..w {
            want[c] -= delta[c];
        }
        u -= 1;
    }
    (u, delta)
}

fn clog2(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}

/// Re-cut `tc` at `log2` rows: rows `< u` from `tc`, then the padding progression
/// `row(u) + (r − u)·delta` (rows `≥ u` of `tc` where they exist).
fn recut(tc: &TraceCols, u: usize, delta: &[F], log2: usize) -> TraceCols {
    let w = tc.width();
    let h = tc.height();
    let mut base = vec![F::new(0); w];
    tc.row_into(u.min(h - 1), &mut base);
    let base_at = u.min(h - 1);
    TraceCols::from_rows(log2, w, |r, buf| {
        if r < u {
            for (c, x) in buf.iter_mut().enumerate() {
                *x = tc.get(r, c).as_canonical_u32();
            }
        } else {
            let k = F::from_u64((r - base_at) as u64);
            for (c, x) in buf.iter_mut().enumerate() {
                *x = (base[c] + delta[c] * k).as_canonical_u32();
            }
        }
    })
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 5 {
        eprintln!("usage: statedump <d0a|d1> <air.json> <case_dir> <out_dir> [--no-compact] [<table>...]");
        std::process::exit(2);
    }
    let mode = a[1].as_str();
    let air = Air::from_json(&std::fs::read_to_string(&a[2]).unwrap()).unwrap();
    let cb = std::fs::read(format!("{}/claim.bin", a[3])).unwrap();
    let wb = std::fs::read(format!("{}/witness.bin", a[3])).unwrap();
    let od = std::path::PathBuf::from(&a[4]);
    std::fs::create_dir_all(&od).unwrap();
    let compact = !a[5..].iter().any(|x| x == "--no-compact");
    let wanted: Vec<&str> = a[5..].iter().filter(|x| !x.starts_with("--")).map(|s| s.as_str()).collect();
    let (order, tape, hint, entries, new_tabs): (&[&str], Vec<u8>, Vec<u8>, _, Vec<npudr::v3::Tab>) = match mode {
        "d0a" => {
            assert_eq!(air.tables.len(), 25, "not nearAirV3");
            let ci = vp::case_inputs(&cb, &wb, None).unwrap();
            (vp::ORDER, ci.tape, ci.hint.encode(), ci.entries, vec![])
        }
        "d1" => {
            assert_eq!(air.tables.len(), 30, "not nearAirV3D1");
            let ci = d1::case_inputs_d1(&cb, &wb).unwrap();
            let nt = d1::d1_tables(&ci).unwrap();
            (d1::ORDER_D1, ci.tape, ci.hint, ci.entries, nt)
        }
        m => panic!("mode {m}"),
    };
    let pubs = npudr::verifier::public_inputs(&air, &tape);
    let names: Vec<&str> = if wanted.is_empty() { order.to_vec() } else { wanted };
    let mut heights = serde_json::Map::new();
    for name in names {
        let t = order.iter().position(|n| *n == name).unwrap_or_else(|| panic!("no table {name}"));
        let tc0 = if t < 25 {
            vp::render_cols(name, &entries[name]).unwrap()
        } else {
            let tb = &new_tabs[t - 25];
            let w = tb.width;
            TraceCols::from_rows(tb.log, w, |r, buf| buf.copy_from_slice(&tb.cells[r * w..(r + 1) * w]))
        };
        let bad = npudr::check::failing_constraints_cols(&air.tables[t], &tc0, &pubs, 10);
        assert!(bad.is_empty(), "{name}: classical constraint failure {bad:?}");
        let (u, delta) = pad_pattern(&tc0);
        let log0 = tc0.log_h;
        let log2 = clog2(u + 1).max(2);
        let tc = if compact && log2 != tc0.log_h {
            let tc1 = recut(&tc0, u, &delta, log2);
            let bad = npudr::check::failing_constraints_cols(&air.tables[t], &tc1, &pubs, 10);
            assert!(bad.is_empty(), "{name}: re-cut at log {log2} fails classical constraints {bad:?}");
            tc1
        } else {
            tc0
        };
        assert!(tc.log_h <= air.tables[t].max_log, "{name}: log {} > maxLog", tc.log_h);
        heights.insert(
            name.to_string(),
            serde_json::json!({"classical_log": log0, "used_rows": u, "log": tc.log_h, "max_log": air.tables[t].max_log}),
        );
        let (h, w) = (tc.height(), tc.width());
        let mut out = Vec::with_capacity(8 + 4 * h * w);
        out.extend_from_slice(&(tc.log_h as u32).to_le_bytes());
        out.extend_from_slice(&(w as u32).to_le_bytes());
        let mut row = vec![F::new(0); w];
        for r in 0..h {
            tc.row_into(r, &mut row);
            for x in &row {
                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
            }
        }
        std::fs::write(od.join(format!("{name}.bin")), out).unwrap();
        eprintln!(
            "statedump: table {t:2} {name:9} classical log {:2} used rows {u:8} -> log {:2} width {w:3}: classical constraints ok",
            log0, tc.log_h
        );
    }
    let mut pb = Vec::with_capacity(4 * pubs.len());
    for x in &pubs {
        pb.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
    std::fs::write(od.join("pubs.bin"), pb).unwrap();
    std::fs::write(od.join("prepared.bin"), &tape).unwrap();
    std::fs::write(od.join("claim.bin"), &cb).unwrap();
    std::fs::write(od.join("hint.bin"), &hint).unwrap();
    std::fs::write(od.join("heights.json"), serde_json::Value::Object(heights).to_string()).unwrap();
    let msgs = npudr::verifier::pub_msgs(&air, &tape);
    let mut f = std::fs::File::create(od.join("pubmsgs.json")).unwrap();
    let js: Vec<serde_json::Value> = msgs
        .iter()
        .map(|(b, s, m)| serde_json::json!([b, s, m.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>()]))
        .collect();
    f.write_all(serde_json::to_string(&js).unwrap().as_bytes()).unwrap();
    eprintln!(
        "statedump: {mode} tape {} B, hint {} B, {} public messages, {} public inputs",
        tape.len(),
        hint.len(),
        msgs.len(),
        pubs.len()
    );
}
