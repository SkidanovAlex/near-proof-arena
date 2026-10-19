//! `cargo run --release --example d1dump -- <nearAirV3D1.json> <case_dir> <out_dir> <table>...`
//!
//! Lane pq-d1-envelope (research only, not shipped): render the honest `nearAirV3D1` traces of
//! the named tables for a real D1a case (the same generators as `npudr v3d1prove`), check every
//! constraint of each with the classical checker, and write them for the PQ (SWIRL) port:
//! * `<table>.bin`: u32 LE `log_h`, `width`, then the row-major canonical cells (u32 LE);
//! * `pubs.bin`: the public vector (`verifier::public_inputs`, u32 LE per element);
//! * `pubmsgs.json`: the public-segment bus messages `[[bus, send, [felts]], ...]`.
//! Table names are `v3::d1::ORDER_D1` (`node`, `head`, `val`, ...).
use npudr::air::Air;
use npudr::v3::d1;
use npudr::v3::prove as vp;
use std::io::Write;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 5 {
        eprintln!("usage: d1dump <nearAirV3D1.json> <case_dir> <out_dir> <table>...");
        std::process::exit(2);
    }
    let air = Air::from_json(&std::fs::read_to_string(&a[1]).unwrap()).unwrap();
    assert_eq!(air.tables.len(), 30, "not nearAirV3D1");
    let cb = std::fs::read(format!("{}/claim.bin", a[2])).unwrap();
    let wb = std::fs::read(format!("{}/witness.bin", a[2])).unwrap();
    let od = std::path::PathBuf::from(&a[3]);
    std::fs::create_dir_all(&od).unwrap();
    let ci = d1::case_inputs_d1(&cb, &wb).unwrap();
    let pubs = npudr::verifier::public_inputs(&air, &ci.tape);
    let new_tabs = d1::d1_tables(&ci).unwrap();
    for name in &a[4..] {
        let t = d1::ORDER_D1
            .iter()
            .position(|n| n == name)
            .unwrap_or_else(|| panic!("no table {name}"));
        let tc = if t < 25 {
            vp::render_cols(name, &ci.entries[name.as_str()]).unwrap()
        } else {
            let tb = &new_tabs[t - 25];
            let w = tb.width;
            npudr::cols::TraceCols::from_rows(tb.log, w, |r, buf| {
                buf.copy_from_slice(&tb.cells[r * w..(r + 1) * w])
            })
        };
        let bad = npudr::check::failing_constraints_cols(&air.tables[t], &tc, &pubs, 10);
        assert!(
            bad.is_empty(),
            "{name}: classical constraint failure {bad:?}"
        );
        let (h, w) = (tc.height(), tc.width());
        let mut out = Vec::with_capacity(8 + 4 * h * w);
        out.extend_from_slice(&(tc.log_h as u32).to_le_bytes());
        out.extend_from_slice(&(w as u32).to_le_bytes());
        let mut row = vec![npudr::field::F::new(0); w];
        for r in 0..h {
            tc.row_into(r, &mut row);
            for x in &row {
                use p3_field::PrimeField32;
                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
            }
        }
        std::fs::write(od.join(format!("{name}.bin")), out).unwrap();
        eprintln!(
            "d1dump: table {t:2} {name:9} log {:2} width {w:3}: classical constraints ok",
            tc.log_h
        );
    }
    let mut pb = Vec::with_capacity(4 * pubs.len());
    for x in &pubs {
        use p3_field::PrimeField32;
        pb.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
    std::fs::write(od.join("pubs.bin"), pb).unwrap();
    let msgs = npudr::verifier::pub_msgs(&air, &ci.tape);
    let mut f = std::fs::File::create(od.join("pubmsgs.json")).unwrap();
    let js: Vec<serde_json::Value> = msgs
        .iter()
        .map(|(b, s, m)| {
            use p3_field::PrimeField32;
            serde_json::json!([
                b,
                s,
                m.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>()
            ])
        })
        .collect();
    f.write_all(serde_json::to_string(&js).unwrap().as_bytes())
        .unwrap();
    eprintln!(
        "d1dump: tape {} B, {} public messages, {} public inputs",
        ci.tape.len(),
        msgs.len(),
        pubs.len()
    );
}
