//! lane/pq-d1-envelope demo: real `nearAirV3D1` tables (the Lean AIR value, exported as
//! `np-air-v2`), with honest traces of a real D1a fixture rendered by the classical Rust
//! generators (`examples/np-udr-stark-v2/source/examples/d1dump.rs`), proven **unchanged** on the
//! unified SWIRL backend (BabyBear, Ext12, SHA-384, T*, 42-byte digests, stacked WHIR) and
//! verified natively.
//!
//! Usage:
//!   nearproof-pq-d1-envelope <nearAirV3D1.json> <dump_dir> check|prove|tamper [small|pinned]
//!
//! The tables proven are those with a `<name>.bin` in `dump_dir`.  The classical public segments
//! become the cached `TAPE` table (V_d recomputes its commitment from the public messages); the
//! net bus traffic of the classical tables *not* in `dump_dir` becomes `EXT`, a synthetic stand-in
//! (reported, and checked to sit only on buses that an excluded table uses).
#[allow(dead_code, clippy::all)]
mod config;
mod air;

use air::{ClassicalAir, E, JsonAir, TableSpec};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    codec::Encode,
    interaction::LogUpSecurityParameters,
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend, DeviceDataTransporter, ProvingContext, TraceCommitter},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Instant;

/// `v3::d1::ORDER_D1` (the 30 tables of `nearAirV3D1`, by position).
const ORDER_D1: &[&str] = &[
    "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf", "codec", "scandist",
    "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv", "mrk", "sort", "tx", "akm", "kib",
    "plf", "rid",
];
const P: u64 = 0x7800_0001;

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

/// seg-v1 shape (DESIGN-BASE §3) with the message-length parameter raised to 2^6 (classical
/// messages reach 35 fields + the bus) and the interaction budget at 2^28.
fn seg_v1_params(n_stack: usize, w_stack: usize, max_degree: usize) -> SystemParams {
    let (l_skip, log_blowup, k, k1, lf) = (2, 1, 4, 1, 7);
    let log_h = l_skip + n_stack;
    assert_eq!((log_h - k1 - lf) % k, 0, "n_stack must be 10, 14, 18 or 22");
    let levers = WhirLevers { k_first: k1, multiproof: true, keep_domain: true, whir_y: true, ..Default::default() };
    let whir = WhirConfig::new_full(
        log_blowup,
        log_h,
        WhirParams {
            k,
            log_final_poly_len: lf,
            query_phase_pow_bits: std::env::var("PQD1_POW").ok().and_then(|v| v.parse().ok()).unwrap_or(24),
            proximity: WhirProximityStrategy::ListDecoding { m: 16 },
            folding_pow_bits: 0,
            mu_pow_bits: 0,
        },
        268,
        levers,
        1,
    );
    SystemParams {
        l_skip,
        n_stack,
        w_stack,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 28, log_max_message_length: 6, pow_bits: 0 },
        max_constraint_degree: max_degree,
    }
}

fn deg(e: &E) -> usize {
    match e {
        E::C(_) | E::P(_) => 0,
        E::Col(..) | E::First | E::Last | E::Trans => 1,
        E::Add(a, b) => deg(a).max(deg(b)),
        E::Mul(a, b) => deg(a) + deg(b),
        E::Neg(a) => deg(a),
    }
}

fn read_trace(path: &std::path::Path) -> RowMajorMatrix<F> {
    let b = std::fs::read(path).unwrap();
    let u = |i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
    let (log, w) = (u(0) as usize, u(1) as usize);
    let n = (1usize << log) * w;
    assert_eq!(b.len(), 8 + 4 * n, "{path:?}: size");
    RowMajorMatrix::new((0..n).map(|i| F::new(u(2 + i))).collect(), w)
}

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    /// (bus, msg) -> net count of the public messages (send +1, receive −1)
    tape: BTreeMap<(u16, Vec<u32>), u64>,
    excluded: Vec<String>,
    ext_buses: BTreeSet<u16>,
}

type Key = (u16, Vec<u32>);

fn add(map: &mut BTreeMap<Key, u64>, k: Key, c: u64) {
    let e = map.entry(k).or_insert(0);
    *e = (*e + c) % P;
}

/// Net bus traffic of `t` (count `+c` for sends, `−c` for receives), modulo p.
fn traffic(t: &TableSpec, m: &RowMajorMatrix<F>, pubs: &[F], map: &mut BTreeMap<Key, u64>) {
    let w = m.width;
    let h = m.values.len() / w;
    for r in 0..h {
        let cur = &m.values[r * w..(r + 1) * w];
        let nr = (r + 1) % h;
        let nxt = &m.values[nr * w..(nr + 1) * w];
        let sel = [
            if r == 0 { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ZERO } else { F::ONE },
        ];
        for i in &t.inters {
            let mut c = F::ZERO;
            for (k, b) in i.mult.iter().enumerate() {
                c += b.eval_f(cur, nxt, pubs, sel) * F::from_u64(1 << k);
            }
            if c == F::ZERO {
                continue;
            }
            let msg: Vec<u32> = i.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, sel).as_canonical_u32()).collect();
            let c = c.as_canonical_u32() as u64;
            add(map, (i.bus, msg), if i.send { c } else { (P - c) % P });
        }
    }
}

fn check_constraints(t: &TableSpec, m: &RowMajorMatrix<F>, pubs: &[F]) -> Result<(), String> {
    let w = m.width;
    let h = m.values.len() / w;
    for r in 0..h {
        let cur = &m.values[r * w..(r + 1) * w];
        let nr = (r + 1) % h;
        let nxt = &m.values[nr * w..(nr + 1) * w];
        let sel = [
            if r == 0 { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ZERO } else { F::ONE },
        ];
        for (ci, c) in t.constraints.iter().enumerate() {
            if c.eval_f(cur, nxt, pubs, sel) != F::ZERO {
                return Err(format!("{}: constraint {ci} fails on row {r}", t.name));
            }
        }
    }
    Ok(())
}

/// A harness table: one row per (key, net count); columns msg[0..W), cnt, sel[k].
fn harness(name: &str, map: &BTreeMap<Key, u64>, cached: bool) -> (TableSpec, RowMajorMatrix<F>) {
    let keys: Vec<(u16, usize)> = map.keys().map(|(b, m)| (*b, m.len())).collect::<BTreeSet<_>>().into_iter().collect();
    let wmsg = keys.iter().map(|k| k.1).max().unwrap_or(1).max(1);
    let width = wmsg + 1 + keys.len().max(1);
    let rows = map.iter().filter(|(_, c)| **c != 0).count();
    let h = rows.next_power_of_two().max(4);
    let mut v = vec![F::ZERO; h * width];
    for (r, ((b, m), c)) in map.iter().filter(|(_, c)| **c != 0).enumerate() {
        let row = &mut v[r * width..(r + 1) * width];
        for (j, x) in m.iter().enumerate() {
            row[j] = F::new(*x);
        }
        row[wmsg] = F::new(*c as u32);
        let k = keys.iter().position(|k| *k == (*b, m.len())).unwrap();
        row[wmsg + 1 + k] = F::ONE;
    }
    let spec = TableSpec {
        name: name.into(),
        width,
        max_log: 22,
        constraints: vec![],
        inters: vec![],
        harness: Some((wmsg, keys)),
        cached,
        num_pub: 0,
    };
    (spec, RowMajorMatrix::new(v, width))
}

fn load(air_path: &str, dir: &str) -> Inst {
    let cl = ClassicalAir::parse(&std::fs::read_to_string(air_path).unwrap(), ORDER_D1);
    assert_eq!(cl.tables.len(), 30, "not nearAirV3D1");
    let d = std::path::Path::new(dir);
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect();
    let (mut spec, mut mats, mut excluded) = (vec![], vec![], vec![]);
    let mut net: BTreeMap<Key, u64> = BTreeMap::new();
    let mut ext_buses = BTreeSet::new();
    for t in cl.tables.iter() {
        let f = d.join(format!("{}.bin", t.name));
        if f.exists() {
            let m = read_trace(&f);
            assert_eq!(m.width, t.width, "{}: width", t.name);
            traffic(t, &m, &pubs, &mut net);
            spec.push(t.clone());
            mats.push(m);
        } else {
            excluded.push(t.name.clone());
            ext_buses.extend(t.inters.iter().map(|i| i.bus));
        }
    }
    // public segments (classical `pubMsgs`): the verifier's own bus messages
    let pm: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(d.join("pubmsgs.json")).unwrap()).unwrap();
    let mut tape = BTreeMap::new();
    for x in pm.as_array().unwrap() {
        let bus = x[0].as_u64().unwrap() as u16;
        let send = x[1].as_bool().unwrap();
        let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
        add(&mut tape, (bus, msg.clone()), if send { 1 } else { P - 1 });
        add(&mut net, (bus, msg), if send { 1 } else { P - 1 });
    }
    // EXT = the negation of the residual; it must lie only on buses an excluded table uses
    let mut ext = BTreeMap::new();
    for (k, c) in &net {
        if *c != 0 {
            assert!(ext_buses.contains(&k.0), "imbalance on bus {} not explained by an excluded table: {k:?} net {c}", k.0);
            ext.insert(k.clone(), (P - c) % P);
        }
    }
    let (ts, tm) = harness("TAPE", &tape, true);
    spec.push(ts);
    mats.push(tm);
    if !ext.is_empty() {
        let (es, em) = harness("EXT", &ext, false);
        spec.push(es);
        mats.push(em);
    }
    Inst { spec, mats, pubs, tape, excluded, ext_buses }
}

fn report(inst: &Inst) {
    let mut cells = 0;
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        cells += h * m.width;
        let d = t.constraints.iter().map(deg).max().unwrap_or(0);
        println!(
            "TABLE {:<8} width {:>3} height 2^{:<2} cells {:>9} constraints {:>4} interactions {:>3} deg {} pubs {}{}",
            t.name,
            m.width,
            h.trailing_zeros(),
            h * m.width,
            t.constraints.len(),
            t.harness.as_ref().map(|h| h.1.len()).unwrap_or(t.inters.len()),
            d,
            t.num_pub,
            if t.cached { " (cached)" } else { "" }
        );
    }
    println!(
        "CELLS {cells}; excluded classical tables {:?} (their traffic = EXT on buses {:?}); tape keys {}",
        inst.excluded,
        inst.ext_buses,
        inst.tape.len()
    );
}

fn pv_of(t: &TableSpec, pubs: &[F]) -> Vec<F> {
    (0..t.num_pub).map(|i| pubs.get(i).copied().unwrap_or(F::ZERO)).collect()
}

fn ctx(eng: &Sha384RefEngine, inst: &Inst, mats: &[RowMajorMatrix<F>], pubs: &[F]) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    ProvingContext::new(
        mats.iter()
            .enumerate()
            .map(|(i, m)| {
                let t = &inst.spec[i];
                let pv = pv_of(t, pubs);
                if !t.cached {
                    (i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv))
                } else {
                    let cm = ColMajorMatrix::from_row_major(m);
                    let (commitment, data) = eng.device().commit(&[&cm]).expect("commit cached");
                    let cached = CommittedTraceData { commitment, trace: cm, data: Arc::new(data) };
                    let h = m.values.len() / m.width;
                    let empty = ColMajorMatrix::from_row_major(&RowMajorMatrix::new(vec![F::ZERO; h], 1));
                    (i, AirProvingContext { cached_mains: vec![cached], common_main: empty, public_values: pv })
                }
            })
            .collect(),
    )
}

/// V_d's statement check: the proof's cached TAPE commitment equals the one recomputed from the
/// public messages (a function of the claim via `prepD1`), and the header public values are the
/// claim's.
fn check_statement(eng: &Sha384RefEngine, inst: &Inst, proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> bool {
    let ti = inst.spec.iter().position(|t| t.name == "TAPE").unwrap();
    let (_, tm) = harness("TAPE", &inst.tape, true);
    let want = eng.device().commit(&[&ColMajorMatrix::from_row_major(&tm)]).expect("tape root").0;
    let tape_ok = matches!(&proof.trace_vdata[ti], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == want);
    let pv_ok = inst.spec.iter().enumerate().all(|(i, t)| proof.public_values[i] == pv_of(t, &inst.pubs));
    tape_ok && pv_ok
}

fn airs(inst: &Inst) -> Vec<AirRef<Sha384Config>> {
    inst.spec.iter().map(|t| Arc::new(JsonAir { spec: t.clone() }) as AirRef<Sha384Config>).collect()
}

fn params_for(inst: &Inst, which: &str) -> SystemParams {
    let total: usize = inst.mats.iter().map(|m| m.values.len()).sum();
    let maxh = inst.mats.iter().map(|m| m.values.len() / m.width.max(1)).max().unwrap();
    let n_stack = match which {
        "pinned" => 22,
        _ => [14, 18, 22].into_iter().find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24).unwrap_or(22),
    };
    let w_stack = total.div_ceil(1 << (n_stack + 2)) + 4;
    let degree = inst.spec.iter().flat_map(|t| t.constraints.iter().map(deg)).max().unwrap_or(2).max(2);
    seg_v1_params(n_stack, w_stack.max(8), degree)
}

fn census(proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> String {
    fn size<T: Encode>(x: &T) -> usize {
        let mut b = Vec::new();
        x.encode(&mut b).unwrap();
        b.len()
    }
    let lv = proof.whir_proof.levers;
    let (mut gk, mut rl) = (Vec::new(), Vec::new());
    proof.gkr_proof.encode_levers(&lv, &mut gk).unwrap();
    proof.batch_constraint_proof.encode_levers(&mut rl).unwrap();
    format!(
        "total={} gkr={} relations={} stacking={} whir={}",
        size(proof),
        gk.len(),
        rl.len(),
        size(&proof.stacking_proof),
        size(&proof.whir_proof)
    )
}

fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap()))
        .unwrap_or(0)
}

fn precheck(inst: &Inst) {
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            check_constraints(t, m, &inst.pubs).expect("constraints");
        }
    }
    // every bus balances mod p over the PQ table set (classical tables + TAPE + EXT)
    let mut net = BTreeMap::new();
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if let Some((w, keys)) = &t.harness {
            let wd = m.width;
            for row in m.values.chunks(wd) {
                for (k, (bus, len)) in keys.iter().enumerate() {
                    let c = row[*w] * row[*w + 1 + k];
                    if c != F::ZERO {
                        add(&mut net, (*bus, row[..*len].iter().map(|x| x.as_canonical_u32()).collect()), c.as_canonical_u32() as u64);
                    }
                }
            }
        } else {
            traffic(t, m, &inst.pubs, &mut net);
        }
    }
    let bad = net.values().filter(|c| **c != 0).count();
    assert_eq!(bad, 0, "{bad} unbalanced messages");
    println!("PRECHECK OK: every constraint on every row; every bus balances ({} distinct messages)", net.len());
}

fn cmd(air_path: &str, dir: &str, mode: &str, which: &str) {
    set_levers();
    let t0 = Instant::now();
    let inst = load(air_path, dir);
    report(&inst);
    precheck(&inst);
    println!("TIME load+precheck {:.2}s", t0.elapsed().as_secs_f64());
    if mode == "check" {
        return;
    }
    let params = params_for(&inst, which);
    println!(
        "PARAMS n_stack {} log_h {} w_stack {} degree {} queries {:?} pow {} log_max_msg {}",
        params.n_stack,
        params.l_skip + params.n_stack,
        params.w_stack,
        params.max_constraint_degree,
        params.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        params.whir.query_phase_pow_bits,
        params.logup.log_max_message_length
    );
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&inst);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    println!("TIME keygen {:.2}s", t1.elapsed().as_secs_f64());
    let mut dag_total = 0;
    for (i, a) in vk.inner.per_air.iter().enumerate() {
        dag_total += a.symbolic_constraints.constraints.nodes.len();
        println!(
            "VK {:<8} degree {} constraints {} interactions {} dag_nodes {}",
            inst.spec[i].name,
            a.max_constraint_degree,
            a.symbolic_constraints.constraints.constraint_idx.len(),
            a.symbolic_constraints.interactions.len(),
            a.symbolic_constraints.constraints.nodes.len()
        );
    }
    println!("VK dag_nodes total {dag_total}");
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!(
        "SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits
    );
    if std::env::var("PQD1_DEBUG").is_ok() {
        eng.debug(&airs, &ctx(&eng, &inst, &inst.mats, &inst.pubs));
        println!("DEBUG OK");
    }
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let t2 = Instant::now();
    let proof = eng.prove(&d_pk, ctx(&eng, &inst, &inst.mats, &inst.pubs)).expect("prove");
    let t_prove = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    eng.verify(&vk, &proof).expect("verify");
    let t_verify = t3.elapsed().as_secs_f64();
    let st = check_statement(&eng, &inst, &proof);
    println!("PROOF {}", census(&proof));
    println!("VERIFY OK (native SWIRL verifier); V_d statement check (TAPE root + header PVs): {}", if st { "OK" } else { "FAIL" });
    assert!(st);
    println!(
        "TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        peak_rss_kib()
    );
    if mode != "tamper" {
        return;
    }
    // Tamper cases: each must be rejected by the native verifier or by V_d's statement check.
    let idx = |n: &str| inst.spec.iter().position(|t| t.name == n);
    let mut cases: Vec<(String, Vec<RowMajorMatrix<F>>, Vec<F>)> = vec![];
    for (name, row, col) in [("node", 0usize, 0usize), ("node", 5, 40), ("head", 1, 3), ("val", 2, 1), ("walk", 3, 7), ("uniq", 1, 2), ("ups", 4, 10), ("tx", 0, 5), ("akm", 1, 4), ("sha_t", 7, 100), ("size", 0, 0), ("srcp", 1, 1)] {
        if let Some(t) = idx(name) {
            let mut mats = inst.mats.clone();
            let w = mats[t].width;
            let h = mats[t].values.len() / w;
            let (r, c) = (row % h, col % w);
            mats[t].values[r * w + c] += F::ONE;
            cases.push((format!("{name}[{r}][{c}]+1"), mats, inst.pubs.clone()));
        }
    }
    {
        // a public message changed in the TAPE table: the prover's TAPE root no longer matches V_d's
        let t = idx("TAPE").unwrap();
        let mut mats = inst.mats.clone();
        mats[t].values[0] += F::ONE;
        cases.push(("TAPE[0][0]+1 (forged public message)".into(), mats, inst.pubs.clone()));
    }
    {
        // a header public value changed (the claim's prepared header)
        let mut pubs = inst.pubs.clone();
        let reader = inst.spec.iter().find(|t| t.num_pub > 0).map(|t| t.num_pub).unwrap_or(1);
        pubs[reader - 1] += F::ONE;
        cases.push((format!("pub[{}]+1 (header byte)", reader - 1), inst.mats.clone(), pubs));
    }
    let mut rejected = 0;
    for (name, mats, pubs) in &cases {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = eng.prove(&d_pk, ctx(&eng, &inst, mats, pubs)).ok()?;
            eng.verify(&vk, &p).ok()?;
            Some(check_statement(&eng, &inst, &p))
        }));
        let verdict = match r {
            Ok(Some(true)) => "ACCEPTED",
            Ok(Some(false)) => "rejected (V_d statement)",
            Ok(None) => "rejected (prove/verify)",
            Err(_) => "rejected (prover panicked)",
        };
        if verdict != "ACCEPTED" {
            rejected += 1;
        }
        println!("TAMPER {name}: {verdict}");
    }
    println!("TAMPER {rejected}/{} rejected", cases.len());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 4 {
        eprintln!("usage: {} <nearAirV3D1.json> <dump_dir> check|prove|tamper [small|pinned]", a[0]);
        std::process::exit(2);
    }
    cmd(&a[1], &a[2], &a[3], a.get(4).map(|s| s.as_str()).unwrap_or("small"));
}
