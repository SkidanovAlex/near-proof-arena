//! Spike #1 (V3-PERF-DESIGN §9): register-form WASM chips on the np-udr-stark-v2 prover.
//!
//! ```text
//! wasmchip run <measured|loadchain|mem> <iters> [--prove] [--tamper]
//! wasmchip bench-hash [mib]
//! wasmchip bench-commit <log_n> <width> <log_blowup>
//! ```
//! All timings are on whatever CPUs the process is pinned to (run under
//! `nice -n 19 taskset -c 9,25`, RAYON_NUM_THREADS=2): contended, indicative only.
mod chips;
mod wasm;

use std::time::Instant;

use npudr::aux::{AuxLayout, table_degree};
use npudr::field::{F, omega, shift};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use rayon::prelude::*;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("run") => run(&a[2], a[3].parse().unwrap(), a.iter().any(|s| s == "--prove"), a.iter().any(|s| s == "--tamper")),
        Some("bench-hash") => bench_hash(a.get(2).map(|s| s.parse().unwrap()).unwrap_or(256)),
        Some("bench-commit") => bench_commit(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        _ => eprintln!("usage: see src/main.rs"),
    }
}

fn prog(name: &str, iters: u64) -> wasm::Prog {
    match name {
        "measured" => wasm::measured_loop(iters),
        "loadchain" => wasm::load_chain(iters, 16),
        "mem" => wasm::mem_loop(iters),
        _ => panic!("unknown program {name}"),
    }
}

fn run(name: &str, iters: u64, prove: bool, tamper: bool) {
    let p = prog(name, iters);
    let t0 = Instant::now();
    let (ops, loc, mem) = wasm::interpret(&p);
    let t_interp = t0.elapsed().as_secs_f64();
    let rp = wasm::translate(&p);
    let t1 = Instant::now();
    let run = wasm::execute(&rp, &p);
    let t_exec = t1.elapsed().as_secs_f64();
    // differential check: register machine == reference interpreter
    for (i, v) in loc.iter().enumerate() {
        let got = run.mem.cur.get(&(0, i as u32)).map(|x| wasm::unlimbs(&x.0)).unwrap_or(p.locals0[i]);
        assert_eq!(got, *v, "local {i} differs");
    }
    for (w, v) in &mem {
        let got = run.mem.cur.get(&(1, *w)).map(|x| wasm::unlimbs(&x.0) as u32).unwrap_or(*p.mem0.get(w).unwrap_or(&0));
        assert_eq!(got, *v, "memory word {w} differs");
    }
    let fee: u64 = run.final_state.2 as u64;
    assert_eq!(fee, ops, "gas units (block-level fees) must equal executed WASM ops");
    println!("program: {} | iterations {iters}", p.name);
    println!(
        "  WASM ops executed {ops} | register-form rows {} | ops/row {:.2} | static rows {} | gas units {fee} (= ops: OK) | locals+memory match reference: OK",
        run.steps.len(),
        ops as f64 / run.steps.len() as f64,
        rp.rows.len()
    );
    println!("  reference interpreter {:.3} s, register machine (recording accesses) {:.3} s", t_interp, t_exec);
    let t2 = Instant::now();
    let b = chips::build(&rp, &run);
    println!("  trace build {:.3} s", t2.elapsed().as_secs_f64());
    // self-check: constraints + buses
    let t3 = Instant::now();
    let mut bad = 0;
    for (t, tr) in b.air.tables.iter().zip(&b.traces) {
        let f = npudr::check::failing_constraints(t, tr, &[], 5);
        if !f.is_empty() {
            println!("  FAIL constraints in {}: {:?}", t.name, f);
            bad += f.len();
        }
    }
    let imb = npudr::check::bus_imbalance(&b.air, &b.traces, &[]);
    for i in imb.iter().take(5) {
        println!("  FAIL bus imbalance {:?}", i);
    }
    println!(
        "  honest trace: {} failing constraints, {} unbalanced bus messages ({:.2} s)",
        bad,
        imb.len(),
        t3.elapsed().as_secs_f64()
    );
    report(&b, ops);
    if prove {
        prove_verify(&b, "honest");
    }
    if tamper {
        tamper_tests(&b);
    }
}

/// Committed-cell accounting, per active row, under several backends (E = extension degree).
fn report(b: &chips::Built, ops: u64) {
    println!("\n  table        kind   active   padded   w   I  aux(GP) deg | W_eq(prover, padded) | per active row: GP/E=10  logUp-k2/E=10  GKR/E=10  multilin");
    let mut tot = [0f64; 7]; // main, fractions, weq_prover, gp10, logup10, gkr10, ml
    let mut fixed = [0f64; 7];
    for (i, t) in b.air.tables.iter().enumerate() {
        let w = t.width as f64;
        let ni = t.interactions.len() as f64;
        let aux = AuxLayout::new(t, 1).width() as f64;
        let d = table_degree(t, 1);
        let q = (d - 1) as f64;
        let h = b.traces[i].height() as f64;
        let act = b.active[i] as f64;
        let weq = (w + 8.0 * aux + 8.0 * q) * h;
        let e = 10.0;
        let gp = w + e * aux + e * q;
        let lu = w + e * ((ni / 2.0).ceil() + 1.0) + e * 2.0;
        let gkr = w + e * 2.0;
        let ml = w;
        println!(
            "  {:12} {:5} {:8} {:8} {:3} {:3} {:4} {:3} | {:20.0} | {:8.0} {:13.0} {:9.0} {:8.0}",
            t.name, b.kind[i], b.active[i], h as usize, t.width, t.interactions.len(), aux as usize, d, weq, gp, lu, gkr, ml
        );
        let v = [w * act, ni * act, weq, gp * act, lu * act, gkr * act, ml * act];
        let tgt = if b.kind[i] == "fixed" { &mut fixed } else { &mut tot };
        for j in 0..7 {
            tgt[j] += v[j];
        }
    }
    let o = ops as f64;
    println!("\n  per WASM op (chips + memory boundary, active rows; fixed lookup/code/io tables excluded):");
    println!(
        "    main cells {:.1} | bus fractions {:.1} | committed cells: GP(E=10) {:.1}, logUp-k2(E=10) {:.1}, GKR-logUp(E=10) {:.1}, multilinear {:.1} | prover-actual W_eq (E=8, GP, padded) {:.1}",
        tot[0] / o, tot[1] / o, tot[3] / o, tot[4] / o, tot[5] / o, tot[6] / o, tot[2] / o
    );
    println!(
        "  fixed tables (range16/pair/code/io; amortised over a segment): main {:.2} M cells, prover W_eq {:.2} M",
        fixed[0] / 1e6,
        fixed[2] / 1e6
    );
}

fn prove_verify(b: &chips::Built, label: &str) -> bool {
    let opts = npudr::prover::ProveOptions { verbose: false };
    let t0 = Instant::now();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        npudr::prover::prove_bytes(&b.air, b.traces.clone(), &[], &[], &opts)
    }));
    let dt = t0.elapsed().as_secs_f64();
    let bytes = match r {
        Ok(Ok(v)) => v,
        Ok(Err(e)) => {
            println!("  [{label}] prover returned error after {dt:.1} s: {e}");
            return false;
        }
        Err(_) => {
            println!("  [{label}] prover panicked after {dt:.1} s");
            return false;
        }
    };
    let weq: f64 = b
        .air
        .tables
        .iter()
        .zip(&b.traces)
        .map(|(t, tr)| {
            (t.width + 8 * AuxLayout::new(t, 1).width() + 8 * (table_degree(t, 1) - 1)) as f64 * tr.height() as f64
        })
        .sum();
    let main: f64 = b.traces.iter().map(|t| (t.width() * t.height()) as f64).sum();
    let t1 = Instant::now();
    let v = npudr::verifier::verify(&b.air, &[], &[], &bytes);
    println!(
        "  [{label}] np-udr-stark-v2 params (BabyBear, Fp8, blowup 16, 216 queries, SHA-256 WH): prove {dt:.1} s | proof {} KB | committed W_eq {:.1} M ({:.2} M W_eq/s), main {:.1} M | Rust verify: {} ({:.2} s)",
        bytes.len() / 1024,
        weq / 1e6,
        weq / dt / 1e6,
        main / 1e6,
        if v.is_ok() { "ACCEPT".to_string() } else { format!("REJECT ({})", v.clone().unwrap_err()) },
        t1.elapsed().as_secs_f64()
    );
    v.is_ok()
}

fn tamper_tests(b: &chips::Built) {
    // T3: verifier-side: an honest proof with one byte flipped at several offsets must be rejected
    {
        let opts = npudr::prover::ProveOptions { verbose: false };
        let bytes = npudr::prover::prove_bytes(&b.air, b.traces.clone(), &[], &[], &opts).expect("honest proof");
        let mut rej = 0;
        let offs: Vec<usize> = (1..=16).map(|k| k * bytes.len() / 17).collect();
        for &o in &offs {
            let mut t = bytes.clone();
            t[o] ^= 0x01;
            if npudr::verifier::verify(&b.air, &[], &[], &t).is_err() {
                rej += 1;
            }
        }
        println!("\n  T3 (proof bytes, 1 bit flipped at {} spread offsets): rejected {rej}/{}", offs.len(), offs.len());
    }
    let alu = b.air.tables.iter().position(|t| t.name == "alu_ri" || t.name == "ld").expect("alu_ri or ld table");
    let names = &b.air.tables[alu].name;
    println!("\n  tamper tests on table {names}:");
    // T1: break an arithmetic/limb relation (constraint violation)
    {
        let mut tr = b.traces.clone();
        let w = tr[alu].width();
        let c = if names == "alu_ri" { 15 } else { 15 }; // a column inside the value block
        tr[alu].values[c] += F::ONE;
        let _ = w;
        let f = npudr::check::failing_constraints(&b.air.tables[alu], &tr[alu], &[], 3);
        let imb = npudr::check::bus_imbalance(&b.air, &tr, &[]).len();
        println!("    T1 (+1 on column {c} of row 0): failing constraints {:?}, unbalanced messages {imb}", f);
        let bb = chips::Built { air: b.air.clone(), traces: tr, active: b.active.clone(), kind: b.kind.clone() };
        let ok = prove_verify(&bb, "T1 tampered");
        println!("    T1 => {}", if ok { "UNSOUND: accepted" } else { "rejected (expected)" });
    }
    // T2: consistent local arithmetic but wrong memory value (bus-only violation):
    // alu_ri row 0 (an add or sub): bump the operand A limb 3 and the matching result limb.
    if names == "alu_ri" {
        let mut tr = b.traces.clone();
        let t = &b.air.tables[alu];
        let _ = t;
        // column layout of alu_ri: act pc ts fp u fee nxt sub aoff doff A0..3 I0..3 C0..3 ...
        let (a3, c3) = (10 + 3, 18 + 3);
        let sub = tr[alu].values[7];
        let (ca, cc) = (tr[alu].values[a3], tr[alu].values[c3]);
        // keep A3 + I3 + k2 = C3 + 2^16 k3 (add) or C3 + I3 + k2 = A3 + 2^16 k3 (sub): shift both by the same delta
        let delta = F::ONE;
        tr[alu].values[a3] = ca + delta;
        tr[alu].values[c3] = cc + delta;
        let _ = sub;
        let f = npudr::check::failing_constraints(&b.air.tables[alu], &tr[alu], &[], 3);
        let imb = npudr::check::bus_imbalance(&b.air, &tr, &[]).len();
        println!("    T2 (operand read != memory, arithmetic kept consistent): failing constraints {:?}, unbalanced messages {imb}", f);
        let bb = chips::Built { air: b.air.clone(), traces: tr, active: b.active.clone(), kind: b.kind.clone() };
        let ok = prove_verify(&bb, "T2 tampered");
        println!("    T2 => {}", if ok { "UNSOUND: accepted" } else { "rejected (expected)" });
    }
}

// ---------------------------------------------------------------------------------------
// micro-benchmarks
// ---------------------------------------------------------------------------------------

fn bench_hash(mib: usize) {
    use sha2::digest::generic_array::GenericArray;
    let nthreads = rayon::current_num_threads();
    let n512 = mib * (1 << 20) / 128;
    let n256 = mib * (1 << 20) / 64;
    let data: Vec<u8> = (0..mib * (1 << 20)).map(|i| (i * 2654435761usize >> 13) as u8).collect();
    // SHA-512 compression (= SHA-384 compression): single thread
    let blocks512: Vec<GenericArray<u8, sha2::digest::consts::U128>> =
        data.chunks(128).map(|c| GenericArray::clone_from_slice(c)).collect();
    let blocks256: Vec<GenericArray<u8, sha2::digest::consts::U64>> =
        data.chunks(64).map(|c| GenericArray::clone_from_slice(c)).collect();
    let mut st = [0x6a09e667f3bcc908u64, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179];
    let t0 = Instant::now();
    sha2::compress512(&mut st, &blocks512);
    let d512 = t0.elapsed().as_secs_f64();
    let mut st2 = [0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let t1 = Instant::now();
    sha2::compress256(&mut st2, &blocks256);
    let d256 = t1.elapsed().as_secs_f64();
    // parallel (independent streams)
    let t2 = Instant::now();
    blocks512.par_chunks(4096).for_each(|c| {
        let mut s = st;
        sha2::compress512(&mut s, c);
        std::hint::black_box(s);
    });
    let p512 = t2.elapsed().as_secs_f64();
    println!(
        "bench-hash ({mib} MiB; {nthreads} rayon threads): SHA-512/384 compression 1 thread {:.2} M/s ({:.0} MB/s), {nthreads} threads {:.2} M/s | SHA-256 compression (SHA-NI if available) 1 thread {:.2} M/s ({:.0} MB/s) [{:x}{:x}]",
        n512 as f64 / d512 / 1e6,
        (mib as f64 * 1.048576) / d512,
        n512 as f64 / p512 / 1e6,
        n256 as f64 / d256 / 1e6,
        (mib as f64 * 1.048576) / d256,
        st[0] & 0xff,
        st2[0] & 0xff
    );
}

/// Rate-1/2^lb LDE (iDFT + coset DFTs, cache-blocked `npudr::lde::CosetDft`) and a SHA-384
/// Merkle commitment of the LDE rows (one leaf per LDE row; binary tree, 48-byte nodes).
fn bench_commit(log_n: usize, w: usize, lb: usize) {
    use sha2::{Digest, Sha384};
    let n = 1usize << log_n;
    let tr: Vec<F> = (0..n * w)
        .into_par_iter()
        .map(|i| F::from_u64((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 34))
        .collect();
    let cd = npudr::lde::CosetDft::new(log_n);
    let t0 = Instant::now();
    let mut coef = vec![F::ZERO; n * w];
    cd.idft(&tr, w, &mut coef);
    let t_idft = t0.elapsed().as_secs_f64();
    let nb = 1usize << lb;
    let mut lde = vec![F::ZERO; n * w * nb];
    let t1 = Instant::now();
    for (bi, blk) in lde.chunks_mut(n * w).enumerate() {
        let c = shift() * omega(log_n + lb).exp_u64(bi as u64);
        cd.eval(&coef, w, c, blk);
    }
    let t_lde = t1.elapsed().as_secs_f64();
    let t2 = Instant::now();
    let leaves: Vec<[u8; 48]> = lde
        .par_chunks(w)
        .map(|row| {
            let mut h = Sha384::new();
            h.update([0x01u8]);
            for v in row {
                use p3_field::PrimeField32;
                h.update(v.as_canonical_u32().to_le_bytes());
            }
            h.finalize().into()
        })
        .collect();
    let t_leaf = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    let mut lvl = leaves;
    while lvl.len() > 1 {
        lvl = lvl
            .par_chunks(2)
            .map(|p| {
                let mut h = Sha384::new();
                h.update([0x02u8]);
                h.update(p[0]);
                h.update(p[1]);
                h.finalize().into()
            })
            .collect();
    }
    let t_node = t3.elapsed().as_secs_f64();
    let cells = (n * w) as f64;
    let tot = t_idft + t_lde + t_leaf + t_node;
    println!(
        "bench-commit 2^{log_n} x {w}, blowup 2^{lb} ({} threads): iDFT {:.3} s, coset DFTs {:.3} s, SHA-384 leaves {:.3} s, nodes {:.3} s | total {:.3} s = {:.1} ns/trace cell ({:.2} M trace cells/s); hashing share {:.0} % [{:02x}]",
        rayon::current_num_threads(),
        t_idft,
        t_lde,
        t_leaf,
        t_node,
        tot,
        tot / cells * 1e9,
        cells / tot / 1e6,
        100.0 * (t_leaf + t_node) / tot,
        lvl[0][0]
    );
}
