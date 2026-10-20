//! Packed-digit SHA-512/384 compression AIR (v2) on the pinned SWIRL backend
//! (SHA-384 transcript/Merkle hash, BabyBear Ext12, WHIR).  Digit width k from
//! NEARPROOF_SHA_K (1, 2 or 3; default 3).
//!
//! Usage:
//!   nearproof-sha384-air selftest [n_random]     correctness + debug checker + negative tests
//!   nearproof-sha384-air prove <n_compressions>  real proof, sizes, census, timings
//! Proof profile via the same env vars as native_sha384_driver.rs
//! (NEARPROOF_N_STACK, NEARPROOF_K, NEARPROOF_LOG_BLOWUP, NEARPROOF_ALL_LIST,
//! NEARPROOF_QUERY_BITS, NEARPROOF_INTERACTION_LOG).
mod air;
mod trace;

use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams,
    prover::{
        AirProvingContext, ColMajorMatrix, CpuColMajorBackend, DeviceDataTransporter,
        ProvingContext,
    },
    test_utils::test_system_params_small,
};
use p3_field::PrimeCharacteristicRing;
use std::sync::Arc;

#[allow(dead_code, clippy::all)]
mod config {
    use super::*;
    include!("../../../airbender/direct-wasm/native_sha384_config.rs");

    use crate::air::*;
    use crate::trace::*;
    use openvm_stark_backend::{
        air_builders::debug::{AirProofRawInput, debug_constraints_and_interactions},
        codec::Encode,
        keygen::types::MultiStarkProvingKey,
        soundness::SoundnessCalculator,
    };
    use p3_matrix::dense::RowMajorMatrix;

    fn setting(name: &str, default: usize) -> usize {
        std::env::var(name)
            .map(|s| s.parse().unwrap())
            .unwrap_or(default)
    }

    pub fn layout() -> Layout {
        Layout::new(setting("NEARPROOF_SHA_K", 3))
    }

    fn airs(lay: Layout) -> Vec<AirRef<SC>> {
        vec![
            Arc::new(Sha512Air { lay }),
            Arc::new(TableAir { lay }),
            Arc::new(HarnessAir),
        ]
    }

    fn to_f(v: &[u32]) -> Vec<F> {
        v.iter().map(|&x| F::from_u32(x)).collect()
    }

    struct Mats {
        pub main: RowMajorMatrix<F>,
        pub table: RowMajorMatrix<F>,
        pub harness: RowMajorMatrix<F>,
    }
    fn mats(t: &Traces) -> Mats {
        Mats {
            main: RowMajorMatrix::new(to_f(&t.main), t.lay.width),
            table: RowMajorMatrix::new(to_f(&t.table), T_WIDTH),
            harness: RowMajorMatrix::new(to_f(&t.harness), H_WIDTH),
        }
    }

    /// Engine with the native SHA-384/Ext12 profile; heights up to 2^log_h.
    fn engine(lay: &Layout, log_h: usize) -> Engine {
        let n_stack = setting("NEARPROOF_N_STACK", log_h.saturating_sub(2).max(8));
        let k = setting("NEARPROOF_K", 3);
        let blowup = setting("NEARPROOF_LOG_BLOWUP", 2);
        assert!((8..=22).contains(&n_stack) && (1..=5).contains(&k) && (1..=8).contains(&blowup));
        assert!(2 + n_stack + blowup <= 27);
        assert!(
            2 + n_stack >= log_h,
            "trace height 2^{log_h} exceeds 2^(l_skip+n_stack)"
        );
        let mut params = test_system_params_small(2, n_stack, k);
        let interaction_log = setting("NEARPROOF_INTERACTION_LOG", 27);
        assert!((20..=30).contains(&interaction_log));
        params.max_constraint_degree = lay.degree();
        params.logup.max_interaction_count = 1 << interaction_log;
        params.logup.pow_bits = 0;
        params.log_blowup = blowup;
        if setting("NEARPROOF_ALL_LIST", 1) == 1 {
            params.whir.proximity =
                openvm_stark_backend::WhirProximityStrategy::ListDecoding { m: 3 };
        }
        let bits = setting("NEARPROOF_QUERY_BITS", 268);
        params.whir = openvm_stark_backend::WhirConfig::new(
            params.log_blowup,
            params.l_skip + params.n_stack,
            openvm_stark_backend::WhirParams {
                k: params.whir.k,
                log_final_poly_len: params.log_final_poly_len(),
                proximity: params.whir.proximity,
                query_phase_pow_bits: 0,
                folding_pow_bits: 0,
                mu_pow_bits: 0,
            },
            bits,
        );
        println!(
            "PROFILE digit_k={} degree={} n_stack={} k={} log_blowup={} queries={:?} interaction_log={}",
            lay.k,
            lay.degree(),
            n_stack,
            k,
            blowup,
            params
                .whir
                .rounds
                .iter()
                .map(|r| r.num_queries)
                .collect::<Vec<_>>(),
            interaction_log
        );
        Engine::new(params)
    }

    fn ctx(m: Mats) -> ProvingContext<CpuColMajorBackend<SC>> {
        ProvingContext::new(vec![
            (
                0,
                AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.main), vec![]),
            ),
            (
                1,
                AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.table), vec![]),
            ),
            (
                2,
                AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.harness), vec![]),
            ),
        ])
    }

    /// Backend debug checker (constraints, then LogUp multiset balance); Err = panic message.
    fn check(
        pk: &MultiStarkProvingKey<SC>,
        airs: &[AirRef<SC>],
        m: &[&RowMajorMatrix<F>],
    ) -> Result<(), String> {
        let inputs: Vec<AirProofRawInput<F>> = m
            .iter()
            .map(|mat| AirProofRawInput {
                cached_mains: vec![],
                common_main: Some(Arc::new((*mat).clone())),
                public_values: vec![],
            })
            .collect();
        let pks: Vec<_> = pk.per_air.iter().collect();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            debug_constraints_and_interactions(airs, &pks, &inputs)
        }))
        .map_err(|e| {
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default()
        })
    }

    fn sha_vectors() -> Vec<(String, [u64; 8], Vec<[u64; 16]>, Vec<u8>)> {
        use sha2::Digest;
        let mut v = Vec::new();
        let long: Vec<u8> = (0..200u32).map(|i| (i * 7 + 3) as u8).collect();
        for (name, msg) in [("abc", b"abc".to_vec()), ("empty", vec![]), ("200B", long)] {
            v.push((
                format!("sha384({name})"),
                SHA384_IV,
                pad_message(&msg),
                sha2::Sha384::digest(&msg).to_vec(),
            ));
            v.push((
                format!("sha512({name})"),
                SHA512_IV,
                pad_message(&msg),
                sha2::Sha512::digest(&msg).to_vec(),
            ));
        }
        v
    }

    pub fn selftest(n_random: usize) {
        let lay = layout();
        let mut rng = Rng(0x9e3779b97f4a7c15);
        // 1. Native round function vs sha2 (sanity of the generator's reference).
        for _ in 0..10_000 {
            let c = rng.comp();
            assert_eq!(round_words(&c).out, sha2_compress(&c));
        }
        println!("SELFTEST native_reference_vs_sha2 pass=10000");
        // 2. Build a trace: known vectors (chained multi-block) + random compressions.
        let mut comps = Vec::new();
        let mut vec_checks = Vec::new();
        for (name, iv, blocks, digest) in sha_vectors() {
            let mut st = iv;
            let first = comps.len();
            for blk in &blocks {
                let c = Comp { h: st, block: *blk };
                st = sha2_compress(&c);
                comps.push(c);
            }
            vec_checks.push((name, first, blocks.len(), digest));
        }
        let n_vec = comps.len();
        for _ in 0..n_random {
            comps.push(rng.comp());
        }
        let t = gen_all(lay, &comps);
        // 3. Outputs read back from the AIR trace equal sha2's compression.
        let mut ok = 0;
        for (s, c) in comps.iter().enumerate() {
            assert_eq!(trace_output(&lay, &t.main, s), sha2_compress(c), "compression {s}");
            ok += 1;
        }
        for (name, first, nb, digest) in &vec_checks {
            // chain through the trace's own outputs
            let mut st = comps[*first].h;
            for b in 0..*nb {
                assert_eq!(comps[first + b].h, st);
                st = trace_output(&lay, &t.main, first + b);
            }
            let bytes: Vec<u8> = st.iter().flat_map(|w| w.to_be_bytes()).collect();
            assert_eq!(&bytes[..digest.len()], &digest[..], "{name}");
            println!("SELFTEST vector {name} blocks={nb} digest_ok");
        }
        println!("SELFTEST trace_outputs_vs_sha2 pass={ok} (vectors {n_vec} + random {n_random})");
        // 4. Backend debug checker on the full trace.
        let log_h = t.main_height.trailing_zeros() as usize;
        let eng = engine(&lay, log_h.max(10));
        let airs = airs(lay);
        let kt = std::time::Instant::now();
        let (pk, _vk) = eng.keygen(&airs);
        println!("KEYGEN_SECONDS {:.2}", kt.elapsed().as_secs_f64());
        print_airs(&pk);
        let m = mats(&t);
        let start = std::time::Instant::now();
        check(&pk, &airs, &[&m.main, &m.table, &m.harness])
            .expect("debug checker rejected honest trace");
        println!(
            "SELFTEST debug_checker pass rows={} compressions={} secs={:.1}",
            t.main_height,
            comps.len(),
            start.elapsed().as_secs_f64()
        );
        // 5. Negative tests on a small trace.
        negative(&lay, &pk, &airs);
    }

    /// Columns referenced at the next row (offset 1) anywhere in constraints or interactions.
    fn next_row_columns(p: &openvm_stark_backend::keygen::types::StarkProvingKey<SC>) -> usize {
        use openvm_stark_backend::air_builders::symbolic::{
            SymbolicExpressionNode, symbolic_variable::Entry,
        };
        let mut cols = std::collections::BTreeSet::new();
        for node in &p.vk.symbolic_constraints.constraints.nodes {
            if let SymbolicExpressionNode::Variable(v) = node {
                if let Entry::Main { offset: 1, .. } = v.entry {
                    cols.insert(v.index);
                }
            }
        }
        cols.len()
    }

    fn print_airs(pk: &MultiStarkProvingKey<SC>) {
        for p in &pk.per_air {
            println!(
                "AIR {} next_row_cols={} width={:?} degree={} constraints={} interactions={} need_rot={} dag_nodes={}",
                p.air_name,
                next_row_columns(p),
                p.vk.params.width.main_widths(),
                p.vk.max_constraint_degree,
                p.vk.symbolic_constraints.constraints.constraint_idx.len(),
                p.vk.symbolic_constraints.interactions.len(),
                p.vk.params.need_rot,
                p.vk.symbolic_constraints.constraints.nodes.len()
            );
        }
    }

    fn category(lay: &Layout, col: usize) -> &'static str {
        if col < lay.e0 {
            "a_digits"
        } else if col < lay.w0 {
            "e_digits"
        } else if col < lay.ndig {
            "w_digits"
        } else if col < lay.de {
            "partial_sum_SA"
        } else if col < lay.v0 {
            "copy_DE"
        } else if col < lay.c1a {
            "received_V"
        } else if col < lay.r {
            "carry"
        } else if col == lay.r {
            "row_index"
        } else if col == lay.g {
            "global_row"
        } else {
            "flag"
        }
    }

    fn by(res: &Result<(), String>) -> &'static str {
        match res {
            Ok(()) => "-",
            Err(s) if s.contains("LogUp") => "bus",
            Err(_) => "constraint",
        }
    }

    fn negative(lay: &Layout, pk: &MultiStarkProvingKey<SC>, airs: &[AirRef<SC>]) {
        let lay = *lay;
        let w = lay.width;
        let mut rng = Rng(0x1234_5678_9abc_def1);
        let comps: Vec<Comp> = (0..3).map(|_| rng.comp()).collect();
        let t = gen_all(lay, &comps);
        let m = mats(&t);
        check(pk, airs, &[&m.main, &m.table, &m.harness]).expect("honest small trace");
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let mut stats: std::collections::BTreeMap<String, (usize, usize, usize, usize)> =
            Default::default();
        let mut undetected = Vec::new();
        // rows: trace row 0, every row type of segment 1, the first padding row and the last row
        let mut rows: Vec<usize> = vec![0];
        rows.extend(
            [0usize, 1, 2, 3, 8, 9, 10, 17, 33, 37, 38, 39, 40, 41, 42]
                .iter()
                .map(|r| ROWS + r),
        );
        // padding: first zero row, one in the middle, the last row
        rows.extend([3 * ROWS, (3 * ROWS + t.main_height) / 2, t.main_height - 1]);
        assert!(t.main[3 * ROWS * w..].iter().all(|&v| v == 0), "padding must be all zero");
        // Digits: move to another in-range value (v -> v xor 1); other cells: +1.
        let newval = |v: F, digit: bool| {
            if digit {
                F::from_u32(v.as_canonical_u32() ^ 1)
            } else {
                v + F::ONE
            }
        };
        let mut run = |label: String, which: usize, idx: usize, nv: &dyn Fn(F) -> F| {
            let mut mm = match which {
                0 => m.main.clone(),
                1 => m.table.clone(),
                _ => m.harness.clone(),
            };
            mm.values[idx] = nv(mm.values[idx]);
            let res = match which {
                0 => check(pk, airs, &[&mm, &m.table, &m.harness]),
                1 => check(pk, airs, &[&m.main, &mm, &m.harness]),
                _ => check(pk, airs, &[&m.main, &m.table, &mm]),
            };
            let e = stats.entry(label.clone()).or_default();
            e.0 += 1;
            match res {
                Ok(()) => undetected.push(format!("{label} idx={idx}")),
                Err(msg) if msg.contains("LogUp") => e.2 += 1,
                Err(_) => e.1 += 1,
            }
            e.3 = e.1 + e.2;
        };
        for &gi in &rows {
            for col in 0..w {
                let d = col < lay.ndig;
                run(format!("main/{}", category(&lay, col)), 0, gi * w + col, &|v| newval(v, d));
                if d && lay.dsize(col % lay.nd) > 1 {
                    // second in-range mutation: flip the digit's top bit
                    let top = 1u32 << (lay.dsize(col % lay.nd) - 1);
                    run(format!("main/{}_topbit", category(&lay, col)), 0, gi * w + col,
                        &|v| F::from_u32(v.as_canonical_u32() ^ top));
                }
            }
        }
        // Out-of-range digit: +2^s on a digit (constraint must reject).
        for &gi in &rows {
            for col in [lay.a0 + 3, lay.e1 + 5, lay.w0 + 7, lay.w1 + lay.nd - 1] {
                let s = lay.dsize((col - lay.a0) % lay.nd);
                run("main/digit_out_of_range".into(), 0, gi * w + col, &|v| v + F::from_u32(1 << s));
            }
        }
        for i in [0usize, 1, 7, 31, 41, 43, 44, 47, 48, 63] {
            for col in 0..T_WIDTH {
                run("table".into(), 1, i * T_WIDTH + col, &|v| newval(v, col < 11));
            }
        }
        for i in [0usize, 3, 4, 11, 12, 15, 16, 47] {
            for col in 0..H_WIDTH {
                run("harness".into(), 2, i * H_WIDTH + col, &|v| newval(v, false));
            }
        }
        // Consistent forgery: flip an output bit AND the interface consumer's copy.
        {
            let mut mm = m.main.clone();
            let mut hh = m.harness.clone();
            let gi = ROWS + 42;
            let idx = gi * w + lay.a1; // H'_0, digit 0 of compression 1
            let old = mm.values[idx].as_canonical_u32();
            mm.values[idx] = F::from_u32(old ^ 1);
            let hrow = 16 + 12; // compression 1, pair 12 = (H'_0, H'_1); limb 0 of H'_0
            let d = if old & 1 == 1 { -F::ONE } else { F::ONE };
            hh.values[hrow * H_WIDTH + 2] += d;
            let res = check(pk, airs, &[&mm, &m.table, &hh]);
            println!(
                "NEGATIVE consistent_output_forgery detected={} by={}",
                res.is_err(),
                by(&res)
            );
        }
        // Constraint-consistent edits: each keeps every AIR constraint satisfied, so only a
        // bus (LogUp) can reject it.  Top-limb edits: the top carry feeds no further limb.
        {
            let top = F::from_u32(1 << lay.lw(2));
            let at = |r: usize, col: usize| (ROWS + r) * w + col;
            let edits: Vec<(&str, Vec<(usize, F)>)> = vec![
                // row x stores values for row x+1
                ("sched_received_V0_plus_carry", vec![(at(19, lay.v0 + 2), top), (at(19, lay.cw0 + 2), F::ONE)]),
                ("sched_received_V1_plus_carry", vec![(at(24, lay.v1 + 2), top), (at(24, lay.cw1 + 2), F::ONE)]),
                ("sched_W7a_residual_via_carry", vec![(at(29, lay.cw0 + 2), F::ONE)]),
                ("sched_W7b_residual_via_carry", vec![(at(30, lay.cw1 + 2), F::ONE)]),
                ("round_d_minus_T2_residual_via_carry", vec![(at(14, lay.c0e + 2), F::ONE)]),
                ("round_K0_residual_via_carry", vec![(at(11, lay.c0a + 2), F::ONE)]),
                ("round_K1_residual_via_carry", vec![(at(12, lay.c1a + 2), F::ONE)]),
                ("round_d_residual_via_carry", vec![(at(13, lay.c1e + 2), F::ONE)]),
                ("out_IV_residual_via_carry_row42", vec![(at(41, lay.c0a + 2), F::ONE)]),
                ("out_fin_residual_via_carry_row0_H3", vec![(at(0, lay.c1a + 2), F::ONE)]),
                ("out_fin_residual_via_carry_row1_H6", vec![(at(0, lay.c0e + 2), F::ONE)]),
            ];
            for (name, ed) in edits {
                let mut mm = m.main.clone();
                for (idx, dv) in ed {
                    mm.values[idx] += dv;
                }
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE_BUS {name} detected={} by={}", res.is_err(), by(&res));
            }
            // Range check (polynomial now): flip W[79] bit 63 (feeds only round 79) and
            // re-solve the three top-limb carries to ±1/2 mod p: every other relation holds.
            {
                use p3_field::Field;
                let mut mm = m.main.clone();
                let dj = 63 / lay.k;
                let bit = 63 - lay.k * dj;
                let idx = at(41, lay.w1 + dj);
                let v = mm.values[idx].as_canonical_u32();
                let up = (v >> bit) & 1 == 0;
                mm.values[idx] = F::from_u32(v ^ (1 << bit));
                let half = F::from_u32(2).inverse();
                let d = if up { half } else { -half };
                mm.values[at(40, lay.cw1 + 2)] -= d;
                mm.values[at(40, lay.c1a + 2)] += d;
                mm.values[at(40, lay.c1e + 2)] += d;
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE carry_range_half detected={} by={}", res.is_err(), by(&res));
            }
            // Padding region: a copy of a real row placed in the zero tail, a fake complete
            // compression segment right after the last real one (consistent trace, no consumer
            // messages), and the same segment one row further (not contiguous).
            {
                let mut mm = m.main.clone();
                let (src, dst) = (ROWS + 20, (3 * ROWS + t.main_height) / 2);
                for col in 0..w {
                    mm.values[dst * w + col] = mm.values[src * w + col];
                }
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE_PAD fake_real_row_in_padding detected={} by={}", res.is_err(), by(&res));
                let mut c4 = comps.clone();
                c4.push(rng.comp());
                let t4 = gen_all(lay, &c4);
                let m4 = mats(&t4);
                let res = check(pk, airs, &[&m4.main, &m4.table, &m.harness]);
                println!("NEGATIVE_PAD fake_segment_after_last detected={} by={}", res.is_err(), by(&res));
                let mut mm = m4.main.clone();
                let seg = 3 * ROWS * w;
                let block: Vec<F> = mm.values[seg..seg + ROWS * w].to_vec();
                for v in &mut mm.values[seg..seg + (ROWS + 1) * w] {
                    *v = F::ZERO;
                }
                mm.values[seg + w..seg + (ROWS + 1) * w].copy_from_slice(&block);
                let res = check(pk, airs, &[&mm, &m4.table, &m.harness]);
                println!("NEGATIVE_PAD fake_segment_after_gap detected={} by={}", res.is_err(), by(&res));
            }
            // A different (input state, block) with a fully consistent AIR trace but the
            // consumer's original messages: only the interface bus can reject it.
            for (name, edit_iv) in [("interface_block_word", false), ("interface_input_state", true)] {
                let mut c2 = comps.clone();
                if edit_iv {
                    c2[1].h[5] ^= 1 << 17
                } else {
                    c2[1].block[9] ^= 1 << 40
                }
                let t2 = gen_all(lay, &c2);
                let m2 = mats(&t2);
                let res = check(pk, airs, &[&m2.main, &m2.table, &m.harness]);
                println!("NEGATIVE_BUS {name} detected={} by={}", res.is_err(), by(&res));
            }
        }
        std::panic::set_hook(prev_hook);
        let mut total = (0, 0);
        for (k, (n, c, b, d)) in &stats {
            println!("NEGATIVE {k} mutations={n} detected={d} by_constraint={c} by_bus={b}");
            total.0 += n;
            total.1 += d;
        }
        println!(
            "NEGATIVE total mutations={} detected={} undetected={}",
            total.0,
            total.1,
            undetected.len()
        );
        for u in undetected.iter().take(50) {
            println!("UNDETECTED {u}");
        }
    }

    pub fn negative_main() {
        let lay = layout();
        let eng = engine(&lay, 10);
        let airs = airs(lay);
        let (pk, _) = eng.keygen(&airs);
        print_airs(&pk);
        negative(&lay, &pk, &airs);
    }

    fn peak_rss_kib() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("VmHWM"))
                    .and_then(|l| l.split_whitespace().nth(1)?.parse().ok())
            })
            .unwrap_or(0)
    }

    pub fn prove(n: usize) {
        let mut rng = Rng(0xdead_beef_cafe_f00d ^ n as u64);
        let comps: Vec<Comp> = (0..n).map(|_| rng.comp()).collect();
        let tg = std::time::Instant::now();
        let lay = layout();
        let t = gen_all(lay, &comps);
        let tracegen = tg.elapsed().as_secs_f64();
        let log_h = t.main_height.trailing_zeros() as usize;
        let eng = engine(&lay, log_h);
        let airs = airs(lay);
        let kt = std::time::Instant::now();
        let (pk, vk) = eng.keygen(&airs);
        println!("KEYGEN_SECONDS {:.2}", kt.elapsed().as_secs_f64());
        print_airs(&pk);
        let bound = SoundnessCalculator::calculate_from_vk(&vk);
        let target = setting("NEARPROOF_QUERY_BITS", 268) as f64;
        println!(
            "SOUNDNESS target={} total={:.1} logup={:.1} proximity={:.1} query={:.1}",
            target,
            bound.total_bits,
            bound.logup_bits,
            bound.whir_details.proximity_gaps_bits,
            bound.whir_details.query_bits
        );
        assert!(
            bound.total_bits >= target,
            "component budget failed; not proving this profile"
        );
        let main_cells = t.main_height * lay.width;
        println!(
            "SHAPE n={} main_rows_used={} main_height={} main_width={} main_cells={} cells_per_compression_padded={:.1} cells_per_compression_dense={} table={}x{} harness={}x{}",
            n,
            n * ROWS,
            t.main_height,
            lay.width,
            main_cells,
            main_cells as f64 / n as f64,
            ROWS * lay.width,
            64,
            T_WIDTH,
            t.harness_height,
            H_WIDTH
        );
        let m = mats(&t);
        drop(t);
        let c = ctx(m);
        let d_pk = eng.device().transport_pk_to_device(&pk);
        let pt = std::time::Instant::now();
        let proof = eng
            .prove(&d_pk, c)
            .map_err(|e| format!("{e:?}"))
            .expect("prove");
        let prove_s = pt.elapsed().as_secs_f64();
        let vt = std::time::Instant::now();
        eng.verify(&vk, &proof).expect("verify");
        let verify_s = vt.elapsed().as_secs_f64();
        fn size<T: Encode>(x: &T) -> usize {
            let mut b = Vec::new();
            x.encode(&mut b).unwrap();
            b.len()
        }
        let mut bytes = Vec::new();
        proof.encode(&mut bytes).unwrap();
        let w = &proof.whir_proof;
        let mut digests = Vec::new();
        for groups in [&w.initial_round_merkle_proofs, &w.codeword_merkle_proofs] {
            for queries in groups {
                for path in queries {
                    for d in path {
                        digests.extend(digest_bytes(*d));
                    }
                }
            }
        }
        let unique: std::collections::BTreeSet<_> = digests.chunks_exact(48).collect();
        let base_values: usize = w
            .initial_round_opened_rows
            .iter()
            .flat_map(|x| x.iter())
            .flat_map(|x| x.iter())
            .map(|x| x.len())
            .sum();
        let ext_values: usize = w
            .codeword_opened_values
            .iter()
            .flat_map(|x| x.iter())
            .map(|x| x.len())
            .sum();
        println!(
            "PROOF_BYTES total={} gkr={} relations={} stacking={} whir={}",
            bytes.len(),
            size(&proof.gkr_proof),
            size(&proof.batch_constraint_proof),
            size(&proof.stacking_proof),
            size(&proof.whir_proof)
        );
        println!(
            "WHIR_CENSUS auth_bytes={} auth_digests={} unique_auth_digests={} initial_values_bytes={} codeword_values_bytes={}",
            digests.len(),
            digests.len() / 48,
            unique.len(),
            base_values * 4,
            ext_values * 48
        );
        println!(
            "TIMES tracegen_s={:.2} prove_s={:.2} verify_s={:.3}",
            tracegen, prove_s, verify_s
        );
        println!("PEAK_RSS_KIB {}", peak_rss_kib());
        if let Ok(dir) = std::env::var("NEARPROOF_PROOF_OUT") {
            std::fs::write(format!("{dir}/sha384-air-n{n}.proof"), &bytes).unwrap();
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn outputs_and_checker_small() {
            let mut rng = Rng(7);
            let comps: Vec<Comp> = (0..20).map(|_| rng.comp()).collect();
            for k in 1..=3 {
            let lay = Layout::new(k);
            let t = gen_all(lay, &comps);
            for (s, c) in comps.iter().enumerate() {
                assert_eq!(trace_output(&lay, &t.main, s), sha2_compress(c));
            }
            let eng = engine(&lay, 10);
            let airs = airs(lay);
            let (pk, _) = eng.keygen(&airs);
            let m = mats(&t);
            check(&pk, &airs, &[&m.main, &m.table, &m.harness]).unwrap();
            // one corrupted state bit must be rejected
            let mut bad = m.main.clone();
            let idx = (ROWS + 20) * lay.width + lay.a1 + 3;
            bad.values[idx] = F::from_u32(bad.values[idx].as_canonical_u32() ^ 1);
            let prev = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));
            let r = check(&pk, &airs, &[&bad, &m.table, &m.harness]);
            std::panic::set_hook(prev);
            assert!(r.is_err());
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("selftest") => {
            config::selftest(args.get(2).map(|s| s.parse().unwrap()).unwrap_or(1000))
        }
        Some("negative") => config::negative_main(),
        Some("prove") => config::prove(args[2].parse().unwrap()),
        _ => eprintln!("usage: selftest [n] | negative | prove <n>"),
    }
}
