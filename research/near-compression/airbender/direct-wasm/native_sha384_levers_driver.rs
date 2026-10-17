// Native SHA-384/Ext12 driver with proof-size levers (lane/pq-whir-levers).
// With all lever variables unset it runs exactly the native_sha384_driver.rs profile.
//
// Lever environment (defaults = upstream):
//   NEARPROOF_K1=<k>             first-round folding factor (0 = same as NEARPROOF_K)
//   NEARPROOF_LOG_FINAL=<n>      log2 final-polynomial length (default (2+n_stack) % k)
//   NEARPROOF_MULTIPROOF=1       batched multiproof per round (dedup siblings)
//   NEARPROOF_KEEP_DOMAIN=1      non-halving WHIR domains
//   NEARPROOF_LIST_M=<m>         list-decoding multiplicity (with NEARPROOF_ALL_LIST=1; default 3)
//   NEARPROOF_QUERY_POW / NEARPROOF_FOLDING_POW / NEARPROOF_MU_POW = grinding bits
//   NEARPROOF_DIGEST_BYTES=42    truncated Merkle digests (default 48)
//   NEARPROOF_COSET_LEAF=1       one SHA-384 message per WHIR leaf (fold coset)
//   NEARPROOF_DUMMY=1            prove the shape-equivalent dummy AIR instead of the literal child
//     NEARPROOF_DUMMY_COLS (460), NEARPROOF_DUMMY_LOG_HEIGHT (14)
//   NEARPROOF_SHA_AIR=<n>        prove the L3 SHA-512/384 compression AIR (lane/pq-sha384-air @58889824f)
//                                on n random compressions (main 442 cols x 44n rows, table, harness)
//   NEARPROOF_GRUEN_GKR / NEARPROOF_GKR_DERIVE / NEARPROOF_GRUEN_ZC / NEARPROOF_NEXT_MASK = 1
//   NEARPROOF_MAX_DEGREE=<d>     max constraint degree in the params (default 8; SHA AIR needs 4)
//   NEARPROOF_NEGATIVE=1         run lever negative tests after proving
use std::sync::Arc;
use openvm_stark_backend::{StarkEngine,SystemParams,AirRef,prover::{CpuColMajorBackend,AirProvingContext,ProvingContext},test_utils::{TestFixture,test_system_params_small}};
use p3_field::PrimeCharacteristicRing;
mod config {use super::*;include!("native_sha384_levers_config.rs");include!("native_digest_dictionary.rs");
    fn setting(name:&str,default:usize)->usize {std::env::var(name).map(|s|s.parse().unwrap()).unwrap_or(default)}
    fn size<T:openvm_stark_backend::codec::Encode>(x:&T)->usize {let mut b=Vec::new();x.encode(&mut b).unwrap();b.len()}
    fn census(proof:&openvm_stark_backend::proof::Proof<SC>,total:usize) {
        let w=&proof.whir_proof;
        let db=levers().digest_bytes;
        let mut digests=0usize;let mut per_round=Vec::new();
        for groups in [&w.initial_round_merkle_proofs,&w.codeword_merkle_proofs] {
            for queries in groups {let n:usize=queries.iter().map(|p|p.len()).sum();digests+=n;per_round.push(n);}
        }
        let base_values:usize=w.initial_round_opened_rows.iter().flat_map(|x|x.iter()).flat_map(|x|x.iter()).map(|x|x.len()).sum();
        let ext_values:usize=w.codeword_opened_values.iter().flat_map(|x|x.iter()).map(|x|x.len()).sum();
        let whir=size(w);
        let (auth,initial,codeword,final_poly)=(digests*db,base_values*4,ext_values*48,w.final_poly.len()*48);
        let lv=proof.whir_proof.levers;
        let gkr=if lv.is_default() {size(&proof.gkr_proof)} else {let mut b=Vec::new();proof.gkr_proof.encode_levers(&lv,&mut b).unwrap();b.len()};
        let rel=if lv.is_default() {size(&proof.batch_constraint_proof)} else {let mut b=Vec::new();proof.batch_constraint_proof.encode_levers(&mut b).unwrap();b.len()};
        let stack=size(&proof.stacking_proof);
        let openings:usize=proof.batch_constraint_proof.column_openings.iter().flat_map(|a|a.iter()).map(|p|p.len()).sum();
        println!("LEVERS_CENSUS total={} auth={} auth_digests={} auth_per_tree={:?} initial={} codeword={} final_poly={} whir_small={} whir={} relations={} column_openings_ef={} gkr={} stacking={} stacking_openings_ef={} other={}",
            total,auth,digests,per_round,initial,codeword,final_poly,whir-auth-initial-codeword-final_poly,whir,rel,openings,gkr,stack,
            proof.stacking_proof.stacking_openings.iter().map(|v|v.len()).sum::<usize>(),total-whir-rel-gkr-stack);
    }
    pub(super) fn run() {
        use openvm_stark_backend::{codec::{Encode,Decode},proof::Proof,soundness::SoundnessCalculator,WhirLevers};
        set_sha_levers(ShaLevers{digest_bytes:setting("NEARPROOF_DIGEST_BYTES",48),coset_leaf:setting("NEARPROOF_COSET_LEAF",0)==1});
        if std::env::var_os("NEARPROOF_TRANSCRIPT_VECTORS").is_some() {transcript_vectors();return;}
        if let Ok(spec)=std::env::var("NEARPROOF_GRIND_BENCH") {
            // "bits:trials,bits:trials,...": grind on independent transcript states; report mean.
            for item in spec.split(',') {
                let (b,n)=item.split_once(':').unwrap();
                let wide=b.starts_with('w');let b=b.trim_start_matches('w');
                let (b,n):(usize,usize)=(b.parse().unwrap(),n.parse().unwrap());
                GRIND_STATS.lock().unwrap().clear();
                let start=std::time::Instant::now();
                for i in 0..n {let mut t=Transcript::new();t.observe(F::from_u32(i as u32));t.observe(F::from_u32(b as u32));
                    let mk=||{let mut v=Transcript::new();v.observe(F::from_u32(i as u32));v.observe(F::from_u32(b as u32));v};
                    if wide {
                        let w=t.grind_wide(b);assert!(mk().check_witness_wide(b,w));
                        assert!(!mk().check_witness_wide(b,[w[0],w[1]+F::ONE]) || b<4,"wrong witness accepted");
                    } else {
                        let w=t.grind(b);assert!(mk().check_witness(b,w));
                        assert!(!mk().check_witness(b,w+F::ONE) || b<4,"wrong witness accepted");
                    }}
                let total=start.elapsed().as_secs_f64();
                let tries:u64=GRIND_STATS.lock().unwrap().iter().map(|x|x.2+1).sum();
                println!("LEVERS_GRIND_BENCH wide={} bits={} trials={} mean_seconds={:.4} attempts_per_second={:.3e} mean_attempts_log2={:.2} threads={}",
                    wide,b,n,total/n as f64,tries as f64/total,((tries as f64)/(n as f64)).log2(),openvm_stark_backend::p3_maybe_rayon::prelude::current_num_threads());
            }
            return;
        }
        let sha_air=setting("NEARPROOF_SHA_AIR",0);
        let dummy=setting("NEARPROOF_DUMMY",0)==1 || sha_air>0;
        let out=std::env::var("NEARPROOF_LITERAL_OUT").unwrap();
        let n_stack=setting("NEARPROOF_N_STACK",16);
        let k=setting("NEARPROOF_K",3);
        let blowup=setting("NEARPROOF_LOG_BLOWUP",5);
        assert!((8..=20).contains(&n_stack) && (1..=5).contains(&k) && (1..=12).contains(&blowup));
        assert!(2+n_stack+blowup<=27);
        let mut params=test_system_params_small(2,n_stack,k);
        let interaction_log=setting("NEARPROOF_INTERACTION_LOG",20);assert!((20..=28).contains(&interaction_log));
        params.max_constraint_degree=setting("NEARPROOF_MAX_DEGREE",8);params.logup.max_interaction_count=1<<interaction_log;
        params.logup.pow_bits=0;params.log_blowup=blowup;
        let all_list=setting("NEARPROOF_ALL_LIST",0);
        assert!(all_list<=1);
        let m=setting("NEARPROOF_LIST_M",3);
        if all_list==1 {params.whir.proximity=openvm_stark_backend::WhirProximityStrategy::ListDecoding {m};}
        let bits:usize=std::env::var("NEARPROOF_QUERY_BITS").unwrap_or("268".into()).parse().unwrap();
        let whir_levers=WhirLevers{k_first:setting("NEARPROOF_K1",0),multiproof:setting("NEARPROOF_MULTIPROOF",0)==1,
            keep_domain:setting("NEARPROOF_KEEP_DOMAIN",0)==1,
            gruen_gkr:setting("NEARPROOF_GRUEN_GKR",0)==1,gkr_derive_claims:setting("NEARPROOF_GKR_DERIVE",0)==1,
            next_mask:setting("NEARPROOF_NEXT_MASK",0)==1,gruen_zerocheck:setting("NEARPROOF_GRUEN_ZC",0)==1,
            wide_query_pow:setting("NEARPROOF_WIDE_POW",0)==1};
        let sha=levers();
        let log_final=setting("NEARPROOF_LOG_FINAL",params.log_final_poly_len());
        let (qpow,fpow,mpow)=(setting("NEARPROOF_QUERY_POW",0),setting("NEARPROOF_FOLDING_POW",0),setting("NEARPROOF_MU_POW",0));
        params.whir=openvm_stark_backend::WhirConfig::new_with_levers(params.log_blowup,params.l_skip+params.n_stack,
            openvm_stark_backend::WhirParams {k:params.whir.k,log_final_poly_len:log_final,
                proximity:params.whir.proximity,query_phase_pow_bits:qpow,folding_pow_bits:fpow,mu_pow_bits:mpow},bits,whir_levers);
        println!("NATIVE_SHA384_PROFILE n_stack={} k={} log_blowup={} all_list={} queries={:?}",n_stack,k,blowup,all_list,params.whir.rounds.iter().map(|r|r.num_queries).collect::<Vec<_>>());
        println!("NATIVE_SHA384_INTERACTION_LOG {}",interaction_log);
        println!("LEVERS_PROFILE_GKR gruen={} derive={} next_mask={} gruen_zc={} max_degree={}",whir_levers.gruen_gkr,whir_levers.gkr_derive_claims,whir_levers.next_mask,whir_levers.gruen_zerocheck,params.max_constraint_degree);
        println!("LEVERS_PROFILE k1={} log_final={} multiproof={} keep_domain={} m={} query_pow={} folding_pow={} mu_pow={} digest_bytes={} coset_leaf={} dummy={}",
            params.whir.k_first(),params.log_final_poly_len(),whir_levers.multiproof,whir_levers.keep_domain,m,qpow,fpow,mpow,
            sha.digest_bytes,sha.coset_leaf,dummy);
        let engine=Engine::new(params);
        let keygen_start=std::time::Instant::now();
        let (pk,vk)=if sha_air>0 {shaair::ShaFixture(sha_air).keygen(&engine)} else if dummy {dummy::DummyFixture.keygen(&engine)} else {literal::LiteralFixture.keygen(&engine)};
        println!("NATIVE_SHA384_KEYGEN_SECONDS {}",keygen_start.elapsed().as_secs_f64());
        for (i,a) in vk.inner.per_air.iter().enumerate() {
            let m=a.params.opening_masks();
            println!("LEVERS_ROT_MASK air={} widths={:?} need_rot={} rotated_per_part={:?}",i,a.params.opening_part_widths(),a.params.need_rot,
                m.iter().map(|p|p.iter().filter(|&&b|b).count()).collect::<Vec<_>>());
        }
        let bound=SoundnessCalculator::calculate_from_vk(&vk);
        println!("NATIVE_SHA384_EXT12 target={} min={} logup={} proximity={} query={}",bits,bound.total_bits,bound.logup_bits,bound.whir_details.proximity_gaps_bits,bound.whir_details.query_bits);
        if setting("NEARPROOF_ALLOW_BELOW_TARGET",0)==0 {
            assert!(bound.total_bits>=bits as f64,"native component budget failed; do not prove this profile");
        } else if bound.total_bits<bits as f64 {println!("LEVERS_WARNING calculator below target (measurement only)");}
        let expected:Vec<F>=if dummy {vec![]} else {std::fs::read(format!("{out}/public.bin")).unwrap().chunks_exact(4)
            .map(|b|F::from_u32(u32::from_le_bytes(b.try_into().unwrap()))).collect()};
        let verify_counted=|proof:&Proof<SC>|->bool {
            let before=hash_counts();
            let ok=engine.verify(&vk,proof).is_ok();
            let after=hash_counts();
            let calls:[u64;NTAGS]=std::array::from_fn(|i|after.0[i]-before.0[i]);
            let blocks:[u64;NTAGS]=std::array::from_fn(|i|after.1[i]-before.1[i]);
            println!("NATIVE_SHA384_VERIFY_CALLS {:?}",calls);
            println!("NATIVE_SHA384_VERIFY_BLOCKS {:?} total={}",blocks,blocks.iter().sum::<u64>());
            ok
        };
        if std::env::var_os("NEARPROOF_REPLAY").is_some() {
            let bytes=std::fs::read(format!("{out}/child.proof")).unwrap();
            let mut cursor=std::io::Cursor::new(&bytes);
            let proof=Proof::<SC>::decode(&mut cursor).unwrap();
            assert_eq!(cursor.position() as usize,bytes.len());
            if !dummy {assert_eq!(proof.public_values[0],expected);}
            census(&proof,bytes.len());
            let trace_path=std::env::var("NEARPROOF_MERKLE_TRACE").ok();
            if trace_path.is_some() {MERKLE_TRACE.lock().unwrap().clear();MERKLE_TRACE_ON.store(true,std::sync::atomic::Ordering::Relaxed);}
            assert!(verify_counted(&proof));
            if let Some(path)=trace_path {MERKLE_TRACE_ON.store(false,std::sync::atomic::Ordering::Relaxed);
                std::fs::write(path,&*MERKLE_TRACE.lock().unwrap()).unwrap();}
            println!("NATIVE_SHA384_EXT12_REPLAY_PASS bytes={}",bytes.len());return;
        }
        let prove_start=std::time::Instant::now();
        let proof=if sha_air>0 {shaair::ShaFixture(sha_air).prove(&engine,&pk)} else if dummy {dummy::DummyFixture.prove(&engine,&pk)} else {literal::LiteralFixture.prove(&engine,&pk)};
        println!("NATIVE_SHA384_PROVE_SECONDS {}",prove_start.elapsed().as_secs_f64());
        for (b,secs,w) in GRIND_STATS.lock().unwrap().iter() {println!("LEVERS_GRIND bits={} seconds={:.4} witness={}",b,secs,w);}
        let verify_start=std::time::Instant::now();
        engine.verify(&vk,&proof).unwrap();
        println!("NATIVE_SHA384_VERIFY_SECONDS {}",verify_start.elapsed().as_secs_f64());
        if !dummy {assert_eq!(proof.public_values[0],expected);}
        let mut bytes=Vec::new();proof.encode(&mut bytes).unwrap();
        // The verifier must accept the decoded wire form, not just the in-memory proof.
        let decoded=Proof::<SC>::decode(&mut std::io::Cursor::new(&bytes)).unwrap();
        assert!(decoded==proof,"codec round trip");
        assert!(verify_counted(&decoded));
        std::fs::write(format!("{out}/child.proof"),&bytes).unwrap();
        println!("NATIVE_SHA384_EXT12_BYTES total={} gkr_upstream_enc={} relations={} stacking={} whir={}",bytes.len(),size(&proof.gkr_proof),size(&proof.batch_constraint_proof),size(&proof.stacking_proof),size(&proof.whir_proof));
        census(&proof,bytes.len());
        if !dummy {
            for index in [43,44,45,46,50,72] {
                let mut bad=proof.clone();bad.public_values[0][index]+=F::ONE;
                assert!(engine.verify(&vk,&bad).is_err());
            }
            println!("NATIVE_SHA384_EXT12_PASS public_mutations_rejected=6");
        }
        if setting("NEARPROOF_NEGATIVE",0)==1 {negative(&engine,&vk,&proof);}
    }
    /// Lever negative tests: each mutation must be rejected by the verifier.
    fn negative(engine:&Engine,vk:&openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<SC>,proof:&openvm_stark_backend::proof::Proof<SC>) {
        use openvm_stark_backend::codec::Encode;
        let p=&engine.config().params;
        let mut cases:Vec<(&str,openvm_stark_backend::proof::Proof<SC>)>=Vec::new();
        let flip=|d:&mut Digest|{d[0]^=1;};
        let mut bad=proof.clone();bad.whir_proof.initial_round_opened_rows[0][0][0][0]+=F::ONE;cases.push(("initial leaf value",bad));
        if !proof.whir_proof.codeword_opened_values.is_empty() {
            let mut bad=proof.clone();let last=bad.whir_proof.codeword_opened_values[0][0].len()-1;
            bad.whir_proof.codeword_opened_values[0][0][last]+=F::ONE;cases.push(("codeword leaf value (last coset element)",bad));
        }
        { let mut bad=proof.clone();let pth=&mut bad.whir_proof.initial_round_merkle_proofs[0][0];let n=pth.len();flip(&mut pth[n-1]);cases.push(("initial auth digest",bad)); }
        if !proof.whir_proof.codeword_merkle_proofs.is_empty() {
            let mut bad=proof.clone();flip(&mut bad.whir_proof.codeword_merkle_proofs[0][0][0]);cases.push(("codeword auth digest",bad));
        }
        if p.whir.levers.multiproof {
            let mut bad=proof.clone();bad.whir_proof.initial_round_merkle_proofs[0][0].pop();cases.push(("multiproof: sibling removed",bad));
            let mut bad=proof.clone();let d=bad.whir_proof.initial_round_merkle_proofs[0][0][0];bad.whir_proof.initial_round_merkle_proofs[0][0].push(d);cases.push(("multiproof: sibling appended",bad));
            let mut bad=proof.clone();bad.whir_proof.initial_round_merkle_proofs[0][0].swap(0,1);cases.push(("multiproof: siblings reordered",bad));
        }
        if levers().digest_bytes<48 {
            // Bytes beyond the digest width are not part of the digest: a proof whose digests
            // carry garbage there must still encode identically (the codec drops them).
            let mut odd=proof.clone();odd.whir_proof.initial_round_merkle_proofs[0][0][0][5]^=0xffff_0000_0000_0000;
            let (mut a,mut b)=(Vec::new(),Vec::new());proof.encode(&mut a).unwrap();odd.encode(&mut b).unwrap();
            assert_eq!(a,b,"truncated digests must not encode the dropped bytes");
            println!("LEVERS_NEGATIVE ok=encoding-ignores-truncated-tail");
        }
        if p.whir.query_phase_pow_bits>0 {
            let mut bad=proof.clone();bad.whir_proof.query_phase_pow_witnesses[0]+=F::ONE;cases.push(("query PoW witness",bad));
            let mut bad=proof.clone();let n=bad.whir_proof.query_phase_pow_witnesses.len();bad.whir_proof.query_phase_pow_witnesses[n-1]+=F::ONE;cases.push(("last-round query PoW witness",bad));
            if p.whir.levers.wide_query_pow {
                let mut bad=proof.clone();bad.whir_proof.query_phase_pow_witnesses[0]+=F::ONE;cases.push(("wide PoW: first element",bad));
                let mut bad=proof.clone();bad.whir_proof.query_phase_pow_witnesses.pop();cases.push(("wide PoW: element missing",bad));
            }
        }
        if p.whir.folding_pow_bits>0 {let mut bad=proof.clone();bad.whir_proof.folding_pow_witnesses[0]+=F::ONE;cases.push(("folding PoW witness",bad));}
        if p.whir.mu_pow_bits>0 {let mut bad=proof.clone();bad.whir_proof.mu_pow_witness+=F::ONE;cases.push(("mu PoW witness",bad));}
        { let mut bad=proof.clone();bad.whir_proof.levers.keep_domain=!bad.whir_proof.levers.keep_domain;cases.push(("levers field mismatch",bad)); }
        let g=&proof.gkr_proof;
        if g.claims_per_layer.len()>2 {
            let mut bad=proof.clone();bad.gkr_proof.sumcheck_polys[1][0][0]+=EF::ONE;cases.push(("GKR sumcheck s(1)",bad));
            let mut bad=proof.clone();bad.gkr_proof.sumcheck_polys[1][1][1]+=EF::ONE;cases.push(("GKR sumcheck s(2)",bad));
            let mut bad=proof.clone();bad.gkr_proof.claims_per_layer[2].q_xi_1+=EF::ONE;cases.push(("GKR layer claim q_xi_1",bad));
            let mut bad=proof.clone();bad.gkr_proof.claims_per_layer[0].p_xi_0+=EF::ONE;cases.push(("GKR root claim p_xi_0",bad));
            let last=g.claims_per_layer.len()-1;
            let mut bad=proof.clone();bad.gkr_proof.claims_per_layer[last].q_xi_0+=EF::ONE;cases.push(("GKR last layer claim q_xi_0",bad));
            if p.whir.levers.gruen_gkr {
                let mut bad=proof.clone();bad.gkr_proof.sumcheck_polys[1][0][2]=EF::ONE;cases.push(("GKR gruen: dropped s(3) set",bad));
            }
            if p.whir.levers.gkr_derive_claims {
                let mut bad=proof.clone();bad.gkr_proof.claims_per_layer[1].p_xi_1=EF::ONE;cases.push(("GKR derive: p_xi_1 set",bad));
                let mut bad=proof.clone();bad.gkr_proof.q0_claim=EF::ONE;cases.push(("GKR derive: q0_claim set",bad));
            }
        }
        if !proof.batch_constraint_proof.sumcheck_round_polys.is_empty() {
            let mut bad=proof.clone();bad.batch_constraint_proof.sumcheck_round_polys[0][0]+=EF::ONE;cases.push(("batch sumcheck eval",bad));
            if p.whir.levers.gruen_zerocheck {
                let mut bad=proof.clone();*bad.batch_constraint_proof.sumcheck_round_polys[0].last_mut().unwrap()=EF::ONE;cases.push(("batch gruen: dropped eval set",bad));
            }
        }
        if p.whir.levers.next_mask {
            // A verifying key whose mask drops one column that the constraints read at the next
            // row, with the proof's rotated claim for it removed: must be rejected.
            let air=0;let masks=vk.inner.per_air[air].params.opening_masks();
            if let Some(col)=masks[0].iter().position(|&b|b) {
                let mut vk2=vk.clone();let mut m2=masks.clone();m2[0][col]=false;
                vk2.inner.per_air[air].params.rot_mask=Some(m2);
                let mut bad=proof.clone();
                let pos=masks[0][..col].iter().map(|&b|1+b as usize).sum::<usize>()+1;
                bad.batch_constraint_proof.column_openings[0][0].remove(pos);
                let rejected=engine.verify(&vk2,&bad).is_err();
                println!("LEVERS_NEGATIVE case=\"next_mask: vk drops a rotated column\" rejected={}",rejected);
                assert!(rejected);
                let mut bad=proof.clone();bad.batch_constraint_proof.column_openings[0][0].remove(pos);
                let rejected=engine.verify(vk,&bad).is_err();
                println!("LEVERS_NEGATIVE case=\"next_mask: rotated claim removed\" rejected={}",rejected);
                assert!(rejected);
                let mut bad=proof.clone();bad.batch_constraint_proof.column_openings[0][0][pos]+=EF::ONE;cases.push(("next_mask: rotated claim value",bad));
            }
        }
        let n=cases.len();
        for (name,bad) in cases {
            let rejected=engine.verify(vk,&bad).is_err();
            println!("LEVERS_NEGATIVE case={:?} rejected={}",name,rejected);
            assert!(rejected,"negative case accepted: {name}");
        }
        println!("LEVERS_NEGATIVE_PASS cases={}",n);
    }
    mod literal {include!("literal.rs");}
    mod shaair {
        //! The L3 SHA-512/384 compression AIR, unmodified (crate::air, crate::trace).
        use super::*;
        use crate::air::{Sha512Air,TableAir,HarnessAir,WIDTH,T_WIDTH,H_WIDTH};
        use crate::trace::{gen_all,Rng,Comp};
        use p3_matrix::dense::RowMajorMatrix;
        use openvm_stark_backend::prover::ColMajorMatrix;
        pub(super) struct ShaFixture(pub usize);
        impl TestFixture<SC> for ShaFixture {
            fn airs(&self)->Vec<AirRef<SC>> {vec![Arc::new(Sha512Air),Arc::new(TableAir),Arc::new(HarnessAir)]}
            fn generate_proving_ctx(&self)->ProvingContext<CpuColMajorBackend<SC>> {
                let n=self.0;
                let mut rng=Rng(0xdead_beef_cafe_f00d ^ n as u64);
                let comps:Vec<Comp>=(0..n).map(|_|rng.comp()).collect();
                let t=gen_all(&comps);
                println!("LEVERS_SHA_AIR n={} main_height={} main_cells={}",n,t.main_height,t.main_height*WIDTH);
                let f=|v:&[u32]|v.iter().map(|&x|F::from_u32(x)).collect::<Vec<F>>();
                let m=|v:&[u32],w|ColMajorMatrix::from_row_major(&RowMajorMatrix::new(f(v),w));
                ProvingContext::new(vec![
                    (0,AirProvingContext::simple(m(&t.main,WIDTH),vec![])),
                    (1,AirProvingContext::simple(m(&t.table,T_WIDTH),vec![])),
                    (2,AirProvingContext::simple(m(&t.harness,H_WIDTH),vec![])),
                ])
            }
        }
    }
    mod dummy {
        //! Shape-equivalent dummy AIR: NEARPROOF_DUMMY_COLS columns x 2^NEARPROOF_DUMMY_LOG_HEIGHT rows,
        //! degree-2 transition constraint per column (uses the next row, as a SHA round AIR does),
        //! and one balanced LogUp bus (send + receive of (c0, c1) on every row).
        use super::*;
        use p3_air::{Air,AirBuilder,BaseAir,BaseAirWithPublicValues};
        use p3_matrix::{Matrix,dense::RowMajorMatrix};
        use openvm_stark_backend::{PartitionedBaseAir,interaction::InteractionBuilder,prover::ColMajorMatrix};
        fn cols()->usize {super::setting("NEARPROOF_DUMMY_COLS",460)}
        fn log_height()->usize {super::setting("NEARPROOF_DUMMY_LOG_HEIGHT",14)}
        pub(super) struct DummyAir {width:usize}
        impl<T> BaseAir<T> for DummyAir {fn width(&self)->usize {self.width}}
        impl<T> PartitionedBaseAir<T> for DummyAir {}
        impl<T> BaseAirWithPublicValues<T> for DummyAir {}
        impl<AB:AirBuilder+InteractionBuilder> Air<AB> for DummyAir {
            fn eval(&self,builder:&mut AB) {
                let main=builder.main();
                let local:Vec<AB::Expr>=main.row_slice(0).unwrap().iter().map(|v|(*v).into()).collect();
                let next:Vec<AB::Expr>=main.row_slice(1).unwrap().iter().map(|v|(*v).into()).collect();
                let n=self.width;
                for c in 0..n {
                    let rhs=local[c].clone()*local[(c+1)%n].clone()+local[(c+2)%n].clone()+AB::Expr::from(AB::F::from_u32(c as u32+1));
                    builder.when_transition().assert_eq(next[c].clone(),rhs);
                }
                builder.push_interaction(0,vec![local[0].clone(),local[1].clone()],AB::Expr::ONE,1);
                builder.push_interaction(0,vec![local[0].clone(),local[1].clone()],-AB::Expr::ONE,1);
            }
        }
        pub(super) struct DummyFixture;
        impl TestFixture<SC> for DummyFixture {
            fn airs(&self)->Vec<AirRef<SC>> {vec![Arc::new(DummyAir{width:cols()})]}
            fn generate_proving_ctx(&self)->ProvingContext<CpuColMajorBackend<SC>> {
                let (n,h)=(cols(),1usize<<log_height());
                let mut v=vec![F::ZERO;n*h];
                for c in 0..n {v[c]=F::from_u32((c as u32).wrapping_mul(2654435761)%2013265921);}
                for r in 1..h {
                    let (prev,cur)=v.split_at_mut(r*n);let prev=&prev[(r-1)*n..];
                    for c in 0..n {cur[c]=prev[c]*prev[(c+1)%n]+prev[(c+2)%n]+F::from_u32(c as u32+1);}
                }
                ProvingContext::new(vec![(0,AirProvingContext::simple(ColMajorMatrix::from_row_major(&RowMajorMatrix::new(v,n)),vec![]))])
            }
        }
    }
}
#[allow(dead_code, clippy::all)]
#[path = "sha384_air.rs"]
mod air;
#[allow(dead_code, clippy::all)]
#[path = "sha384_trace.rs"]
mod trace;
fn main(){config::run();}
