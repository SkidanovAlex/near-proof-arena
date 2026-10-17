use std::sync::Arc;
use openvm_stark_backend::{StarkEngine,SystemParams,AirRef,prover::{CpuColMajorBackend,AirProvingContext,ProvingContext},test_utils::{TestFixture,test_system_params_small}};
use p3_field::PrimeCharacteristicRing;
mod config {use super::*;include!("native_sha384_config.rs");include!("native_digest_dictionary.rs");
    pub(super) fn run() {
        use openvm_stark_backend::{codec::{Encode,Decode},proof::Proof,soundness::SoundnessCalculator};
        if std::env::var_os("NEARPROOF_TRANSCRIPT_VECTORS").is_some() {transcript_vectors();return;}
        let out=std::env::var("NEARPROOF_LITERAL_OUT").unwrap();
        fn setting(name:&str,default:usize)->usize {std::env::var(name).map(|s|s.parse().unwrap()).unwrap_or(default)}
        let n_stack=setting("NEARPROOF_N_STACK",16);
        let k=setting("NEARPROOF_K",3);
        let blowup=setting("NEARPROOF_LOG_BLOWUP",5);
        assert!((8..=20).contains(&n_stack) && (1..=5).contains(&k) && (1..=8).contains(&blowup));
        assert!(2+n_stack+blowup<=27);
        let mut params=test_system_params_small(2,n_stack,k);
        let interaction_log=setting("NEARPROOF_INTERACTION_LOG",20);assert!((20..=28).contains(&interaction_log));
        params.max_constraint_degree=8;params.logup.max_interaction_count=1<<interaction_log;
        params.logup.pow_bits=0;params.log_blowup=blowup;
        let all_list=setting("NEARPROOF_ALL_LIST",0);
        assert!(all_list<=1);
        if all_list==1 {params.whir.proximity=openvm_stark_backend::WhirProximityStrategy::ListDecoding {m:3};}
        let bits:usize=std::env::var("NEARPROOF_QUERY_BITS").unwrap_or("268".into()).parse().unwrap();
        params.whir=openvm_stark_backend::WhirConfig::new(params.log_blowup,params.l_skip+params.n_stack,
            openvm_stark_backend::WhirParams {k:params.whir.k,log_final_poly_len:params.log_final_poly_len(),
                proximity:params.whir.proximity,query_phase_pow_bits:0,folding_pow_bits:0,mu_pow_bits:0},bits);
        println!("NATIVE_SHA384_PROFILE n_stack={} k={} log_blowup={} all_list={} queries={:?}",n_stack,k,blowup,all_list,params.whir.rounds.iter().map(|r|r.num_queries).collect::<Vec<_>>());
        println!("NATIVE_SHA384_INTERACTION_LOG {}",interaction_log);
        let engine=Engine::new(params);
        let fx=literal::LiteralFixture;
        let (pk,vk)=fx.keygen(&engine);
        let bound=SoundnessCalculator::calculate_from_vk(&vk);
        println!("NATIVE_SHA384_EXT12 target={} min={} logup={} proximity={} query={}",bits,bound.total_bits,bound.logup_bits,bound.whir_details.proximity_gaps_bits,bound.whir_details.query_bits);
        assert!(bound.total_bits>=bits as f64,"native component budget failed; do not prove this profile");
        let expected:Vec<F>=std::fs::read(format!("{out}/public.bin")).unwrap().chunks_exact(4)
            .map(|b|F::from_u32(u32::from_le_bytes(b.try_into().unwrap()))).collect();
        if std::env::var_os("NEARPROOF_REPLAY").is_some() {
            let bytes=if let Ok(path)=std::env::var("NEARPROOF_DICTIONARY") {
                let wire=std::fs::read(path).unwrap();
                let native=decode_digest_dictionary(&wire).expect("invalid dictionary stream");
                println!("NATIVE_DICTIONARY_DECODE wire={} native={}",wire.len(),native.len());
                native
            } else {std::fs::read(format!("{out}/child.proof")).unwrap()};
            let mut cursor=std::io::Cursor::new(&bytes);
            let proof=Proof::<SC>::decode(&mut cursor).unwrap();
            assert_eq!(cursor.position() as usize,bytes.len());
            assert_eq!(proof.public_values[0],expected);
            if std::env::var_os("NEARPROOF_WHIR_CENSUS").is_some() {
                let w=&proof.whir_proof;
                let mut digests=Vec::new();
                for groups in [&w.initial_round_merkle_proofs,&w.codeword_merkle_proofs] {
                    for queries in groups {for path in queries {for d in path {digests.extend(digest_bytes(*d));}}}
                }
                let unique:std::collections::BTreeSet<_>=digests.chunks_exact(48).collect();
                let base_values:usize=w.initial_round_opened_rows.iter().flat_map(|x|x.iter()).flat_map(|x|x.iter()).map(|x|x.len()).sum();
                let ext_values:usize=w.codeword_opened_values.iter().flat_map(|x|x.iter()).map(|x|x.len()).sum();
                println!("WHIR_CENSUS auth_bytes={} auth_digests={} unique_auth_digests={} initial_values_bytes={} codeword_values_bytes={}",
                    digests.len(),digests.len()/48,unique.len(),base_values*4,ext_values*48);
                std::fs::write(format!("{out}/auth-digests.bin"),&digests).unwrap();
            }
            let trace_path=std::env::var("NEARPROOF_MERKLE_TRACE").ok();
            if trace_path.is_some() {MERKLE_TRACE.lock().unwrap().clear();MERKLE_TRACE_ON.store(true,std::sync::atomic::Ordering::Relaxed);}
            let before=hash_counts();
            engine.verify(&vk,&proof).unwrap();
            let after=hash_counts();
            if let Some(path)=trace_path {MERKLE_TRACE_ON.store(false,std::sync::atomic::Ordering::Relaxed);
                std::fs::write(path,&*MERKLE_TRACE.lock().unwrap()).unwrap();}
            let calls:[u64;6]=std::array::from_fn(|i|after.0[i]-before.0[i]);
            let blocks:[u64;6]=std::array::from_fn(|i|after.1[i]-before.1[i]);
            println!("NATIVE_SHA384_VERIFY_CALLS {:?}",calls);
            println!("NATIVE_SHA384_VERIFY_BLOCKS {:?}",blocks);
            println!("NATIVE_SHA384_EXT12_REPLAY_PASS bytes={}",bytes.len());return;
        }
        let proof=fx.prove(&engine,&pk);
        engine.verify(&vk,&proof).unwrap();assert_eq!(proof.public_values[0],expected);
        fn size<T:Encode>(x:&T)->usize {let mut b=Vec::new();x.encode(&mut b).unwrap();b.len()}
        let mut bytes=Vec::new();proof.encode(&mut bytes).unwrap();
        std::fs::write(format!("{out}/child.proof"),&bytes).unwrap();
        println!("NATIVE_SHA384_EXT12_BYTES total={} gkr={} relations={} stacking={} whir={}",bytes.len(),size(&proof.gkr_proof),size(&proof.batch_constraint_proof),size(&proof.stacking_proof),size(&proof.whir_proof));
        for index in [43,44,45,46,50,72] {
            let mut bad=proof.clone();bad.public_values[0][index]+=F::ONE;
            assert!(engine.verify(&vk,&bad).is_err());
        }
        println!("NATIVE_SHA384_EXT12_PASS public_mutations_rejected=6");
    }
    mod literal {include!("literal.rs");}
}
fn main(){config::run();}
