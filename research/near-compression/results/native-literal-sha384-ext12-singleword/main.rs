use std::sync::Arc;
use openvm_stark_backend::{StarkEngine,SystemParams,AirRef,prover::{CpuColMajorBackend,AirProvingContext,ProvingContext},test_utils::{TestFixture,test_system_params_small}};
use p3_field::PrimeCharacteristicRing;
mod config {use super::*;include!("native_sha384_config.rs");
    pub(super) fn run() {
        use openvm_stark_backend::{codec::{Encode,Decode},proof::Proof,soundness::SoundnessCalculator};
        if std::env::var_os("NEARPROOF_TRANSCRIPT_VECTORS").is_some() {transcript_vectors();return;}
        let out=std::env::var("NEARPROOF_LITERAL_OUT").unwrap();
        let mut params=test_system_params_small(2,16,3);
        params.max_constraint_degree=8;params.logup.max_interaction_count=1<<20;
        params.logup.pow_bits=0;params.log_blowup=5;
        let bits:usize=std::env::var("NEARPROOF_QUERY_BITS").unwrap_or("268".into()).parse().unwrap();
        params.whir=openvm_stark_backend::WhirConfig::new(params.log_blowup,params.l_skip+params.n_stack,
            openvm_stark_backend::WhirParams {k:params.whir.k,log_final_poly_len:params.log_final_poly_len(),
                proximity:params.whir.proximity,query_phase_pow_bits:0,folding_pow_bits:0,mu_pow_bits:0},bits);
        let engine=Engine::new(params);
        let fx=literal::LiteralFixture;
        let (pk,vk)=fx.keygen(&engine);
        let bound=SoundnessCalculator::calculate_from_vk(&vk);
        println!("NATIVE_SHA384_EXT12 target={} min={} logup={} proximity={} query={}",bits,bound.total_bits,bound.logup_bits,bound.whir_details.proximity_gaps_bits,bound.whir_details.query_bits);
        let expected:Vec<F>=std::fs::read(format!("{out}/public.bin")).unwrap().chunks_exact(4)
            .map(|b|F::from_u32(u32::from_le_bytes(b.try_into().unwrap()))).collect();
        if std::env::var_os("NEARPROOF_REPLAY").is_some() {
            let bytes=std::fs::read(format!("{out}/child.proof")).unwrap();
            let mut cursor=std::io::Cursor::new(&bytes);
            let proof=Proof::<SC>::decode(&mut cursor).unwrap();
            assert_eq!(cursor.position() as usize,bytes.len());
            assert_eq!(proof.public_values[0],expected);
            engine.verify(&vk,&proof).unwrap();
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
