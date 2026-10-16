#![feature(allocator_api)]
//! WHIR opening proof experiment; no GKR constraint proof or security claim.
use field::{baby_bear::{base::BabyBearField as F,ext4::BabyBearExt4 as E},Field,FieldExtension,PrimeField};
use prover::{allocation_pool::default_pool_for,gkr::{prover::{backend::NaiveBackend,NaiveGKRBackend,SetupCommitment,WhirSchedule,stages::commitment_utils::commit_trace_part},sumcheck::access_and_fold::{GKRStorage,GKRLayerSource,BaseFieldPoly},whir::{whir_fold,evaluate_multivariate,WhirIntermediateOracleMode}},merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap};
use cs::definitions::GKRAddress;
use transcript::{Blake2sTranscript,Transcript};
use serde_json::{json,Value};
use worker::Worker;
type Tree=Blake2sU32MerkleTreeWithCap<std::alloc::Global,false>;
type TR=Blake2sTranscript<false>;
fn main(){
 let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),4);
 let input:Value=serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
 let rows:Vec<Vec<u32>>=serde_json::from_value(input["rows"].clone()).unwrap();
 assert_eq!(rows.len(),8);assert!(rows.iter().all(|r|r.len()==104));
 let columns:Vec<Vec<F>>=(0..104).map(|c|rows.iter().map(|r|{assert!(r[c]<F::CHARACTERISTICS_U32);F::from_u32_unchecked(r[c])}).collect()).collect();
 let refs:Vec<_>=columns.iter().map(|c|c.as_slice()).collect();
 let worker=Worker::new_with_num_threads(2);let tw=fft::Twiddles::<F,std::alloc::Global>::new(8,&worker);
 let pool=default_pool_for::<F,E>();
 let witness=commit_trace_part::<F,E,Tree,_>(&NaiveBackend,&refs,&tw,4,1,1,3,pool.as_ref(),&worker);
 let memory=commit_trace_part::<F,E,Tree,_>(&NaiveBackend,&[],&tw,4,1,1,3,pool.as_ref(),&worker);
 let setup=SetupCommitment::InMemory(commit_trace_part::<F,E,Tree,_>(&NaiveBackend,&[],&tw,4,1,1,3,pool.as_ref(),&worker));
 // Prover-only handoff. The independent verifier derives this from sumcheck.
 let handoff:Value=serde_json::from_slice(&std::fs::read(&args[3]).unwrap()).unwrap();
 let statement:Vec<u32>=serde_json::from_value(handoff["statement_words"].clone()).unwrap();
 let expected_cap:Vec<u32>=serde_json::from_value(handoff["root"].clone()).unwrap();
 assert_eq!(witness.get_cap().cap[0].to_vec(),expected_cap);
 let seed_words:[u32;8]=serde_json::from_value(handoff["pre_opening_seed"].clone()).unwrap();
 let mut seed=transcript::Seed(seed_words);
 let point:Vec<E>=serde_json::from_value(handoff["evaluation_point"].clone()).unwrap();
 assert_eq!(point.len(),3);
 let claims:Vec<E>=columns.iter().map(|c|evaluate_multivariate(&c.iter().map(|v|E::from_base(*v)).collect::<Vec<_>>(),&point,&worker)).collect();
 <TR as Transcript<F,E>>::commit_extension_field_elements(&mut seed,&claims);
 let mut batch=[E::ZERO];<TR as Transcript<F,E>>::draw_fresh_random_field_elements(&mut seed,&mut batch);
 let initial_seed=seed;
 let mut layer=GKRLayerSource::<F,E>::default();
 for (i,c) in columns.into_iter().enumerate(){layer.base_field_inputs.insert(GKRAddress::BaseLayerWitness(i),BaseFieldPoly::new(c.into_boxed_slice()));}
 let storage=GKRStorage{layers:vec![layer]};
 let schedule=WhirSchedule{base_lde_factor:4,cap_size:1,whir_steps_schedule:vec![1,1],whir_queries_schedule:vec![8,8],whir_steps_lde_factors:vec![4],whir_pow_schedule:vec![0,0]};
 let proof=whir_fold::<F,E,Tree,TR,_,_>(memory,vec![],witness,claims,&setup,vec![],storage,0,point.clone(),batch[0],&schedule,&tw,seed,1,3,&NaiveBackend,&NaiveGKRBackend,WhirIntermediateOracleMode::Monolithic,pool.as_ref(),&worker);
 let binary=bincode::serialize(&proof).unwrap();
 let out=json!({"experiment":"direct-Wasm constraint-sumcheck WHIR opening generation","statement_words":statement,"initial_whir_seed":initial_seed.0,"evaluation_point":point,"proof":proof,"bincode_bytes":binary.len(),"verified":false,"security_bits_claimed":null,"limitations":["Toy 8-row schedule; no security claim.","No independent WHIR verifier run yet.","No GKR constraint proof, recursion or full NEAR transition."]});
 std::fs::write(&args[2],serde_json::to_string_pretty(&out).unwrap()+"\n").unwrap();
 std::fs::write(format!("{}.bin",args[2]),binary).unwrap();
 println!("Fresh WHIR opening generated; verification still required");
}
