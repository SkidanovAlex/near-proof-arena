#![feature(allocator_api)]
//! Standalone full-round BLAKE2s RS commitment to direct Wasm AIR columns.
//! Exports all openings for independent checking, not a WHIR proximity proof.
use field::{baby_bear::{base::BabyBearField as F,ext4::BabyBearExt4 as E},PrimeField};
use prover::{allocation_pool::default_pool_for,gkr::{prover::{backend::NaiveBackend,stages::commitment_utils::commit_trace_part},whir::ColumnMajorBaseOracleForLDE},merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap};
use serde_json::{json,Value};
use worker::Worker;
type Tree=Blake2sU32MerkleTreeWithCap<std::alloc::Global,false>;
fn main(){
 let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
 let input:Value=serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
 let rows:Vec<Vec<u32>>=serde_json::from_value(input["rows"].clone()).unwrap();
 assert_eq!(rows.len(),8);let width=rows[0].len();assert!(width>0);assert!(rows.iter().all(|r|r.len()==width));
 let columns:Vec<Vec<F>>=(0..width).map(|c|rows.iter().map(|r|{assert!(r[c]<F::CHARACTERISTICS_U32);F::from_u32_unchecked(r[c])}).collect()).collect();
 let refs:Vec<_>=columns.iter().map(|c|c.as_slice()).collect();
 let worker=Worker::new_with_num_threads(2);let tw=fft::Twiddles::<F,std::alloc::Global>::new(8,&worker);
 let pool=default_pool_for::<F,E>();
 let oracle=commit_trace_part::<F,E,Tree,_>(&NaiveBackend,&refs,&tw,4,1,1,3,pool.as_ref(),&worker);
 let cap=oracle.get_cap();let mut openings=vec![];
 for i in 0..16{
  let (coset,values,q)=oracle.query_for_folded_index(i);
  let logical:Vec<Vec<u32>>=values.iter().map(|v|v.iter().map(|x|x.as_u32_reduced()).collect()).collect();
  let raw:Vec<Vec<u32>>=values.iter().map(|v|v.iter().map(|x|x.as_u32_raw_repr_reduced()).collect()).collect();
  openings.push(json!({"query":i,"coset":coset,"tree_index":q.index,"values":logical,"raw_words":raw,"path":q.path}));
 }
 let ColumnMajorBaseOracleForLDE::InMemory(o)=oracle else{panic!("expected materialized")};
 let codewords:Vec<Value>=o.cosets.cosets.iter().map(|c|json!({"offset":c.offset.as_u32_reduced(),"columns":c.original_values_normal_order.iter().map(|v|v.to_vec().iter().map(|x|x.as_u32_reduced()).collect::<Vec<_>>()).collect::<Vec<_>>()})).collect();
 let out=json!({"field_modulus":F::CHARACTERISTICS_U32,"hash":"BLAKE2s-256, 10 rounds","rows":rows,"columns":width,"lde_factor":4,"values_per_leaf":2,"root":cap.cap[0],"domain_root":fft::domain_generator_for_size::<F>(8).as_u32_reduced(),"codewords":codewords,"openings":openings,"cryptographic_scope":"Merkle commitment to RS codeword only; no GKR or WHIR proximity proof"});
 std::fs::write(&args[2],serde_json::to_string_pretty(&out).unwrap()+"\n").unwrap();
 println!("exported 104-column RS commitment and 16 openings");
}
