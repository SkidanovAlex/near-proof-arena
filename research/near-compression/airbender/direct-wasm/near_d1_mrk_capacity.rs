//! Focused malformed/capacity cases for isolated complete-block Merkle renderer.
use npudr::v3::{d1,mrksort::{self,MrkV,MrkNode}};
use serde_json::json;
use std::{error::Error,fs,path::PathBuf};
fn main()->Result<(),Box<dyn Error>> {
 let args:Vec<_>=std::env::args().collect();
 if args.len()!=3{return Err("usage: near-d1-mrk-capacity CASE_DIR REPORT_JSON".into())}
 let case=PathBuf::from(&args[1]);
 let ci=d1::case_inputs_d1(&fs::read(case.join("claim.bin"))?,&fs::read(case.join("witness.bin"))?)?;
 let v:MrkV=serde_json::from_str(&ci.entries["mrk"])?;
 let required=mrksort::mrk_required_rows(&v)?;
 let low=(required-1).ilog2() as usize;
 let mut checks=Vec::new();
 for log in [0,20,low] {
  let e=mrksort::mrk_at_log(&v,log).expect_err("invalid height accepted");
  checks.push(json!({"kind":"height","log":log,"error":e}));
 }
 let mut missing=v.clone();missing.nodes.pop();
 checks.push(json!({"kind":"missing_node","error":mrksort::mrk_at_log(&missing,19).expect_err("missing node accepted")}));
 let mut extra=v.clone();extra.nodes.push(v.nodes[0].clone());
 checks.push(json!({"kind":"extra_node","error":mrksort::mrk_at_log(&extra,19).expect_err("extra node accepted")}));
 if let Some(k)=v.nodes.iter().position(|n|matches!(n,MrkNode::Hashed{..})) {
  let mut wrong=v.clone();wrong.nodes[k]=MrkNode::Promoted{c_id:0,c_len:0};
  checks.push(json!({"kind":"wrong_node_kind","error":mrksort::mrk_at_log(&wrong,19).expect_err("wrong node kind accepted")}));
 }
 let empty=mrksort::mrk_at_log(&MrkV::default(),1)?;
 assert_eq!((empty.log,empty.width,empty.cells.len()),(1,60,120));
 assert!(empty.cells.iter().enumerate().all(|(i,&x)|x==if i%60==58 {1}else{0}));
 fs::write(&args[2],serde_json::to_vec_pretty(&json!({"status":"PASS","case":case,"required_rows":required,"rejections":checks,"empty_log1":"PASS","scope":"Capacity and complete-block shape guards before trace allocation; no proof claim"}))?)?;
 println!("PASS Merkle capacity/shape guards and empty log1");Ok(())
}
