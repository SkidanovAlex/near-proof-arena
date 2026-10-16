//! Focused checks against the isolated research height API; no proof generation.
use npudr::v3::{d1,sched};
use serde_json::json;
use std::{error::Error,fs,path::PathBuf};
fn main()->Result<(),Box<dyn Error>> {
 let args:Vec<_>=std::env::args().collect();
 if args.len()!=3{return Err("usage: near-d1-height-capacity CASE_DIR REPORT_JSON".into())}
 let case=PathBuf::from(&args[1]);
 let ci=d1::case_inputs_d1(&fs::read(case.join("claim.bin"))?,&fs::read(case.join("witness.bin"))?)?;
 let input=&ci.entries["codec"];
 let mut cases=Vec::new();
 for (name,log,expected) in [("codec",7,"requires 454 rows"),("proc",4,"requires 18 rows"),("codec",0,"within1..22"),("proc",23,"within1..22")] {
  let error=sched::render_at_log(name,input,log).expect_err("invalid capacity must be rejected");
  assert!(error.contains(expected),"unexpected diagnostic: {error}");
  cases.push(json!({"name":name,"log":log,"result":"Err","diagnostic":error}));
 }
 // Empty proc has no active prefix: row0 is the mandatory tail and row1 padding.
 let tab=sched::proc_aligned_at_log(&[],1);
 assert_eq!(tab.log,1);assert_eq!(tab.width,64);assert_eq!(tab.height(),2);
 assert_eq!(&tab.cells[..64],&tab.cells[64..]);
 let ikc=tab.cells[23] as u64;let p=2013265921u64;
 assert_eq!(ikc*(p-15)%p,1,"canonical ikcPad is inverse of -15");
 assert!(tab.cells[..64].iter().enumerate().all(|(c,&x)|c==23 || x==0));
 cases.push(json!({"name":"empty_proc","log":1,"result":"PASS","active_rows":0,"tail_rows":1,"padding_rows":1,"ikc_pad":ikc}));
 let out=json!({"status":"PASS","checks":cases,"case":case,
  "scope":"Four API rejection checks and exact empty-proc tail/padding rows. Source validates capacity before Tab::zero; no allocator instrumentation or proof claim."});
 fs::write(&args[2],serde_json::to_vec_pretty(&out)?)?;
 println!("PASS: 4 capacity/log errors and empty proc tail+padding");Ok(())
}
