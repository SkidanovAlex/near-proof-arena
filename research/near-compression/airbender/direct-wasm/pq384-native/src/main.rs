//! Primitive cross-check only. No PCS or quantum-security claim.
use near_pq384_primitives::{P,H,h,words};
use serde_json::{Value,json};
fn decode_hex(s:&str)->Vec<u8>{assert_eq!(s.len()%2,0);(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn draw(state:&mut H,label:&[u8],count:usize,coeff:usize,max_blocks:usize)->Result<(Vec<Vec<u32>>,usize,usize),String>{
 if count==0||count>4096||coeff==0||coeff>64||max_blocks==0||max_blocks>1<<20{return Err("draw shape".into())}
 let n=(count as u64).to_le_bytes();let d=(coeff as u64).to_le_bytes();
 let mut seed=h(b"transcript/request",&[state,label,&n,&d]);let mut values=vec![];let mut rejected=0;
 for counter in 0..max_blocks{
  let block=h(b"transcript/squeeze",&[&seed,label,&(counter as u64).to_le_bytes()]);
  seed=h(b"transcript/ratchet",&[&seed,label,&block]);
  for word in words(&block){
   if (word as u64)>=((1u64<<32)/P)*P{rejected+=1;continue}
   values.push((word as u64%P)as u32);
   if values.len()==count*coeff{
    *state=h(b"transcript/draw-result",&[&seed,label,&n,&d,&((counter+1)as u64).to_le_bytes()]);
    return Ok((values.chunks_exact(coeff).map(|x|x.to_vec()).collect(),counter+1,rejected))
   }
  }
 }
 Err("rejection sampler exhausted block budget".into())
}
fn main(){
 let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
 let input:Value=serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
 let statement=decode_hex(input["statement_hex"].as_str().unwrap());
 let mut seed=h(b"transcript/init",&[&statement]);let mut events=vec![];
 for event in input["events"].as_array().unwrap(){
  let label=event["label"].as_str().unwrap().as_bytes();
  if event["kind"]=="commit"{
   let payload=decode_hex(event["payload_hex"].as_str().unwrap());seed=h(b"transcript/commit",&[&seed,label,&payload]);
   events.push(json!({"seed":words(&seed)}));
  }else{
   assert_eq!(event["kind"],"draw");
   let before=seed;
   let result=draw(&mut seed,label,event["count"].as_u64().unwrap()as usize,event["coefficients"].as_u64().unwrap()as usize,event["max_blocks"].as_u64().unwrap()as usize);
   match result{
    Ok((values,blocks,rejected))=>events.push(json!({"values":values,"blocks":blocks,"rejected_words":rejected,"seed":words(&seed)})),
    Err(e)=>{assert_eq!(seed,before);events.push(json!({"error":e,"seed":words(&seed)}));}
   }
  }
 }
 let context=decode_hex(input["context_hex"].as_str().unwrap());
 let leaves:Vec<Vec<u32>>=serde_json::from_value(input["leaves"].clone()).unwrap();
 assert!(leaves.len()>=2&&leaves.len().is_power_of_two());
 let mut layers:Vec<Vec<H>>=vec![leaves.iter().enumerate().map(|(i,leaf)|{
  assert!(leaf.iter().all(|&v|(v as u64)<P));let bytes:Vec<u8>=leaf.iter().flat_map(|v|v.to_le_bytes()).collect();
  h(b"merkle/leaf",&[&context,&(i as u64).to_le_bytes(),&bytes])
 }).collect()];
 while layers.last().unwrap().len()>1{
  let level=(layers.len()as u64).to_le_bytes();let next=layers.last().unwrap().chunks_exact(2).map(|pair|h(b"merkle/node",&[&context,&level,&pair[0],&pair[1]])).collect();layers.push(next);
 }
 let root=h(b"merkle/root",&[&context,&(leaves.len()as u64).to_le_bytes(),&layers.last().unwrap()[0]]);
 let paths:Vec<_>=(0..leaves.len()).map(|mut i|layers[..layers.len()-1].iter().map(|layer|{let v=words(&layer[i^1]);i/=2;v}).collect::<Vec<_>>()).collect();
 std::fs::write(&args[2],serde_json::to_vec_pretty(&json!({"events":events,"root":words(&root),"paths":paths})).unwrap()).unwrap();
}
