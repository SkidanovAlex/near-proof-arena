//! Versioned natural-order RS commitment experiment, not a PCS proof.
use near_pq384_primitives::{P,H,h,words};
use serde_json::{Value,json};
use std::io::Write;
fn mul(a:u64,b:u64)->u64{a*b%P}
fn pow(mut a:u64,mut n:u64)->u64{let mut r=1;while n>0{if n&1==1{r=mul(r,a)}a=mul(a,a);n>>=1;}r}
fn fft(a:&mut [u64],omega:u64){
 let n=a.len();let mut j=0;
 for i in 1..n{let mut bit=n>>1;while j&bit!=0{j^=bit;bit>>=1;}j^=bit;if i<j{a.swap(i,j)}}
 let mut len=2;while len<=n{let step=pow(omega,(n/len)as u64);
  for block in a.chunks_exact_mut(len){let mut w=1;for i in 0..len/2{let u=block[i];let v=mul(block[i+len/2],w);block[i]=(u+v)%P;block[i+len/2]=(u+P-v)%P;w=mul(w,step);}}
  len*=2;
 }
}
fn main(){
 let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
 let input:Value=serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
 let rows:Vec<Vec<u32>>=serde_json::from_value(input["rows"].clone()).unwrap();
 let n=rows.len();assert!(n>=2&&n.is_power_of_two()&&n<=1<<25);
 let width=rows[0].len();assert!(width>0&&rows.iter().all(|r|r.len()==width&&r.iter().all(|&x|(x as u64)<P)));
 let packed=input.get("packing").is_some();
 let packing=if packed{input["packing"].as_u64().unwrap()as usize}else{1};
 assert!(packing>0&&packing.is_power_of_two()&&packing<=1<<20);
 let dimension=n.checked_mul(packing).unwrap();assert!(dimension<=1<<25);
 let lanes=width.div_ceil(packing);
 let size=dimension*4;let omega=pow(440564289,(1<<27)/size as u64);
 assert_eq!(pow(omega,size as u64),1);assert_eq!(pow(omega,(size/2)as u64),P-1);
 // Context binds field, dimensions, natural domain, bit/axis/leaf order and zero padding.
 let mut context=b"NEAR-PQ384-RS-V1/row-lowbit-mobius/columns-separate/zero-pad4/natural-domain/column-major-pairs/le-u32".to_vec();
 if packed{
  context=b"NEAR-PQ384-RS-PACKED-V2/row-low-column-high-mobius/consecutive-column-groups/zero-pad-columns-and-lde4/natural-domain/lane-major-pairs/le-u32".to_vec();
  for v in [P,n as u64,width as u64,packing as u64,lanes as u64,size as u64,omega]{context.extend_from_slice(&v.to_le_bytes());}
 }else{
  for v in [P,n as u64,width as u64,size as u64,omega]{context.extend_from_slice(&v.to_le_bytes());}
 }
 // Optional prover cache: immutable per-run directory, never overwrite.
 let cache=input.get("cache_directory").map(|v|std::path::PathBuf::from(v.as_str().unwrap()));
 if let Some(path)=&cache{std::fs::create_dir(path).unwrap();}
 let mut coefficient_file=cache.as_ref().map(|path|std::io::BufWriter::new(std::fs::File::create(path.join("coefficients.u32")).unwrap()));
 let half=size/2;let mut leaves=vec![Vec::<u8>::with_capacity(lanes*8);half];
 for lane in 0..lanes{
  let mut a=vec![0u64;size];
  for col in 0..packing{let source_col=lane*packing+col;if source_col<width{for i in 0..n{a[i+n*col]=rows[i][source_col]as u64;}}}
  let mut bit=1;while bit<dimension{for i in 0..dimension{if i&bit!=0{a[i]=(a[i]+P-a[i^bit])%P;}}bit*=2;}
  if let Some(file)=coefficient_file.as_mut(){for &value in &a[..dimension]{file.write_all(&(value as u32).to_le_bytes()).unwrap();}}
  fft(&mut a,omega);
  for i in 0..half{leaves[i].extend_from_slice(&(a[i]as u32).to_le_bytes());leaves[i].extend_from_slice(&(a[i+half]as u32).to_le_bytes());}
 }
 let mut layers:Vec<Vec<H>>=vec![leaves.iter().enumerate().map(|(i,l)|h(b"merkle/leaf",&[&context,&(i as u64).to_le_bytes(),l])).collect()];
 while layers.last().unwrap().len()>1{let level=(layers.len()as u64).to_le_bytes();let next=layers.last().unwrap().chunks_exact(2).map(|p|h(b"merkle/node",&[&context,&level,&p[0],&p[1]])).collect();layers.push(next);}
 let root=h(b"merkle/root",&[&context,&(half as u64).to_le_bytes(),&layers.last().unwrap()[0]]);
 if let Some(path)=&cache{
  coefficient_file.as_mut().unwrap().flush().unwrap();
  let mut file=std::io::BufWriter::new(std::fs::File::create(path.join("leaves.u32")).unwrap());
  for leaf in &leaves{file.write_all(leaf).unwrap();}file.flush().unwrap();
  let mut file=std::io::BufWriter::new(std::fs::File::create(path.join("tree.sha384")).unwrap());
  for layer in &layers{for digest in layer{file.write_all(digest).unwrap();}}file.flush().unwrap();
  let manifest=json!({"format":"near-pq384-source-cache-v1","rows":n,"width":width,"packing":packing,"lanes":lanes,"degree":dimension,"leaf_count":half,"root_hex":root.iter().map(|b|format!("{b:02x}")).collect::<String>(),"context_hex":context.iter().map(|b|format!("{b:02x}")).collect::<String>()});
  std::fs::write(path.join("manifest.json"),serde_json::to_vec(&manifest).unwrap()).unwrap();
 }
 let indices:Vec<usize>=serde_json::from_value(input["indices"].clone()).unwrap();
 let openings:Vec<_>=indices.iter().map(|&index|{assert!(index<half);let mut i=index;let path:Vec<_>=layers[..layers.len()-1].iter().map(|l|{let v=words(&l[i^1]);i/=2;v}).collect();let leaf:Vec<_>=leaves[index].chunks_exact(4).map(|v|u32::from_le_bytes(v.try_into().unwrap())).collect();json!({"index":index,"leaf":leaf,"path":path})}).collect();
 let result=json!({"profile":if packed{"near-pq384-rs-packed-v2"}else{"near-pq384-rs-v1"},"packing":packing,"lanes":lanes,"rows":n,"width":width,"domain_size":size,"omega":omega,"context_hex":context.iter().map(|b|format!("{b:02x}")).collect::<String>(),"root":words(&root),"openings":openings});
 std::fs::write(&args[2],serde_json::to_vec(&result).unwrap()).unwrap();
}
