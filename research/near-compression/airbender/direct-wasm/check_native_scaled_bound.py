"""Compile the actual patched native implication method in an exhaustive small test."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/native-literal-recursion'
source=Path('/home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5/crates/stark-backend/src/keygen/types.rs').read_text()
a=source.index('impl LinearConstraint {');b=source.index('\n#[derive(Error',a)
method=source[a:b]
program='struct LinearConstraint {coefficients:Vec<u32>,threshold:u32}\n'+method+r'''
fn main() {
 let mut checked=0u64;
 for a in 0..4 { for b in 0..4 { for c in 0..4 { for d in 0..4 {
 for t in 0..7 { for u in 0..7 {
  let x=LinearConstraint{coefficients:vec![a,b],threshold:t};
  let y=LinearConstraint{coefficients:vec![c,d],threshold:u};
  if x.is_implied_by(&y) {
   for h in 0..6 {for k in 0..6 {
    if c*h+d*k<u {assert!(a*h+b*k<t);}
    checked+=1;
   }}
  }
 }}}}}}
 let x=LinearConstraint{coefficients:vec![1,511],threshold:2013265921};
 assert!(x.is_implied_by(&LinearConstraint{coefficients:vec![198,2],threshold:1<<20}));
 assert!(!x.is_implied_by(&LinearConstraint{coefficients:vec![198,2],threshold:1<<30}));
 assert!(!x.is_implied_by(&LinearConstraint{coefficients:vec![198],threshold:1<<20}));
 let large=LinearConstraint{coefficients:vec![u32::MAX],threshold:u32::MAX};
 assert!(large.is_implied_by(&large));
 assert!(!large.is_implied_by(&LinearConstraint{coefficients:vec![1],threshold:u32::MAX}));
 println!("{}",checked);
}
'''
with tempfile.TemporaryDirectory() as tmp:
 p=Path(tmp);(p/'check.rs').write_text(program)
 subprocess.run(['rustc','--edition=2021','-O',str(p/'check.rs'),'-o',str(p/'check')],check=True)
 count=int(subprocess.check_output([str(p/'check')],text=True))
(OUT/'scaled-bound-check.rs').write_text(program)
(OUT/'scaled-bound-check.json').write_text(json.dumps(dict(assignments=count,source_sha256=hashlib.sha256(source.encode()).hexdigest(),scope='Actual native method; finite checks plus conditional Lean scaling theorem, not a Rust refinement proof.'),indent=2)+'\n')
print(count)
