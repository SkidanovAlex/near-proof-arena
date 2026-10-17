//! Direct Lean AIR -> Airbender quadratic kernel interoperability experiment.
//! No instruction decoder, VM, memory argument, GKR transcript, or WHIR proof.
use std::collections::BTreeMap;
use std::panic::{catch_unwind, AssertUnwindSafe};
use cs::{definitions::GKRAddress, gkr_compiler::CompiledMaxQuadraticGKRRelation};
use field::{baby_bear::{base::BabyBearField as F, ext4::BabyBearExt4 as E}, PrimeField};
use prover::gkr::sumcheck::{access_and_fold::BaseFieldPoly, evaluation_kernels::{
    enforce_max_quadratic_constraint::EnforceSingleMaxQuadraticConstraintGKRKernel as Kernel,
    SingleInputTypeBatchSumcheckEvaluationKernel,
}};
use serde_json::{json, Value};
const P: u64 = 2013265921;
type Poly = BTreeMap<Vec<usize>, u64>;
fn plus(p: &mut Poly, mon: Vec<usize>, value: u64) {
    let x = p.entry(mon).or_default(); *x = (*x + value) % P;
}
fn compile(v: &Value) -> Poly {
    let obj=v.as_object().expect("expression object"); assert_eq!(obj.len(),1);
    if let Some(c)=v.get("const") { return BTreeMap::from([(vec![],c.as_u64().unwrap()%P)]); }
    if let Some(c)=v.get("col") { let i=c.as_u64().unwrap() as usize; assert!(i<104); return BTreeMap::from([(vec![i],1)]); }
    if let Some(a)=v.get("neg") { return compile(a).into_iter().map(|(m,c)|(m,(P-c)%P)).collect(); }
    for op in ["add","mul"] { if let Some(args)=v.get(op) {
        let args=args.as_array().unwrap(); assert_eq!(args.len(),2);
        let a=compile(&args[0]); let b=compile(&args[1]); let mut out=Poly::new();
        if op=="add" { for (m,c) in a.into_iter().chain(b) { plus(&mut out,m,c); } }
        else { for (m,c) in &a { for (n,d) in &b { let mut mn=m.clone(); mn.extend(n); mn.sort();
            assert!(mn.len()<=2,"requires layered lowering"); plus(&mut out,mn,c*d%P); } } }
        out.retain(|_,c|*c!=0); return out;
    }}
    panic!("unsupported expression input");
}
fn ast(v:&Value,row:&[u64])->u64 {
    if let Some(c)=v.get("const") {return c.as_u64().unwrap()%P;}
    if let Some(c)=v.get("col") {return row[c.as_u64().unwrap() as usize];}
    if let Some(a)=v.get("neg") {return (P-ast(a,row))%P;}
    if let Some(a)=v.get("add") {return (ast(&a[0],row)+ast(&a[1],row))%P;}
    if let Some(a)=v.get("mul") {return ast(&a[0],row)*ast(&a[1],row)%P;}
    panic!("unsupported AST");
}
fn f(x:u64)->F { F::from_u32_unchecked(x as u32) }
fn kernel(p:&Poly)->Kernel<F> {
    let mut q=BTreeMap::<usize,Vec<(F,GKRAddress)>>::new(); let mut l=vec![];
    let mut qp=vec![]; let mut lp=vec![]; let mut constant=0;
    for (m,c) in p {match m.as_slice() {
        []=>constant=*c,
        [a]=>{l.push((f(*c),GKRAddress::BaseLayerWitness(*a)));lp.push((*a,f(*c)));},
        [a,b]=>{q.entry(*a).or_default().push((f(*c),GKRAddress::BaseLayerWitness(*b)));qp.push(((*a,*b),f(*c)));},
        _=>panic!("degree"),
    }}
    let relation=CompiledMaxQuadraticGKRRelation{quadratic_terms:q.into_iter().map(|(a,b)|(GKRAddress::BaseLayerWitness(a),b.into_boxed_slice())).collect::<Vec<_>>().into_boxed_slice(),linear_terms:l.into_boxed_slice(),constant:f(constant)};
    Kernel{relation,quadratic_parts:qp,linear_parts:lp,constant_offset:f(constant)}
}
fn check(k:&Kernel<F>, row:&[u64])->bool {
    // Two identical rows are a minimal power-of-two source; checks row zero.
    let polys:Vec<_>=row.iter().map(|v|BaseFieldPoly::new(vec![f(*v);2].into_boxed_slice())).collect();
    let sources:Vec<_>=polys.iter().map(|p|p.accessor()).collect();
    catch_unwind(AssertUnwindSafe(|| {
        <Kernel<F> as SingleInputTypeBatchSumcheckEvaluationKernel<F,E,0>>::evaluate_forward(k,0,&sources)
    })).is_ok()
}
fn main() {
    assert_eq!(F::CHARACTERISTICS_U32 as u64,P);
    let args:Vec<_>=std::env::args().collect(); assert_eq!(args.len(),3,"input export, output report");
    let input:Value=serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
    assert_eq!(input["field_modulus"].as_u64(),Some(P)); assert_eq!(input["columns"].as_u64(),Some(104));
    let expr=input["constraints"].as_array().unwrap(); let polys:Vec<_>=expr.iter().map(compile).collect();
    let kernels:Vec<_>=polys.iter().map(kernel).collect();
    let rows:Vec<Vec<u64>>=serde_json::from_value(input["rows"].clone()).unwrap();
    // Suppress expected panic diagnostics; upstream kernel still prints failing cells.
    std::panic::set_hook(Box::new(|_|{}));
    let mut rejected=0; let mut parity=0;
    for row in &rows {
        assert_eq!(row.len(),104); assert!(row.iter().all(|x|*x<P));
        for k in &kernels {assert!(check(k,row),"honest kernel failure");}
        for col in 0..104 {
            let mut bad=row.clone();bad[col]=(bad[col]+1)%P;
            let mut first_bad=None;
            for (i,(e,p)) in expr.iter().zip(&polys).enumerate() {
                let eval=p.iter().fold(0,|s,(m,c)|(s+m.iter().fold(*c,|a,j|a*bad[*j]%P))%P);
                assert_eq!(eval,ast(e,&bad));parity+=1;
                if eval!=0 && first_bad.is_none(){first_bad=Some(i);}
            }
            assert!(!check(&kernels[first_bad.expect("mutation escaped constraints")],&bad));rejected+=1;
        }
    }
    let report=json!({"status":"PASS","upstream_commit":"129f827003b34acd64a3315a5863eac75bc09fe6",
        "field_modulus":P,"constraints":expr.len(),"columns":104,"honest_rows":rows.len(),
        "kernel_mutations_rejected":rejected,"ast_polynomial_parity_checks":parity,
        "uses_riscv_execution":false,"cryptographic_proof_generated":false,
        "limitations":["Quadratic local constraints only; no stack, memory, gas or control integration.",
        "Rust lowering not yet linked by a formal refinement theorem.","No GKR sumcheck, WHIR commitment, recursion, proof-size or security claim."]});
    std::fs::write(&args[2],serde_json::to_string_pretty(&report).unwrap()+"\n").unwrap();
    println!("{}",report);
}
