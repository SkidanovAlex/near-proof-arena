// The generated static node tables contain only AIR expressions, never witness values.
#[allow(dead_code)]
enum N { C(u32), V(usize,bool), P(usize), First, Last, Trans, Neg(usize), Add(usize,usize), Mul(usize,usize) }
fn eval_nodes<AB: AirBuilderWithPublicValues + InteractionBuilder>(builder:&AB,nodes:&[N])->Vec<AB::Expr> {
    let main=builder.main();
    let local=main.row_slice(0).unwrap();
    let next=main.row_slice(1).unwrap();
    let public=builder.public_values();
    let mut values:Vec<AB::Expr>=Vec::with_capacity(nodes.len());
    for node in nodes {
        let v=match *node {
            N::C(c)=>AB::Expr::from(AB::F::from_u32(c)),
            N::V(i,false)=>local[i].into(), N::V(i,true)=>next[i].into(),
            N::P(i)=>public[i].into(),
            N::First=>builder.is_first_row(), N::Last=>builder.is_last_row(),
            N::Trans=>builder.is_transition_window(2),
            N::Neg(i)=>-values[i].clone(),
            N::Add(i,j)=>values[i].clone()+values[j].clone(),
            N::Mul(i,j)=>values[i].clone()*values[j].clone(),
        };
        values.push(v);
    }
    values
}
