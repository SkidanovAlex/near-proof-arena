//! Ext8 multilinear folding primitives. Flat basis: X^8 = 11 over BabyBear.
//! ABI buffers contain canonical u32 coefficients, eight per field element.
const P: u64 = 2_013_265_921;
type E = [u32; 8];
fn add(a: E, b: E) -> E { std::array::from_fn(|i| ((a[i] as u64+b[i] as u64)%P) as u32) }
fn sub(a: E, b: E) -> E { std::array::from_fn(|i| ((a[i] as u64+P-b[i] as u64)%P) as u32) }
fn mul(a: E, b: E) -> E {
    let mut v=[0u128;8];
    for i in 0..8 { for j in 0..8 {
        v[(i+j)%8] += a[i] as u128*b[j] as u128*if i+j>=8 {11} else {1};
    }}
    std::array::from_fn(|i| (v[i]%P as u128) as u32)
}
fn elem(v: &[u32], i: usize) -> E { v[8*i..8*i+8].try_into().unwrap() }
fn valid(v: &[u32]) -> bool { v.iter().all(|&x| (x as u64)<P) }

/// Caller must supply valid disjoint buffers; returns 1 for bad shape/scalars.
/// n counts field elements, not words. Output has n/2 elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn near_ext8_fold(input: *const u32, n: usize, challenge: *const u32, output: *mut u32) -> i32 {
    if n%2!=0 || n>isize::MAX as usize/32 || input.is_null() || challenge.is_null() || output.is_null() { return 1; }
    let v=unsafe {std::slice::from_raw_parts(input,n*8)};
    let r=unsafe {std::slice::from_raw_parts(challenge,8)};
    if !valid(v) || !valid(r) { return 1; }
    let out=unsafe {std::slice::from_raw_parts_mut(output,n*4)};
    for i in 0..n/2 { let a=elem(v,2*i);let b=elem(v,2*i+1);
        out[8*i..8*i+8].copy_from_slice(&add(a,mul(r.try_into().unwrap(),sub(b,a))));
    }
    0
}

/// Sum the product of two multilinear tables along their first variable.
/// Output is three Ext8 coefficients, low degree first.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn near_ext8_quadratic(input: *const u32, weights: *const u32, n: usize, output: *mut u32) -> i32 {
    if n%2!=0 || n>isize::MAX as usize/32 || input.is_null() || weights.is_null() || output.is_null() { return 1; }
    let v=unsafe {std::slice::from_raw_parts(input,n*8)};
    let w=unsafe {std::slice::from_raw_parts(weights,n*8)};
    if !valid(v) || !valid(w) {return 1;}
    let mut q=[[0;8];3];
    for i in 0..n/2 {
        let a=elem(v,2*i);let b=elem(v,2*i+1);let u=elem(w,2*i);let z=elem(w,2*i+1);
        let d=sub(b,a);let e=sub(z,u);
        q[0]=add(q[0],mul(a,u));q[1]=add(q[1],add(mul(d,u),mul(a,e)));q[2]=add(q[2],mul(d,e));
    }
    let out=unsafe {std::slice::from_raw_parts_mut(output,24)};
    for i in 0..3 {out[8*i..8*i+8].copy_from_slice(&q[i]);}
    0
}

/// One GKR round. Gates are (opcode,left,right), opcodes add/sub/mul=0/1/2.
/// `weights` includes equality factors from earlier rounds. `fixed_left` is
/// the completed left evaluation on axis1 (ignored on axis0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn near_ext8_gkr_round(
    gates: *const u32, count: usize, weights: *const u32,
    original: *const u32, n: usize, folded: *const u32, nf: usize,
    axis: u32, bit: u32, fixed_left: *const u32, output: *mut u32) -> i32 {
    let limit=isize::MAX as usize/32;
    if count>limit || n>limit || nf>limit || nf<2 || nf%2!=0 || axis>1 || bit>=usize::BITS ||
        gates.is_null() || weights.is_null() || original.is_null() || folded.is_null() || fixed_left.is_null() || output.is_null() {return 1;}
    let g=unsafe {std::slice::from_raw_parts(gates,count*3)};
    let w=unsafe {std::slice::from_raw_parts(weights,count*8)};
    let v=unsafe {std::slice::from_raw_parts(original,n*8)};
    let f=unsafe {std::slice::from_raw_parts(folded,nf*8)};
    let a=unsafe {std::slice::from_raw_parts(fixed_left,8)};
    if !valid(w) || !valid(v) || !valid(f) || !valid(a) {return 1;}
    // Validate every gate before writing output.
    for gate in g.chunks_exact(3) {
        if gate[0]>2 || gate[1] as usize>=n || gate[2] as usize>=n {return 1;}
        let index=(gate[1+axis as usize] as usize)>>bit;
        if index|1>=nf {return 1;}
    }
    let mut q=[[0;8];3];let zero=[0;8];
    for (k,gate) in g.chunks_exact(3).enumerate() {
        let index=(gate[1+axis as usize] as usize)>>bit;
        let b=elem(f,index&!1);let d=sub(elem(f,index|1),b);
        let other=if axis==0 {elem(v,gate[2] as usize)} else {a.try_into().unwrap()};
        let (c0,c1)=match gate[0] {
            0=>(add(b,other),d),
            1=>if axis==0 {(sub(b,other),d)} else {(sub(other,b),sub(zero,d))},
            _=>(mul(b,other),mul(d,other)),
        };
        let coeff=if index&1==0 {[c0,sub(c1,c0),sub(zero,c1)]} else {[zero,c0,c1]};
        for j in 0..3 {q[j]=add(q[j],mul(elem(w,k),coeff[j]));}
    }
    let out=unsafe {std::slice::from_raw_parts_mut(output,24)};
    for j in 0..3 {out[8*j..8*j+8].copy_from_slice(&q[j]);}
    0
}
