//! Untrusted prover acceleration. No hashing or protocol decisions.
//! C ABI: caller owns valid aligned buffers of declared lengths. Buffers must
//! not overlap. Returns 0 success, 1 pointer, 2 shape, 3 capacity, 4 canonical,
//! 5 overlap. Validation completes before writing output. No allocations.
const P: u64 = 2013265921;
const MAX_DOMAIN: usize = 1 << 22;
fn pow(mut a:u64, mut n:usize)->u64 { let mut r=1; while n>0 {if n&1!=0 {r=r*a%P;} a=a*a%P;n>>=1;} r }
fn add(a:u32,b:u32)->u32 {((a as u64+b as u64)%P) as u32}
fn sub(a:u32,b:u32)->u32 {((a as u64+P-b as u64)%P) as u32}
fn mul(a:u32,b:u32)->u32 {(a as u64*b as u64%P) as u32}
unsafe fn validate(src:*const u32,len:usize,out:*mut u32,cap:usize,needed:usize)->i32 {
    if src.is_null()||out.is_null()||(src as usize)%4!=0||(out as usize)%4!=0 {return 1;}
    if cap<needed {return 3;}
    let Some(a)=(src as usize).checked_add(len*4) else{return 1;};
    let Some(b)=(out as usize).checked_add(needed*4) else{return 1;};
    if (src as usize)<b && (out as usize)<a {return 5;}
    if std::slice::from_raw_parts(src,len).iter().any(|&v|v as u64>=P) {return 4;}
    0
}
/// Forward natural-order FFT; domain/input ratio must be 1 or 4.
#[no_mangle]
pub unsafe extern "C" fn pq384_fft(src:*const u32,len:usize,out:*mut u32,cap:usize,domain:usize)->i32 {
    if domain==0||!domain.is_power_of_two()||domain>MAX_DOMAIN||len==0||len%4!=0 {return 2;}
    let n=len/4;
    if n!=domain && n.checked_mul(4)!=Some(domain) {return 2;}
    let status=validate(src,len,out,cap,domain*4);if status!=0{return status;}
    let a=std::slice::from_raw_parts_mut(out,domain*4);
    a.fill(0);a[..len].copy_from_slice(std::slice::from_raw_parts(src,len));
    let mut j=0;
    for i in 1..domain {let mut bit=domain>>1;while j&bit!=0 {j^=bit;bit>>=1;}j^=bit;if i<j {for k in 0..4 {a.swap(4*i+k,4*j+k);}}}
    let omega=pow(440564289,(1<<27)/domain);
    let mut size=2;
    while size<=domain {let step=pow(omega,domain/size);for start in (0..domain).step_by(size) {let mut w=1;for i in start..start+size/2 {for k in 0..4 {let u=a[4*i+k];let v=mul(a[4*(i+size/2)+k],w as u32);a[4*i+k]=add(u,v);a[4*(i+size/2)+k]=sub(u,v);}w=w*step%P;}}size*=2;}
    0
}
fn ext_add(a:[u32;4],b:[u32;4])->[u32;4] {std::array::from_fn(|i|add(a[i],b[i]))}
fn ext_sub(a:[u32;4],b:[u32;4])->[u32;4] {std::array::from_fn(|i|sub(a[i],b[i]))}
fn ext_mul(a:[u32;4],b:[u32;4])->[u32;4] {
    let mut c=[0u32;4];
    for i in 0..4 {for j in 0..4 {let mut v=mul(a[i],b[j]);if i+j>=4 {v=mul(v,11);}c[(i+j)%4]=add(c[(i+j)%4],v);}}
    c
}
fn ext_at(a:&[u32],i:usize)->[u32;4] {a[4*i..4*i+4].try_into().unwrap()}
/// Affine folds of adjacent Ext4 entries; r is passed by value (canonical).
#[no_mangle]
pub unsafe extern "C" fn pq384_affine_fold(src:*const u32,len:usize,out:*mut u32,cap:usize,r0:u32,r1:u32,r2:u32,r3:u32)->i32 {
    if len==0||len%8!=0||len>4*MAX_DOMAIN {return 2;}
    let r=[r0,r1,r2,r3];if r.iter().any(|&v|v as u64>=P){return 4;}
    let status=validate(src,len,out,cap,len/2);if status!=0{return status;}
    let a=std::slice::from_raw_parts(src,len);let b=std::slice::from_raw_parts_mut(out,len/2);
    for i in 0..len/8 {let x=ext_at(a,2*i);let y=ext_at(a,2*i+1);b[4*i..4*i+4].copy_from_slice(&ext_add(x,ext_mul(r,ext_sub(y,x))));}
    0
}
/// Three coefficients of dot(affine_pairs(values,t),affine_pairs(weights,t)).
#[no_mangle]
pub unsafe extern "C" fn pq384_quadratic_dot(src:*const u32,weights:*const u32,len:usize,out:*mut u32,cap:usize)->i32 {
    if len==0||len%8!=0||len>4*MAX_DOMAIN {return 2;}
    let s=validate(src,len,out,cap,12);if s!=0{return s;}
    let s=validate(weights,len,out,cap,12);if s!=0{return s;}
    let a=std::slice::from_raw_parts(src,len);let w=std::slice::from_raw_parts(weights,len);
    let mut c=[[0u32;4];3];
    for i in 0..len/8 {let x=ext_at(a,2*i);let dx=ext_sub(ext_at(a,2*i+1),x);let y=ext_at(w,2*i);let dy=ext_sub(ext_at(w,2*i+1),y);
        c[0]=ext_add(c[0],ext_mul(x,y));
        c[1]=ext_add(c[1],ext_add(ext_mul(dx,y),ext_mul(x,dy)));
        c[2]=ext_add(c[2],ext_mul(dx,dy));
    }
    let dst=std::slice::from_raw_parts_mut(out,12);for i in 0..3 {dst[4*i..4*i+4].copy_from_slice(&c[i]);}0
}
