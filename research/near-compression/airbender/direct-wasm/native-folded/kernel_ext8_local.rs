// Ext8 local-sumcheck state, adapted from kernel_v2's row/selector layout.
include!("kernel_ext8.rs");
#[allow(unsafe_op_in_unsafe_fn)]
mod local {
use std::slice;
use super::P;
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(C)]
struct LocalElement([u32;8]);
const ZERO:LocalElement=LocalElement([0;8]);
const ONE:LocalElement=LocalElement([1,0,0,0,0,0,0,0]);
impl LocalElement {
 fn base(x:u32)->Self {let mut v=[0;8];v[0]=x;Self(v)}
 fn add(self,b:Self)->Self {Self(super::add(self.0,b.0))}
 fn sub(self,b:Self)->Self {Self(super::sub(self.0,b.0))}
 fn mul(self,b:Self)->Self {Self(super::mul(self.0,b.0))}
 fn affine(a:Self,b:Self,r:Self)->Self {a.add(r.mul(b.sub(a)))}
}
fn eq(a:LocalElement,b:LocalElement)->LocalElement {a.mul(b).add(ONE.sub(a).mul(ONE.sub(b)))}
struct State {width:usize,rows:usize,current:Vec<LocalElement>,next:Vec<LocalElement>}
#[repr(C)]
struct Ins {op:u32,a:u32,b:u32,c:[u32;8]}
fn valid_program(p:&[Ins],width:usize)->bool {
 !p.is_empty() && p.iter().enumerate().all(|(i,x)|match x.op {
 0=>x.c.iter().all(|&c|u64::from(c)<P),1|2=>(x.a as usize)<width,3|4|5=>true,
 6|7|8=>(x.a as usize)<i&&(x.b as usize)<i,_=>false})
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn np8_new(values:*const u32,rows:usize,width:usize)->*mut std::ffi::c_void {
 if values.is_null()||rows<2||!rows.is_power_of_two()||width==0{return std::ptr::null_mut()}
 let Some(size)=rows.checked_mul(width) else{return std::ptr::null_mut()};
 if size>1_000_000_000{return std::ptr::null_mut()}
 let src=slice::from_raw_parts(values,size);
 if src.iter().any(|&x|u64::from(x)>=P){return std::ptr::null_mut()}
 let current:Vec<LocalElement>=src.iter().map(|&v|LocalElement::base(v)).collect();
 let next:Vec<LocalElement>=(0..size).map(|i|current[(i+width)%size]).collect();
 Box::into_raw(Box::new(State{width,rows,current,next})).cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn np8_free(state:*mut std::ffi::c_void){if !state.is_null(){drop(Box::from_raw(state.cast::<State>()))}}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn np8_fold(state:*mut std::ffi::c_void,r:*const u32)->i32 {
 if state.is_null()||r.is_null(){return -1}let s=&mut *state.cast::<State>();if s.rows<2{return -2}
 let r=LocalElement(*(r.cast::<[u32;8]>()));if r.0.iter().any(|&x|u64::from(x)>=P){return -3}
 let count=s.rows/2*s.width;
 for dest in 0..count {let i=dest/s.width;let c=dest%s.width;let a=2*i*s.width+c;let b=a+s.width;
  s.current[dest]=LocalElement::affine(s.current[a],s.current[b],r);s.next[dest]=LocalElement::affine(s.next[a],s.next[b],r);}
 s.rows/=2;s.current.truncate(count);s.next.truncate(count);0
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn np8_round(state:*mut std::ffi::c_void,program:*const u32,instructions:usize,
 tau:*const u32,dimension:usize,prefix:*const u32,prefix_len:usize,nodes:usize,out:*mut u32)->i32 {
 if state.is_null()||program.is_null()||tau.is_null()||out.is_null()||prefix_len>=dimension||nodes==0||nodes>1000{return -1}
 if prefix_len>0&&prefix.is_null(){return -2}
 let s=&*state.cast::<State>();if dimension-prefix_len>=usize::BITS as usize||s.rows!=(1usize<<(dimension-prefix_len)){return -3}
 let p=slice::from_raw_parts(program.cast::<Ins>(),instructions);if !valid_program(p,s.width){return -4}
 let ts=slice::from_raw_parts(tau.cast::<LocalElement>(),dimension);
 let ps=if prefix_len==0 {&[][..]}else{slice::from_raw_parts(prefix.cast::<LocalElement>(),prefix_len)};
 if ts.iter().chain(ps.iter()).any(|e|e.0.iter().any(|&x|u64::from(x)>=P)){return -5}
 let mut first=ONE;let mut last=ONE;let mut weight=ONE;
 for i in 0..prefix_len {first=first.mul(ONE.sub(ps[i]));last=last.mul(ps[i]);weight=weight.mul(eq(ts[i],ps[i]));}
 let mut suffix=vec![ONE];
 for &t in &ts[prefix_len+1..] {let old=suffix.len();suffix.resize(old*2,ZERO);for i in 0..old{let v=suffix[i];suffix[i]=v.mul(ONE.sub(t));suffix[old+i]=v.mul(t);}}
 let mut regs=vec![ZERO;p.len()];let mut cur=vec![ZERO;s.width];let mut nxt=vec![ZERO;s.width];
 for node in 0..nodes {
  let r=LocalElement::base(node as u32);let f=first.mul(ONE.sub(r));let l=last.mul(r);let mut total=ZERO;
  for pair in 0..s.rows/2 {
   for c in 0..s.width {let a=2*pair*s.width+c;let b=a+s.width;cur[c]=LocalElement::affine(s.current[a],s.current[b],r);nxt[c]=LocalElement::affine(s.next[a],s.next[b],r);}
   let f=if pair==0{f}else{ZERO};let l=if pair+1==s.rows/2{l}else{ZERO};
   for (j,ins) in p.iter().enumerate(){regs[j]=match ins.op {
    0=>LocalElement(ins.c),1=>cur[ins.a as usize],2=>nxt[ins.a as usize],3=>f,4=>l,5=>ONE.sub(l),
    6=>regs[ins.a as usize].add(regs[ins.b as usize]),7=>regs[ins.a as usize].sub(regs[ins.b as usize]),
    8=>regs[ins.a as usize].mul(regs[ins.b as usize]),_=>unreachable!()};}
   total=total.add(suffix[pair].mul(regs[p.len()-1]));
  }
  let value=weight.mul(eq(ts[prefix_len],r)).mul(total);
  std::ptr::copy_nonoverlapping(value.0.as_ptr(),out.add(8*node),8);
 }0
}

// Terminal vectors from the already completed constraint sumcheck folds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn np8_terminal(state:*mut std::ffi::c_void,out:*mut u32)->i32 {
 if state.is_null()||out.is_null(){return -1}let s=&*state.cast::<State>();if s.rows!=1{return -2}
 for (i,v) in s.current.iter().chain(s.next.iter()).enumerate(){std::ptr::copy_nonoverlapping(v.0.as_ptr(),out.add(8*i),8);}0
}

}
