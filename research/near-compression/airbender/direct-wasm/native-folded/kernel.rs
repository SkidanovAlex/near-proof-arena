//! Prover-only Ext4 folded sumcheck kernel. Python owns the transcript and PCS.
use std::slice;
const P: u64 = 2013265921;
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(C)]
struct E([u32; 4]);
const ZERO:E=E([0,0,0,0]); const ONE:E=E([1,0,0,0]);
impl E {
 fn base(x:u32)->Self {E([x,0,0,0])}
 fn add(self,b:Self)->Self {let mut c=[0;4];for i in 0..4 {let v=self.0[i] as u64+b.0[i] as u64;c[i]=(if v>=P {v-P}else{v})as u32;} E(c)}
 fn sub(self,b:Self)->Self {let mut c=[0;4];for i in 0..4 {let v=self.0[i] as u64+P-b.0[i] as u64;c[i]=(if v>=P {v-P}else{v})as u32;} E(c)}
 fn mul(self,b:Self)->Self {
  if self==ZERO || b==ZERO{return ZERO} if self==ONE{return b} if b==ONE{return self}
  if self.0[1..]==[0,0,0] {let mut c=[0;4];for i in 0..4{c[i]=((self.0[0]as u64*b.0[i]as u64)%P)as u32;}return E(c)}
  if b.0[1..]==[0,0,0] {return b.mul(self)}
  let mut c=[0u128;7];for i in 0..4 {for j in 0..4 {c[i+j]+=self.0[i]as u128*b.0[j]as u128;}}
  E([((c[0]+11*c[4])%P as u128)as u32,((c[1]+11*c[5])%P as u128)as u32,
     ((c[2]+11*c[6])%P as u128)as u32,(c[3]%P as u128)as u32])
 }
 fn affine(a:Self,b:Self,r:Self)->Self {a.add(r.mul(b.sub(a)))}
}
fn eq(a:E,b:E)->E {a.mul(b).add(ONE.sub(a).mul(ONE.sub(b)))}
struct State {width:usize,rows:usize,current:Vec<E>,next:Vec<E>}
#[repr(C)]
struct Ins {op:u32,a:u32,b:u32,c:[u32;4]}
fn valid_program(p:&[Ins],width:usize)->bool {
 !p.is_empty() && p.iter().enumerate().all(|(i,x)|match x.op {
 0=>x.c.iter().all(|&c|u64::from(c)<P),1|2=>(x.a as usize)<width,3|4|5=>true,
 6|7|8=>(x.a as usize)<i&&(x.b as usize)<i,_=>false})
}
#[no_mangle]
pub unsafe extern "C" fn np_new(values:*const u32,rows:usize,width:usize)->*mut std::ffi::c_void {
 if values.is_null()||rows<2||!rows.is_power_of_two()||width==0{return std::ptr::null_mut()}
 let Some(size)=rows.checked_mul(width) else{return std::ptr::null_mut()};
 if size>1_000_000_000{return std::ptr::null_mut()}
 let src=slice::from_raw_parts(values,size);
 if src.iter().any(|&x|u64::from(x)>=P){return std::ptr::null_mut()}
 let current:Vec<E>=src.iter().map(|&v|E::base(v)).collect();
 let next:Vec<E>=(0..size).map(|i|current[(i+width)%size]).collect();
 Box::into_raw(Box::new(State{width,rows,current,next})).cast()
}
#[no_mangle]
pub unsafe extern "C" fn np_free(state:*mut std::ffi::c_void){if !state.is_null(){drop(Box::from_raw(state.cast::<State>()))}}
#[no_mangle]
pub unsafe extern "C" fn np_fold(state:*mut std::ffi::c_void,r:*const u32)->i32 {
 if state.is_null()||r.is_null(){return -1}let s=&mut *state.cast::<State>();if s.rows<2{return -2}
 let r=E(*(r.cast::<[u32;4]>()));if r.0.iter().any(|&x|u64::from(x)>=P){return -3}
 let count=s.rows/2*s.width;
 for dest in 0..count {let i=dest/s.width;let c=dest%s.width;let a=2*i*s.width+c;let b=a+s.width;
  s.current[dest]=E::affine(s.current[a],s.current[b],r);s.next[dest]=E::affine(s.next[a],s.next[b],r);}
 s.rows/=2;s.current.truncate(count);s.next.truncate(count);0
}
#[no_mangle]
pub unsafe extern "C" fn np_round(state:*mut std::ffi::c_void,program:*const u32,instructions:usize,
 tau:*const u32,dimension:usize,prefix:*const u32,prefix_len:usize,nodes:usize,out:*mut u32)->i32 {
 if state.is_null()||program.is_null()||tau.is_null()||out.is_null()||prefix_len>=dimension||nodes==0||nodes>1000{return -1}
 if prefix_len>0&&prefix.is_null(){return -2}
 let s=&*state.cast::<State>();if dimension-prefix_len>=usize::BITS as usize||s.rows!=(1usize<<(dimension-prefix_len)){return -3}
 let p=slice::from_raw_parts(program.cast::<Ins>(),instructions);if !valid_program(p,s.width){return -4}
 let ts=slice::from_raw_parts(tau.cast::<E>(),dimension);
 let ps=if prefix_len==0 {&[][..]}else{slice::from_raw_parts(prefix.cast::<E>(),prefix_len)};
 if ts.iter().chain(ps.iter()).any(|e|e.0.iter().any(|&x|u64::from(x)>=P)){return -5}
 let mut first=ONE;let mut last=ONE;let mut weight=ONE;
 for i in 0..prefix_len {first=first.mul(ONE.sub(ps[i]));last=last.mul(ps[i]);weight=weight.mul(eq(ts[i],ps[i]));}
 let mut suffix=vec![ONE];
 for &t in &ts[prefix_len+1..] {let old=suffix.len();suffix.resize(old*2,ZERO);for i in 0..old{let v=suffix[i];suffix[i]=v.mul(ONE.sub(t));suffix[old+i]=v.mul(t);}}
 let mut regs=vec![ZERO;p.len()];let mut cur=vec![ZERO;s.width];let mut nxt=vec![ZERO;s.width];
 for node in 0..nodes {
  let r=E::base(node as u32);let f=first.mul(ONE.sub(r));let l=last.mul(r);let mut total=ZERO;
  for pair in 0..s.rows/2 {
   for c in 0..s.width {let a=2*pair*s.width+c;let b=a+s.width;cur[c]=E::affine(s.current[a],s.current[b],r);nxt[c]=E::affine(s.next[a],s.next[b],r);}
   let f=if pair==0{f}else{ZERO};let l=if pair+1==s.rows/2{l}else{ZERO};
   for (j,ins) in p.iter().enumerate(){regs[j]=match ins.op {
    0=>E(ins.c),1=>cur[ins.a as usize],2=>nxt[ins.a as usize],3=>f,4=>l,5=>ONE.sub(l),
    6=>regs[ins.a as usize].add(regs[ins.b as usize]),7=>regs[ins.a as usize].sub(regs[ins.b as usize]),
    8=>regs[ins.a as usize].mul(regs[ins.b as usize]),_=>unreachable!()};}
   total=total.add(suffix[pair].mul(regs[p.len()-1]));
  }
  let value=weight.mul(eq(ts[prefix_len],r)).mul(total);
  std::ptr::copy_nonoverlapping(value.0.as_ptr(),out.add(4*node),4);
 }0
}
