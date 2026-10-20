use sha2::{Digest, Sha384};
pub const P:u64=2013265921;
pub type H=[u8;48];
pub fn h(tag:&[u8],parts:&[&[u8]])->H {
 let mut s=Sha384::new();s.update(b"NEAR-PQ384-PRIMITIVES-V1");
 s.update((tag.len() as u32).to_le_bytes());s.update(tag);s.update((parts.len() as u32).to_le_bytes());
 for p in parts{s.update((p.len() as u64).to_le_bytes());s.update(p);}
 s.finalize().into()
}
pub fn words(h:&H)->Vec<u32>{h.chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect()}
