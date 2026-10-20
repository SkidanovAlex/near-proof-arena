// Experimental SHA-384 configuration. Compiler applicability remains unproved.
use std::io::{self,Read,Write};
use openvm_stark_backend::{StarkProtocolConfig,FiatShamirTranscript,hasher::MerkleHasher,
    codec::{EncodableConfig,DecodableConfig,encode_prime_field32,decode_prime_field32,encode_extension_field32,decode_extension_field32},
    prover::{ReferenceDevice,Coordinator}};
use p3_field::{extension::BinomialExtensionField,PrimeField32};
use sha2::{Sha384,Digest as ShaDigest};
type F=p3_baby_bear::BabyBear;
type EF=BinomialExtensionField<F,12>;
type Digest=[u64;6];
fn digest_bytes(d:Digest)->Vec<u8> {d.into_iter().flat_map(u64::to_le_bytes).collect()}
fn hash_parts(tag:u8,parts:&[&[u8]])->[u8;48] {
    let mut h=Sha384::new();h.update(b"nearproof-native-sha384-ext12-v1");h.update([tag]);
    for part in parts {h.update((part.len() as u64).to_le_bytes());h.update(part);}
    h.finalize().into()
}
fn words(bytes:[u8;48])->Digest {std::array::from_fn(|i|u64::from_le_bytes(bytes[i*8..i*8+8].try_into().unwrap()))}
#[derive(Clone,Debug)]
struct ShaHasher;
impl MerkleHasher for ShaHasher {
    type F=F;type Digest=Digest;
    fn hash_slice(&self,values:&[F])->Digest {
        let bytes:Vec<u8>=values.iter().flat_map(|x|x.as_canonical_u32().to_le_bytes()).collect();
        words(hash_parts(0,&[&bytes]))
    }
    fn compress(&self,left:Digest,right:Digest)->Digest {
        words(hash_parts(1,&[&digest_bytes(left),&digest_bytes(right)]))
    }
}
#[derive(Clone,Debug)]
struct SC {params:SystemParams,hasher:ShaHasher}
impl StarkProtocolConfig for SC {
    type F=F;type EF=EF;type Digest=Digest;type Hasher=ShaHasher;
    fn params(&self)->&SystemParams {&self.params}
    fn hasher(&self)->&ShaHasher {&self.hasher}
}
impl EncodableConfig for SC {
    fn encode_base_field<W:Write>(v:&F,w:&mut W)->io::Result<()> {encode_prime_field32(v,w)}
    fn encode_extension_field<W:Write>(v:&EF,w:&mut W)->io::Result<()> {encode_extension_field32::<F,_,_>(v,w)}
    fn encode_digest<W:Write>(v:&Digest,w:&mut W)->io::Result<()> {w.write_all(&digest_bytes(*v))}
}
impl DecodableConfig for SC {
    fn decode_base_field<R:Read>(r:&mut R)->io::Result<F> {decode_prime_field32(r)}
    fn decode_extension_field<R:Read>(r:&mut R)->io::Result<EF> {decode_extension_field32::<F,_,_>(r)}
    fn decode_digest<R:Read>(r:&mut R)->io::Result<Digest> {let mut b=[0;48];r.read_exact(&mut b)?;Ok(words(b))}
}
#[derive(Clone)]
struct Transcript {state:[u8;48]}
impl Transcript {fn new()->Self {Self {state:hash_parts(2,&[])}}}
impl FiatShamirTranscript<SC> for Transcript {
    fn observe(&mut self,v:F) {self.state=hash_parts(3,&[&self.state,&v.as_canonical_u32().to_le_bytes()]);}
    fn observe_commit(&mut self,d:Digest) {self.state=hash_parts(4,&[&self.state,&digest_bytes(d)]);}
    fn sample(&mut self)->F {
        loop {
            self.state=hash_parts(5,&[&self.state]);
            let n=u32::from_le_bytes(self.state[..4].try_into().unwrap());
            // Exact uniformity for a fresh random 32-bit word, no modulo bias.
            // Rejections advance the state and are never capped/folded into zero.
            if n<4026531842 {return F::from_u32(n%2013265921);}
        }
    }
    fn grind(&mut self,bits:usize)->F {assert_eq!(bits,0,"grinding unsupported in this profile");F::ZERO}
}
struct Engine {device:ReferenceDevice<SC>}
impl StarkEngine for Engine {
    type SC=SC;type PB=CpuColMajorBackend<SC>;type PD=ReferenceDevice<SC>;type TS=Transcript;
    fn new(params:SystemParams)->Self {Self {device:ReferenceDevice::new(SC{params,hasher:ShaHasher})}}
    fn config(&self)->&SC {self.device.config()}
    fn device(&self)->&Self::PD {&self.device}
    fn initial_transcript(&self)->Transcript {Transcript::new()}
    fn prover_from_transcript(&self,t:Transcript)->Coordinator<SC,Self::PB,Self::PD,Transcript> {
        Coordinator::new(CpuColMajorBackend::new(),self.device.clone(),t)
    }
}
fn transcript_vectors() {
    let hasher=ShaHasher;
    let leaf=hasher.hash_slice(&[F::ZERO,F::ONE,F::from_u32(2013265920)]);
    let empty=hasher.hash_slice(&[]);
    let node=hasher.compress(leaf,empty);
    let mut t=Transcript::new();t.observe(F::from_u32(123));t.observe_commit(node);
    let samples:Vec<u32>=(0..64).map(|i| {
        if i%7==0 {t.observe(F::from_u32(i));}
        t.sample().as_canonical_u32()
    }).collect();
    println!("VECTOR_LEAF {:?}",digest_bytes(leaf));
    println!("VECTOR_EMPTY {:?}",digest_bytes(empty));
    println!("VECTOR_NODE {:?}",digest_bytes(node));
    println!("VECTOR_SAMPLES {:?}",samples);
    println!("VECTOR_STATE {:?}",t.state.to_vec());
}
